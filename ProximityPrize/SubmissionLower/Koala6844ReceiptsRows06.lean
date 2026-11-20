import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_8_68_flag : Flag := ⟨8, 68, 3266⟩
private def endpoint_8_68_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_8_68_base : receiptBase endpoint_8_68_flag endpoint_8_68_sources = some 241930293348608809 := by decide +kernel
private theorem endpoint_8_68_w0 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 2 241930293348608809 = some 241930293348608809 := by decide +kernel
private theorem endpoint_8_68_w2 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 2 2 241930293348608809 = some 241930293348608809 := by decide +kernel
private theorem endpoint_8_68_p4 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 4 241930293348608809 = some 241930293348608809 :=
  join_receipt_window endpoint_8_68_flag endpoint_8_68_sources 0 2 2 241930293348608809 241930293348608809 241930293348608809 endpoint_8_68_w0 endpoint_8_68_w2
private theorem endpoint_8_68_w4 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 4 2 241930293348608809 = some 241930293348608809 := by decide +kernel
private theorem endpoint_8_68_p6 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 6 241930293348608809 = some 241930293348608809 :=
  join_receipt_window endpoint_8_68_flag endpoint_8_68_sources 0 4 2 241930293348608809 241930293348608809 241930293348608809 endpoint_8_68_p4 endpoint_8_68_w4
private theorem endpoint_8_68_w6 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 6 1 241930293348608809 = some 241930293348608809 := by decide +kernel
private theorem endpoint_8_68_p7 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 7 241930293348608809 = some 241930293348608809 :=
  join_receipt_window endpoint_8_68_flag endpoint_8_68_sources 0 6 1 241930293348608809 241930293348608809 241930293348608809 endpoint_8_68_p6 endpoint_8_68_w6
def endpoint_8_68 : CertifiedEndpoint :=
  ⟨⟨8, 68, 3266⟩, 241930293348608809, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_8_68_flag endpoint_8_68_sources 7 241930293348608809 241930293348608809 rfl endpoint_8_68_base endpoint_8_68_p7) (by decide)⟩
private def endpoint_8_69_flag : Flag := ⟨8, 69, 3199⟩
private def endpoint_8_69_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_8_69_base : receiptBase endpoint_8_69_flag endpoint_8_69_sources = some 240111903594921635 := by decide +kernel
private theorem endpoint_8_69_w0 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 2 240111903594921635 = some 240111903594921635 := by decide +kernel
private theorem endpoint_8_69_w2 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 2 2 240111903594921635 = some 240111903594921635 := by decide +kernel
private theorem endpoint_8_69_p4 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 4 240111903594921635 = some 240111903594921635 :=
  join_receipt_window endpoint_8_69_flag endpoint_8_69_sources 0 2 2 240111903594921635 240111903594921635 240111903594921635 endpoint_8_69_w0 endpoint_8_69_w2
private theorem endpoint_8_69_w4 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 4 2 240111903594921635 = some 240111903594921635 := by decide +kernel
private theorem endpoint_8_69_p6 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 6 240111903594921635 = some 240111903594921635 :=
  join_receipt_window endpoint_8_69_flag endpoint_8_69_sources 0 4 2 240111903594921635 240111903594921635 240111903594921635 endpoint_8_69_p4 endpoint_8_69_w4
private theorem endpoint_8_69_w6 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 6 1 240111903594921635 = some 240111903594921635 := by decide +kernel
private theorem endpoint_8_69_p7 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 7 240111903594921635 = some 240111903594921635 :=
  join_receipt_window endpoint_8_69_flag endpoint_8_69_sources 0 6 1 240111903594921635 240111903594921635 240111903594921635 endpoint_8_69_p6 endpoint_8_69_w6
def endpoint_8_69 : CertifiedEndpoint :=
  ⟨⟨8, 69, 3199⟩, 240111903594921635, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_8_69_flag endpoint_8_69_sources 7 240111903594921635 240111903594921635 rfl endpoint_8_69_base endpoint_8_69_p7) (by decide)⟩
private def endpoint_8_70_flag : Flag := ⟨8, 70, 3128⟩
private def endpoint_8_70_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_8_70_base : receiptBase endpoint_8_70_flag endpoint_8_70_sources = some 239486566781478116 := by decide +kernel
private theorem endpoint_8_70_w0 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 2 239486566781478116 = some 239486566781478116 := by decide +kernel
private theorem endpoint_8_70_w2 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 2 2 239486566781478116 = some 239486566781478116 := by decide +kernel
private theorem endpoint_8_70_p4 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 4 239486566781478116 = some 239486566781478116 :=
  join_receipt_window endpoint_8_70_flag endpoint_8_70_sources 0 2 2 239486566781478116 239486566781478116 239486566781478116 endpoint_8_70_w0 endpoint_8_70_w2
private theorem endpoint_8_70_w4 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 4 2 239486566781478116 = some 239486566781478116 := by decide +kernel
private theorem endpoint_8_70_p6 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 6 239486566781478116 = some 239486566781478116 :=
  join_receipt_window endpoint_8_70_flag endpoint_8_70_sources 0 4 2 239486566781478116 239486566781478116 239486566781478116 endpoint_8_70_p4 endpoint_8_70_w4
private theorem endpoint_8_70_w6 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 6 1 239486566781478116 = some 239486566781478116 := by decide +kernel
private theorem endpoint_8_70_p7 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 7 239486566781478116 = some 239486566781478116 :=
  join_receipt_window endpoint_8_70_flag endpoint_8_70_sources 0 6 1 239486566781478116 239486566781478116 239486566781478116 endpoint_8_70_p6 endpoint_8_70_w6
def endpoint_8_70 : CertifiedEndpoint :=
  ⟨⟨8, 70, 3128⟩, 239486566781478116, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_8_70_flag endpoint_8_70_sources 7 239486566781478116 239486566781478116 rfl endpoint_8_70_base endpoint_8_70_p7) (by decide)⟩
private def endpoint_8_71_flag : Flag := ⟨8, 71, 3054⟩
private def endpoint_8_71_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_8_71_base : receiptBase endpoint_8_71_flag endpoint_8_71_sources = some 238496020129348128 := by decide +kernel
private theorem endpoint_8_71_w0 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 2 238496020129348128 = some 238496020129348128 := by decide +kernel
private theorem endpoint_8_71_w2 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 2 2 238496020129348128 = some 238496020129348128 := by decide +kernel
private theorem endpoint_8_71_p4 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 4 238496020129348128 = some 238496020129348128 :=
  join_receipt_window endpoint_8_71_flag endpoint_8_71_sources 0 2 2 238496020129348128 238496020129348128 238496020129348128 endpoint_8_71_w0 endpoint_8_71_w2
private theorem endpoint_8_71_w4 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 4 2 238496020129348128 = some 238496020129348128 := by decide +kernel
private theorem endpoint_8_71_p6 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 6 238496020129348128 = some 238496020129348128 :=
  join_receipt_window endpoint_8_71_flag endpoint_8_71_sources 0 4 2 238496020129348128 238496020129348128 238496020129348128 endpoint_8_71_p4 endpoint_8_71_w4
private theorem endpoint_8_71_w6 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 6 1 238496020129348128 = some 238496020129348128 := by decide +kernel
private theorem endpoint_8_71_p7 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 7 238496020129348128 = some 238496020129348128 :=
  join_receipt_window endpoint_8_71_flag endpoint_8_71_sources 0 6 1 238496020129348128 238496020129348128 238496020129348128 endpoint_8_71_p6 endpoint_8_71_w6
def endpoint_8_71 : CertifiedEndpoint :=
  ⟨⟨8, 71, 3054⟩, 238496020129348128, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_8_71_flag endpoint_8_71_sources 7 238496020129348128 238496020129348128 rfl endpoint_8_71_base endpoint_8_71_p7) (by decide)⟩
private def endpoint_8_72_flag : Flag := ⟨8, 72, 2977⟩
private def endpoint_8_72_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_8_72_base : receiptBase endpoint_8_72_flag endpoint_8_72_sources = some 236986678320275392 := by decide +kernel
private theorem endpoint_8_72_w0 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 2 236986678320275392 = some 236986678320275392 := by decide +kernel
private theorem endpoint_8_72_w2 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 2 2 236986678320275392 = some 236986678320275392 := by decide +kernel
private theorem endpoint_8_72_p4 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 4 236986678320275392 = some 236986678320275392 :=
  join_receipt_window endpoint_8_72_flag endpoint_8_72_sources 0 2 2 236986678320275392 236986678320275392 236986678320275392 endpoint_8_72_w0 endpoint_8_72_w2
private theorem endpoint_8_72_w4 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 4 2 236986678320275392 = some 236986678320275392 := by decide +kernel
private theorem endpoint_8_72_p6 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 6 236986678320275392 = some 236986678320275392 :=
  join_receipt_window endpoint_8_72_flag endpoint_8_72_sources 0 4 2 236986678320275392 236986678320275392 236986678320275392 endpoint_8_72_p4 endpoint_8_72_w4
private theorem endpoint_8_72_w6 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 6 1 236986678320275392 = some 236986678320275392 := by decide +kernel
private theorem endpoint_8_72_p7 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 7 236986678320275392 = some 236986678320275392 :=
  join_receipt_window endpoint_8_72_flag endpoint_8_72_sources 0 6 1 236986678320275392 236986678320275392 236986678320275392 endpoint_8_72_p6 endpoint_8_72_w6
def endpoint_8_72 : CertifiedEndpoint :=
  ⟨⟨8, 72, 2977⟩, 236986678320275392, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_8_72_flag endpoint_8_72_sources 7 236986678320275392 236986678320275392 rfl endpoint_8_72_base endpoint_8_72_p7) (by decide)⟩
private def endpoint_8_73_flag : Flag := ⟨8, 73, 2897⟩
private def endpoint_8_73_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_8_73_base : receiptBase endpoint_8_73_flag endpoint_8_73_sources = some 233541098494375095 := by decide +kernel
private theorem endpoint_8_73_w0 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 2 233541098494375095 = some 233541098494375095 := by decide +kernel
private theorem endpoint_8_73_w2 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 2 2 233541098494375095 = some 233541098494375095 := by decide +kernel
private theorem endpoint_8_73_p4 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 4 233541098494375095 = some 233541098494375095 :=
  join_receipt_window endpoint_8_73_flag endpoint_8_73_sources 0 2 2 233541098494375095 233541098494375095 233541098494375095 endpoint_8_73_w0 endpoint_8_73_w2
private theorem endpoint_8_73_w4 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 4 2 233541098494375095 = some 233541098494375095 := by decide +kernel
private theorem endpoint_8_73_p6 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 6 233541098494375095 = some 233541098494375095 :=
  join_receipt_window endpoint_8_73_flag endpoint_8_73_sources 0 4 2 233541098494375095 233541098494375095 233541098494375095 endpoint_8_73_p4 endpoint_8_73_w4
private theorem endpoint_8_73_w6 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 6 1 233541098494375095 = some 233541098494375095 := by decide +kernel
private theorem endpoint_8_73_p7 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 7 233541098494375095 = some 233541098494375095 :=
  join_receipt_window endpoint_8_73_flag endpoint_8_73_sources 0 6 1 233541098494375095 233541098494375095 233541098494375095 endpoint_8_73_p6 endpoint_8_73_w6
def endpoint_8_73 : CertifiedEndpoint :=
  ⟨⟨8, 73, 2897⟩, 233541098494375095, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_8_73_flag endpoint_8_73_sources 7 233541098494375095 233541098494375095 rfl endpoint_8_73_base endpoint_8_73_p7) (by decide)⟩
private def endpoint_8_74_flag : Flag := ⟨8, 74, 2814⟩
private def endpoint_8_74_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_8_74_base : receiptBase endpoint_8_74_flag endpoint_8_74_sources = some 229692132517633903 := by decide +kernel
private theorem endpoint_8_74_w0 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 2 229692132517633903 = some 229692132517633903 := by decide +kernel
private theorem endpoint_8_74_w2 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 2 2 229692132517633903 = some 229692132517633903 := by decide +kernel
private theorem endpoint_8_74_p4 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 4 229692132517633903 = some 229692132517633903 :=
  join_receipt_window endpoint_8_74_flag endpoint_8_74_sources 0 2 2 229692132517633903 229692132517633903 229692132517633903 endpoint_8_74_w0 endpoint_8_74_w2
private theorem endpoint_8_74_w4 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 4 2 229692132517633903 = some 229692132517633903 := by decide +kernel
private theorem endpoint_8_74_p6 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 6 229692132517633903 = some 229692132517633903 :=
  join_receipt_window endpoint_8_74_flag endpoint_8_74_sources 0 4 2 229692132517633903 229692132517633903 229692132517633903 endpoint_8_74_p4 endpoint_8_74_w4
private theorem endpoint_8_74_w6 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 6 1 229692132517633903 = some 229692132517633903 := by decide +kernel
private theorem endpoint_8_74_p7 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 7 229692132517633903 = some 229692132517633903 :=
  join_receipt_window endpoint_8_74_flag endpoint_8_74_sources 0 6 1 229692132517633903 229692132517633903 229692132517633903 endpoint_8_74_p6 endpoint_8_74_w6
def endpoint_8_74 : CertifiedEndpoint :=
  ⟨⟨8, 74, 2814⟩, 229692132517633903, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_8_74_flag endpoint_8_74_sources 7 229692132517633903 229692132517633903 rfl endpoint_8_74_base endpoint_8_74_p7) (by decide)⟩
private def endpoint_8_75_flag : Flag := ⟨8, 75, 2728⟩
private def endpoint_8_75_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_8_75_base : receiptBase endpoint_8_75_flag endpoint_8_75_sources = some 229756728554518012 := by decide +kernel
private theorem endpoint_8_75_w0 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 2 229756728554518012 = some 229756728554518012 := by decide +kernel
private theorem endpoint_8_75_w2 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 2 2 229756728554518012 = some 229756728554518012 := by decide +kernel
private theorem endpoint_8_75_p4 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 4 229756728554518012 = some 229756728554518012 :=
  join_receipt_window endpoint_8_75_flag endpoint_8_75_sources 0 2 2 229756728554518012 229756728554518012 229756728554518012 endpoint_8_75_w0 endpoint_8_75_w2
private theorem endpoint_8_75_w4 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 4 2 229756728554518012 = some 229756728554518012 := by decide +kernel
private theorem endpoint_8_75_p6 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 6 229756728554518012 = some 229756728554518012 :=
  join_receipt_window endpoint_8_75_flag endpoint_8_75_sources 0 4 2 229756728554518012 229756728554518012 229756728554518012 endpoint_8_75_p4 endpoint_8_75_w4
private theorem endpoint_8_75_w6 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 6 1 229756728554518012 = some 229756728554518012 := by decide +kernel
private theorem endpoint_8_75_p7 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 7 229756728554518012 = some 229756728554518012 :=
  join_receipt_window endpoint_8_75_flag endpoint_8_75_sources 0 6 1 229756728554518012 229756728554518012 229756728554518012 endpoint_8_75_p6 endpoint_8_75_w6
def endpoint_8_75 : CertifiedEndpoint :=
  ⟨⟨8, 75, 2728⟩, 229756728554518012, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_8_75_flag endpoint_8_75_sources 7 229756728554518012 229756728554518012 rfl endpoint_8_75_base endpoint_8_75_p7) (by decide)⟩
private def endpoint_8_76_flag : Flag := ⟨8, 76, 2638⟩
private def endpoint_8_76_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_8_76_base : receiptBase endpoint_8_76_flag endpoint_8_76_sources = some 224947814032402164 := by decide +kernel
private theorem endpoint_8_76_w0 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 2 224947814032402164 = some 224947814032402164 := by decide +kernel
private theorem endpoint_8_76_w2 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 2 2 224947814032402164 = some 224947814032402164 := by decide +kernel
private theorem endpoint_8_76_p4 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 4 224947814032402164 = some 224947814032402164 :=
  join_receipt_window endpoint_8_76_flag endpoint_8_76_sources 0 2 2 224947814032402164 224947814032402164 224947814032402164 endpoint_8_76_w0 endpoint_8_76_w2
private theorem endpoint_8_76_w4 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 4 2 224947814032402164 = some 224947814032402164 := by decide +kernel
private theorem endpoint_8_76_p6 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 6 224947814032402164 = some 224947814032402164 :=
  join_receipt_window endpoint_8_76_flag endpoint_8_76_sources 0 4 2 224947814032402164 224947814032402164 224947814032402164 endpoint_8_76_p4 endpoint_8_76_w4
private theorem endpoint_8_76_w6 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 6 1 224947814032402164 = some 224947814032402164 := by decide +kernel
private theorem endpoint_8_76_p7 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 7 224947814032402164 = some 224947814032402164 :=
  join_receipt_window endpoint_8_76_flag endpoint_8_76_sources 0 6 1 224947814032402164 224947814032402164 224947814032402164 endpoint_8_76_p6 endpoint_8_76_w6
def endpoint_8_76 : CertifiedEndpoint :=
  ⟨⟨8, 76, 2638⟩, 224947814032402164, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_8_76_flag endpoint_8_76_sources 7 224947814032402164 224947814032402164 rfl endpoint_8_76_base endpoint_8_76_p7) (by decide)⟩
private def endpoint_8_77_flag : Flag := ⟨8, 77, 2546⟩
private def endpoint_8_77_sources : Sources := ⟨contact11, contact11, contact13⟩
private theorem endpoint_8_77_base : receiptBase endpoint_8_77_flag endpoint_8_77_sources = some 219898172366360018 := by decide +kernel
private theorem endpoint_8_77_w0 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 2 219898172366360018 = some 219898172366360018 := by decide +kernel
private theorem endpoint_8_77_w2 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 2 2 219898172366360018 = some 219898172366360018 := by decide +kernel
private theorem endpoint_8_77_p4 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 4 219898172366360018 = some 219898172366360018 :=
  join_receipt_window endpoint_8_77_flag endpoint_8_77_sources 0 2 2 219898172366360018 219898172366360018 219898172366360018 endpoint_8_77_w0 endpoint_8_77_w2
private theorem endpoint_8_77_w4 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 4 2 219898172366360018 = some 219898172366360018 := by decide +kernel
private theorem endpoint_8_77_p6 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 6 219898172366360018 = some 219898172366360018 :=
  join_receipt_window endpoint_8_77_flag endpoint_8_77_sources 0 4 2 219898172366360018 219898172366360018 219898172366360018 endpoint_8_77_p4 endpoint_8_77_w4
private theorem endpoint_8_77_w6 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 6 1 219898172366360018 = some 219898172366360018 := by decide +kernel
private theorem endpoint_8_77_p7 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 7 219898172366360018 = some 219898172366360018 :=
  join_receipt_window endpoint_8_77_flag endpoint_8_77_sources 0 6 1 219898172366360018 219898172366360018 219898172366360018 endpoint_8_77_p6 endpoint_8_77_w6
def endpoint_8_77 : CertifiedEndpoint :=
  ⟨⟨8, 77, 2546⟩, 219898172366360018, .terminal ⟨contact11, contact11, contact13⟩ (finish_receipt_window endpoint_8_77_flag endpoint_8_77_sources 7 219898172366360018 219898172366360018 rfl endpoint_8_77_base endpoint_8_77_p7) (by decide)⟩
private def endpoint_8_78_flag : Flag := ⟨8, 78, 2450⟩
private def endpoint_8_78_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_8_78_base : receiptBase endpoint_8_78_flag endpoint_8_78_sources = some 216328552729304828 := by decide +kernel
private theorem endpoint_8_78_w0 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 2 216328552729304828 = some 216328552729304828 := by decide +kernel
private theorem endpoint_8_78_w2 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 2 2 216328552729304828 = some 216328552729304828 := by decide +kernel
private theorem endpoint_8_78_p4 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 4 216328552729304828 = some 216328552729304828 :=
  join_receipt_window endpoint_8_78_flag endpoint_8_78_sources 0 2 2 216328552729304828 216328552729304828 216328552729304828 endpoint_8_78_w0 endpoint_8_78_w2
private theorem endpoint_8_78_w4 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 4 2 216328552729304828 = some 216328552729304828 := by decide +kernel
private theorem endpoint_8_78_p6 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 6 216328552729304828 = some 216328552729304828 :=
  join_receipt_window endpoint_8_78_flag endpoint_8_78_sources 0 4 2 216328552729304828 216328552729304828 216328552729304828 endpoint_8_78_p4 endpoint_8_78_w4
private theorem endpoint_8_78_w6 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 6 1 216328552729304828 = some 216328552729304828 := by decide +kernel
private theorem endpoint_8_78_p7 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 7 216328552729304828 = some 216328552729304828 :=
  join_receipt_window endpoint_8_78_flag endpoint_8_78_sources 0 6 1 216328552729304828 216328552729304828 216328552729304828 endpoint_8_78_p6 endpoint_8_78_w6
def endpoint_8_78 : CertifiedEndpoint :=
  ⟨⟨8, 78, 2450⟩, 216328552729304828, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_8_78_flag endpoint_8_78_sources 7 216328552729304828 216328552729304828 rfl endpoint_8_78_base endpoint_8_78_p7) (by decide)⟩
private def endpoint_8_79_flag : Flag := ⟨8, 79, 2352⟩
private def endpoint_8_79_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_8_79_base : receiptBase endpoint_8_79_flag endpoint_8_79_sources = some 210136171185409623 := by decide +kernel
private theorem endpoint_8_79_w0 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 2 210136171185409623 = some 210136171185409623 := by decide +kernel
private theorem endpoint_8_79_w2 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 2 2 210136171185409623 = some 210136171185409623 := by decide +kernel
private theorem endpoint_8_79_p4 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 4 210136171185409623 = some 210136171185409623 :=
  join_receipt_window endpoint_8_79_flag endpoint_8_79_sources 0 2 2 210136171185409623 210136171185409623 210136171185409623 endpoint_8_79_w0 endpoint_8_79_w2
private theorem endpoint_8_79_w4 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 4 2 210136171185409623 = some 210136171185409623 := by decide +kernel
private theorem endpoint_8_79_p6 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 6 210136171185409623 = some 210136171185409623 :=
  join_receipt_window endpoint_8_79_flag endpoint_8_79_sources 0 4 2 210136171185409623 210136171185409623 210136171185409623 endpoint_8_79_p4 endpoint_8_79_w4
private theorem endpoint_8_79_w6 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 6 1 210136171185409623 = some 210136171185409623 := by decide +kernel
private theorem endpoint_8_79_p7 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 7 210136171185409623 = some 210136171185409623 :=
  join_receipt_window endpoint_8_79_flag endpoint_8_79_sources 0 6 1 210136171185409623 210136171185409623 210136171185409623 endpoint_8_79_p6 endpoint_8_79_w6
def endpoint_8_79 : CertifiedEndpoint :=
  ⟨⟨8, 79, 2352⟩, 210136171185409623, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_8_79_flag endpoint_8_79_sources 7 210136171185409623 210136171185409623 rfl endpoint_8_79_base endpoint_8_79_p7) (by decide)⟩
private def endpoint_8_80_flag : Flag := ⟨8, 80, 2250⟩
private def endpoint_8_80_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_8_80_base : receiptBase endpoint_8_80_flag endpoint_8_80_sources = some 203386195355593255 := by decide +kernel
private theorem endpoint_8_80_w0 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 2 203386195355593255 = some 203386195355593255 := by decide +kernel
private theorem endpoint_8_80_w2 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 2 2 203386195355593255 = some 203386195355593255 := by decide +kernel
private theorem endpoint_8_80_p4 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 4 203386195355593255 = some 203386195355593255 :=
  join_receipt_window endpoint_8_80_flag endpoint_8_80_sources 0 2 2 203386195355593255 203386195355593255 203386195355593255 endpoint_8_80_w0 endpoint_8_80_w2
private theorem endpoint_8_80_w4 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 4 2 203386195355593255 = some 203386195355593255 := by decide +kernel
private theorem endpoint_8_80_p6 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 6 203386195355593255 = some 203386195355593255 :=
  join_receipt_window endpoint_8_80_flag endpoint_8_80_sources 0 4 2 203386195355593255 203386195355593255 203386195355593255 endpoint_8_80_p4 endpoint_8_80_w4
private theorem endpoint_8_80_w6 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 6 1 203386195355593255 = some 203386195355593255 := by decide +kernel
private theorem endpoint_8_80_p7 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 7 203386195355593255 = some 203386195355593255 :=
  join_receipt_window endpoint_8_80_flag endpoint_8_80_sources 0 6 1 203386195355593255 203386195355593255 203386195355593255 endpoint_8_80_p6 endpoint_8_80_w6
def endpoint_8_80 : CertifiedEndpoint :=
  ⟨⟨8, 80, 2250⟩, 203386195355593255, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_8_80_flag endpoint_8_80_sources 7 203386195355593255 203386195355593255 rfl endpoint_8_80_base endpoint_8_80_p7) (by decide)⟩
private def endpoint_8_81_flag : Flag := ⟨8, 81, 2145⟩
private def endpoint_8_81_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_8_81_base : receiptBase endpoint_8_81_flag endpoint_8_81_sources = some 198327543148707145 := by decide +kernel
private theorem endpoint_8_81_w0 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 2 198327543148707145 = some 198327543148707145 := by decide +kernel
private theorem endpoint_8_81_w2 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 2 2 198327543148707145 = some 198327543148707145 := by decide +kernel
private theorem endpoint_8_81_p4 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 4 198327543148707145 = some 198327543148707145 :=
  join_receipt_window endpoint_8_81_flag endpoint_8_81_sources 0 2 2 198327543148707145 198327543148707145 198327543148707145 endpoint_8_81_w0 endpoint_8_81_w2
private theorem endpoint_8_81_w4 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 4 2 198327543148707145 = some 198327543148707145 := by decide +kernel
private theorem endpoint_8_81_p6 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 6 198327543148707145 = some 198327543148707145 :=
  join_receipt_window endpoint_8_81_flag endpoint_8_81_sources 0 4 2 198327543148707145 198327543148707145 198327543148707145 endpoint_8_81_p4 endpoint_8_81_w4
private theorem endpoint_8_81_w6 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 6 1 198327543148707145 = some 198327543148707145 := by decide +kernel
private theorem endpoint_8_81_p7 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 7 198327543148707145 = some 198327543148707145 :=
  join_receipt_window endpoint_8_81_flag endpoint_8_81_sources 0 6 1 198327543148707145 198327543148707145 198327543148707145 endpoint_8_81_p6 endpoint_8_81_w6
def endpoint_8_81 : CertifiedEndpoint :=
  ⟨⟨8, 81, 2145⟩, 198327543148707145, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_8_81_flag endpoint_8_81_sources 7 198327543148707145 198327543148707145 rfl endpoint_8_81_base endpoint_8_81_p7) (by decide)⟩
private def endpoint_8_82_flag : Flag := ⟨8, 82, 2037⟩
private def endpoint_8_82_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_8_82_base : receiptBase endpoint_8_82_flag endpoint_8_82_sources = some 192648768430072793 := by decide +kernel
private theorem endpoint_8_82_w0 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 2 192648768430072793 = some 192648768430072793 := by decide +kernel
private theorem endpoint_8_82_w2 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 2 2 192648768430072793 = some 192648768430072793 := by decide +kernel
private theorem endpoint_8_82_p4 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 4 192648768430072793 = some 192648768430072793 :=
  join_receipt_window endpoint_8_82_flag endpoint_8_82_sources 0 2 2 192648768430072793 192648768430072793 192648768430072793 endpoint_8_82_w0 endpoint_8_82_w2
private theorem endpoint_8_82_w4 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 4 2 192648768430072793 = some 192648768430072793 := by decide +kernel
private theorem endpoint_8_82_p6 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 6 192648768430072793 = some 192648768430072793 :=
  join_receipt_window endpoint_8_82_flag endpoint_8_82_sources 0 4 2 192648768430072793 192648768430072793 192648768430072793 endpoint_8_82_p4 endpoint_8_82_w4
private theorem endpoint_8_82_w6 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 6 1 192648768430072793 = some 192648768430072793 := by decide +kernel
private theorem endpoint_8_82_p7 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 7 192648768430072793 = some 192648768430072793 :=
  join_receipt_window endpoint_8_82_flag endpoint_8_82_sources 0 6 1 192648768430072793 192648768430072793 192648768430072793 endpoint_8_82_p6 endpoint_8_82_w6
def endpoint_8_82 : CertifiedEndpoint :=
  ⟨⟨8, 82, 2037⟩, 192648768430072793, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_8_82_flag endpoint_8_82_sources 7 192648768430072793 192648768430072793 rfl endpoint_8_82_base endpoint_8_82_p7) (by decide)⟩
private def endpoint_8_83_flag : Flag := ⟨8, 83, 1925⟩
private def endpoint_8_83_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_8_83_base : receiptBase endpoint_8_83_flag endpoint_8_83_sources = some 184107330451701963 := by decide +kernel
private theorem endpoint_8_83_w0 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 0 2 184107330451701963 = some 184107330451701963 := by decide +kernel
private theorem endpoint_8_83_w2 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 2 2 184107330451701963 = some 184107330451701963 := by decide +kernel
private theorem endpoint_8_83_p4 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 0 4 184107330451701963 = some 184107330451701963 :=
  join_receipt_window endpoint_8_83_flag endpoint_8_83_sources 0 2 2 184107330451701963 184107330451701963 184107330451701963 endpoint_8_83_w0 endpoint_8_83_w2
private theorem endpoint_8_83_w4 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 4 2 184107330451701963 = some 184107330451701963 := by decide +kernel
private theorem endpoint_8_83_p6 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 0 6 184107330451701963 = some 184107330451701963 :=
  join_receipt_window endpoint_8_83_flag endpoint_8_83_sources 0 4 2 184107330451701963 184107330451701963 184107330451701963 endpoint_8_83_p4 endpoint_8_83_w4
private theorem endpoint_8_83_w6 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 6 1 184107330451701963 = some 184107330451701963 := by decide +kernel
private theorem endpoint_8_83_p7 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 0 7 184107330451701963 = some 184107330451701963 :=
  join_receipt_window endpoint_8_83_flag endpoint_8_83_sources 0 6 1 184107330451701963 184107330451701963 184107330451701963 endpoint_8_83_p6 endpoint_8_83_w6
def endpoint_8_83 : CertifiedEndpoint :=
  ⟨⟨8, 83, 1925⟩, 184107330451701963, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_8_83_flag endpoint_8_83_sources 7 184107330451701963 184107330451701963 rfl endpoint_8_83_base endpoint_8_83_p7) (by decide)⟩
private def endpoint_8_84_flag : Flag := ⟨8, 84, 1811⟩
private def endpoint_8_84_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_8_84_base : receiptBase endpoint_8_84_flag endpoint_8_84_sources = some 175138518068786270 := by decide +kernel
private theorem endpoint_8_84_w0 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 0 2 175138518068786270 = some 175138518068786270 := by decide +kernel
private theorem endpoint_8_84_w2 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 2 2 175138518068786270 = some 175138518068786270 := by decide +kernel
private theorem endpoint_8_84_p4 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 0 4 175138518068786270 = some 175138518068786270 :=
  join_receipt_window endpoint_8_84_flag endpoint_8_84_sources 0 2 2 175138518068786270 175138518068786270 175138518068786270 endpoint_8_84_w0 endpoint_8_84_w2
private theorem endpoint_8_84_w4 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 4 2 175138518068786270 = some 175138518068786270 := by decide +kernel
private theorem endpoint_8_84_p6 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 0 6 175138518068786270 = some 175138518068786270 :=
  join_receipt_window endpoint_8_84_flag endpoint_8_84_sources 0 4 2 175138518068786270 175138518068786270 175138518068786270 endpoint_8_84_p4 endpoint_8_84_w4
private theorem endpoint_8_84_w6 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 6 1 175138518068786270 = some 175138518068786270 := by decide +kernel
private theorem endpoint_8_84_p7 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 0 7 175138518068786270 = some 175138518068786270 :=
  join_receipt_window endpoint_8_84_flag endpoint_8_84_sources 0 6 1 175138518068786270 175138518068786270 175138518068786270 endpoint_8_84_p6 endpoint_8_84_w6
def endpoint_8_84 : CertifiedEndpoint :=
  ⟨⟨8, 84, 1811⟩, 175138518068786270, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_8_84_flag endpoint_8_84_sources 7 175138518068786270 175138518068786270 rfl endpoint_8_84_base endpoint_8_84_p7) (by decide)⟩
def endpoint_8_85 : CertifiedEndpoint :=
  ⟨⟨8, 85, 1694⟩, 257764962692478451, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_86 : CertifiedEndpoint :=
  ⟨⟨8, 86, 1573⟩, 241741757937898063, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_87 : CertifiedEndpoint :=
  ⟨⟨8, 87, 1449⟩, 224766283218139402, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_88 : CertifiedEndpoint :=
  ⟨⟨8, 88, 1322⟩, 206821066163871694, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_89 : CertifiedEndpoint :=
  ⟨⟨8, 89, 1192⟩, 187888634405764165, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_90 : CertifiedEndpoint :=
  ⟨⟨8, 90, 1058⟩, 167785519453626658, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_91 : CertifiedEndpoint :=
  ⟨⟨8, 91, 922⟩, 146824299805477079, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_92 : CertifiedEndpoint :=
  ⟨⟨8, 92, 782⟩, 124653569475895802, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_93 : CertifiedEndpoint :=
  ⟨⟨8, 93, 640⟩, 101593672460381077, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_94 : CertifiedEndpoint :=
  ⟨⟨8, 94, 494⟩, 77285437276032934, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_95 : CertifiedEndpoint :=
  ⟨⟨8, 95, 345⟩, 51881270423120154, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_96 : CertifiedEndpoint :=
  ⟨⟨8, 96, 192⟩, 25186055165232064, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_9 : CertifiedEndpoint :=
  ⟨⟨9, 9, 5066⟩, 59579633182567971, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_10 : CertifiedEndpoint :=
  ⟨⟨9, 10, 5046⟩, 62933959431084676, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_11 : CertifiedEndpoint :=
  ⟨⟨9, 11, 5025⟩, 66246563278138610, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_12 : CertifiedEndpoint :=
  ⟨⟨9, 12, 5003⟩, 76932796686799355, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_13 : CertifiedEndpoint :=
  ⟨⟨9, 13, 4982⟩, 87537672798619697, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_14 : CertifiedEndpoint :=
  ⟨⟨9, 14, 4960⟩, 98028188203039360, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_15 : CertifiedEndpoint :=
  ⟨⟨9, 15, 4939⟩, 108441744468017296, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_16 : CertifiedEndpoint :=
  ⟨⟨9, 16, 4917⟩, 118736541868195877, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_17 : CertifiedEndpoint :=
  ⟨⟨9, 17, 4894⟩, 128905983167477089, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_18 : CertifiedEndpoint :=
  ⟨⟨9, 18, 4872⟩, 139000664406015912, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_19 : CertifiedEndpoint :=
  ⟨⟨9, 19, 4849⟩, 148965591386258690, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_20 : CertifiedEndpoint :=
  ⟨⟨9, 20, 4827⟩, 158860156463157755, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_21 : CertifiedEndpoint :=
  ⟨⟨9, 21, 4804⟩, 168620569124362099, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_22 : CertifiedEndpoint :=
  ⟨⟨9, 22, 4780⟩, 178240232133773708, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_23 : CertifiedEndpoint :=
  ⟨⟨9, 23, 4757⟩, 187791732318540942, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_24 : CertifiedEndpoint :=
  ⟨⟨9, 24, 4733⟩, 197198084694116765, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_25 : CertifiedEndpoint :=
  ⟨⟨9, 25, 4709⟩, 206496682213425026, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_26 : CertifiedEndpoint :=
  ⟨⟨9, 26, 4685⟩, 215687524876465725, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_27 : CertifiedEndpoint :=
  ⟨⟨9, 27, 4660⟩, 224722224336818323, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_28 : CertifiedEndpoint :=
  ⟨⟨9, 28, 4635⟩, 233644770783504683, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_29 : CertifiedEndpoint :=
  ⟨⟨9, 29, 4610⟩, 242455164216524805, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_30 : CertifiedEndpoint :=
  ⟨⟨9, 30, 4585⟩, 251153404635878689, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_31 : CertifiedEndpoint :=
  ⟨⟨9, 31, 4559⟩, 259682307380348444, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_9_32_flag : Flag := ⟨9, 32, 4533⟩
private def endpoint_9_32_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_32_base : receiptBase endpoint_9_32_flag endpoint_9_32_sources = some 183485962509578184 := by decide +kernel
private theorem endpoint_9_32_w0 : receiptWindow endpoint_9_32_flag endpoint_9_32_sources 0 2 183485962509578184 = some 183485962509578184 := by decide +kernel
private theorem endpoint_9_32_w2 : receiptWindow endpoint_9_32_flag endpoint_9_32_sources 2 2 183485962509578184 = some 183485962509578184 := by decide +kernel
private theorem endpoint_9_32_p4 : receiptWindow endpoint_9_32_flag endpoint_9_32_sources 0 4 183485962509578184 = some 183485962509578184 :=
  join_receipt_window endpoint_9_32_flag endpoint_9_32_sources 0 2 2 183485962509578184 183485962509578184 183485962509578184 endpoint_9_32_w0 endpoint_9_32_w2
private theorem endpoint_9_32_w4 : receiptWindow endpoint_9_32_flag endpoint_9_32_sources 4 2 183485962509578184 = some 183485962509578184 := by decide +kernel
private theorem endpoint_9_32_p6 : receiptWindow endpoint_9_32_flag endpoint_9_32_sources 0 6 183485962509578184 = some 183485962509578184 :=
  join_receipt_window endpoint_9_32_flag endpoint_9_32_sources 0 4 2 183485962509578184 183485962509578184 183485962509578184 endpoint_9_32_p4 endpoint_9_32_w4
private theorem endpoint_9_32_w6 : receiptWindow endpoint_9_32_flag endpoint_9_32_sources 6 2 183485962509578184 = some 183485962509578184 := by decide +kernel
private theorem endpoint_9_32_p8 : receiptWindow endpoint_9_32_flag endpoint_9_32_sources 0 8 183485962509578184 = some 183485962509578184 :=
  join_receipt_window endpoint_9_32_flag endpoint_9_32_sources 0 6 2 183485962509578184 183485962509578184 183485962509578184 endpoint_9_32_p6 endpoint_9_32_w6
def endpoint_9_32 : CertifiedEndpoint :=
  ⟨⟨9, 32, 4533⟩, 183485962509578184, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_32_flag endpoint_9_32_sources 8 183485962509578184 183485962509578184 rfl endpoint_9_32_base endpoint_9_32_p8) (by decide)⟩
private def endpoint_9_33_flag : Flag := ⟨9, 33, 4507⟩
private def endpoint_9_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_33_base : receiptBase endpoint_9_33_flag endpoint_9_33_sources = some 187090647204777983 := by decide +kernel
private theorem endpoint_9_33_w0 : receiptWindow endpoint_9_33_flag endpoint_9_33_sources 0 2 187090647204777983 = some 187090647204777983 := by decide +kernel
private theorem endpoint_9_33_w2 : receiptWindow endpoint_9_33_flag endpoint_9_33_sources 2 2 187090647204777983 = some 187090647204777983 := by decide +kernel
private theorem endpoint_9_33_p4 : receiptWindow endpoint_9_33_flag endpoint_9_33_sources 0 4 187090647204777983 = some 187090647204777983 :=
  join_receipt_window endpoint_9_33_flag endpoint_9_33_sources 0 2 2 187090647204777983 187090647204777983 187090647204777983 endpoint_9_33_w0 endpoint_9_33_w2
private theorem endpoint_9_33_w4 : receiptWindow endpoint_9_33_flag endpoint_9_33_sources 4 2 187090647204777983 = some 187090647204777983 := by decide +kernel
private theorem endpoint_9_33_p6 : receiptWindow endpoint_9_33_flag endpoint_9_33_sources 0 6 187090647204777983 = some 187090647204777983 :=
  join_receipt_window endpoint_9_33_flag endpoint_9_33_sources 0 4 2 187090647204777983 187090647204777983 187090647204777983 endpoint_9_33_p4 endpoint_9_33_w4
private theorem endpoint_9_33_w6 : receiptWindow endpoint_9_33_flag endpoint_9_33_sources 6 2 187090647204777983 = some 187090647204777983 := by decide +kernel
private theorem endpoint_9_33_p8 : receiptWindow endpoint_9_33_flag endpoint_9_33_sources 0 8 187090647204777983 = some 187090647204777983 :=
  join_receipt_window endpoint_9_33_flag endpoint_9_33_sources 0 6 2 187090647204777983 187090647204777983 187090647204777983 endpoint_9_33_p6 endpoint_9_33_w6
def endpoint_9_33 : CertifiedEndpoint :=
  ⟨⟨9, 33, 4507⟩, 187090647204777983, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_33_flag endpoint_9_33_sources 8 187090647204777983 187090647204777983 rfl endpoint_9_33_base endpoint_9_33_p8) (by decide)⟩
private def endpoint_9_34_flag : Flag := ⟨9, 34, 4480⟩
private def endpoint_9_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_34_base : receiptBase endpoint_9_34_flag endpoint_9_34_sources = some 190599509335381391 := by decide +kernel
private theorem endpoint_9_34_w0 : receiptWindow endpoint_9_34_flag endpoint_9_34_sources 0 2 190599509335381391 = some 190599509335381391 := by decide +kernel
private theorem endpoint_9_34_w2 : receiptWindow endpoint_9_34_flag endpoint_9_34_sources 2 2 190599509335381391 = some 190599509335381391 := by decide +kernel
private theorem endpoint_9_34_p4 : receiptWindow endpoint_9_34_flag endpoint_9_34_sources 0 4 190599509335381391 = some 190599509335381391 :=
  join_receipt_window endpoint_9_34_flag endpoint_9_34_sources 0 2 2 190599509335381391 190599509335381391 190599509335381391 endpoint_9_34_w0 endpoint_9_34_w2
private theorem endpoint_9_34_w4 : receiptWindow endpoint_9_34_flag endpoint_9_34_sources 4 2 190599509335381391 = some 190599509335381391 := by decide +kernel
private theorem endpoint_9_34_p6 : receiptWindow endpoint_9_34_flag endpoint_9_34_sources 0 6 190599509335381391 = some 190599509335381391 :=
  join_receipt_window endpoint_9_34_flag endpoint_9_34_sources 0 4 2 190599509335381391 190599509335381391 190599509335381391 endpoint_9_34_p4 endpoint_9_34_w4
private theorem endpoint_9_34_w6 : receiptWindow endpoint_9_34_flag endpoint_9_34_sources 6 2 190599509335381391 = some 190599509335381391 := by decide +kernel
private theorem endpoint_9_34_p8 : receiptWindow endpoint_9_34_flag endpoint_9_34_sources 0 8 190599509335381391 = some 190599509335381391 :=
  join_receipt_window endpoint_9_34_flag endpoint_9_34_sources 0 6 2 190599509335381391 190599509335381391 190599509335381391 endpoint_9_34_p6 endpoint_9_34_w6
def endpoint_9_34 : CertifiedEndpoint :=
  ⟨⟨9, 34, 4480⟩, 190599509335381391, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_34_flag endpoint_9_34_sources 8 190599509335381391 190599509335381391 rfl endpoint_9_34_base endpoint_9_34_p8) (by decide)⟩
private def endpoint_9_35_flag : Flag := ⟨9, 35, 4453⟩
private def endpoint_9_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_35_base : receiptBase endpoint_9_35_flag endpoint_9_35_sources = some 194052541835124879 := by decide +kernel
private theorem endpoint_9_35_w0 : receiptWindow endpoint_9_35_flag endpoint_9_35_sources 0 2 194052541835124879 = some 194052541835124879 := by decide +kernel
private theorem endpoint_9_35_w2 : receiptWindow endpoint_9_35_flag endpoint_9_35_sources 2 2 194052541835124879 = some 194052541835124879 := by decide +kernel
private theorem endpoint_9_35_p4 : receiptWindow endpoint_9_35_flag endpoint_9_35_sources 0 4 194052541835124879 = some 194052541835124879 :=
  join_receipt_window endpoint_9_35_flag endpoint_9_35_sources 0 2 2 194052541835124879 194052541835124879 194052541835124879 endpoint_9_35_w0 endpoint_9_35_w2
private theorem endpoint_9_35_w4 : receiptWindow endpoint_9_35_flag endpoint_9_35_sources 4 2 194052541835124879 = some 194052541835124879 := by decide +kernel
private theorem endpoint_9_35_p6 : receiptWindow endpoint_9_35_flag endpoint_9_35_sources 0 6 194052541835124879 = some 194052541835124879 :=
  join_receipt_window endpoint_9_35_flag endpoint_9_35_sources 0 4 2 194052541835124879 194052541835124879 194052541835124879 endpoint_9_35_p4 endpoint_9_35_w4
private theorem endpoint_9_35_w6 : receiptWindow endpoint_9_35_flag endpoint_9_35_sources 6 2 194052541835124879 = some 194052541835124879 := by decide +kernel
private theorem endpoint_9_35_p8 : receiptWindow endpoint_9_35_flag endpoint_9_35_sources 0 8 194052541835124879 = some 194052541835124879 :=
  join_receipt_window endpoint_9_35_flag endpoint_9_35_sources 0 6 2 194052541835124879 194052541835124879 194052541835124879 endpoint_9_35_p6 endpoint_9_35_w6
def endpoint_9_35 : CertifiedEndpoint :=
  ⟨⟨9, 35, 4453⟩, 194052541835124879, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_35_flag endpoint_9_35_sources 8 194052541835124879 194052541835124879 rfl endpoint_9_35_base endpoint_9_35_p8) (by decide)⟩
private def endpoint_9_36_flag : Flag := ⟨9, 36, 4425⟩
private def endpoint_9_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_36_base : receiptBase endpoint_9_36_flag endpoint_9_36_sources = some 197405691760726164 := by decide +kernel
private theorem endpoint_9_36_w0 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 2 197405691760726164 = some 197405691760726164 := by decide +kernel
private theorem endpoint_9_36_w2 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 2 2 197405691760726164 = some 197405691760726164 := by decide +kernel
private theorem endpoint_9_36_p4 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 4 197405691760726164 = some 197405691760726164 :=
  join_receipt_window endpoint_9_36_flag endpoint_9_36_sources 0 2 2 197405691760726164 197405691760726164 197405691760726164 endpoint_9_36_w0 endpoint_9_36_w2
private theorem endpoint_9_36_w4 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 4 2 197405691760726164 = some 197405691760726164 := by decide +kernel
private theorem endpoint_9_36_p6 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 6 197405691760726164 = some 197405691760726164 :=
  join_receipt_window endpoint_9_36_flag endpoint_9_36_sources 0 4 2 197405691760726164 197405691760726164 197405691760726164 endpoint_9_36_p4 endpoint_9_36_w4
private theorem endpoint_9_36_w6 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 6 2 197405691760726164 = some 197405691760726164 := by decide +kernel
private theorem endpoint_9_36_p8 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 8 197405691760726164 = some 197405691760726164 :=
  join_receipt_window endpoint_9_36_flag endpoint_9_36_sources 0 6 2 197405691760726164 197405691760726164 197405691760726164 endpoint_9_36_p6 endpoint_9_36_w6
def endpoint_9_36 : CertifiedEndpoint :=
  ⟨⟨9, 36, 4425⟩, 197405691760726164, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_36_flag endpoint_9_36_sources 8 197405691760726164 197405691760726164 rfl endpoint_9_36_base endpoint_9_36_p8) (by decide)⟩
private def endpoint_9_37_flag : Flag := ⟨9, 37, 4398⟩
private def endpoint_9_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_37_base : receiptBase endpoint_9_37_flag endpoint_9_37_sources = some 200746049996363362 := by decide +kernel
private theorem endpoint_9_37_w0 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 2 200746049996363362 = some 200746049996363362 := by decide +kernel
private theorem endpoint_9_37_w2 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 2 2 200746049996363362 = some 200746049996363362 := by decide +kernel
private theorem endpoint_9_37_p4 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 4 200746049996363362 = some 200746049996363362 :=
  join_receipt_window endpoint_9_37_flag endpoint_9_37_sources 0 2 2 200746049996363362 200746049996363362 200746049996363362 endpoint_9_37_w0 endpoint_9_37_w2
private theorem endpoint_9_37_w4 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 4 2 200746049996363362 = some 200746049996363362 := by decide +kernel
private theorem endpoint_9_37_p6 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 6 200746049996363362 = some 200746049996363362 :=
  join_receipt_window endpoint_9_37_flag endpoint_9_37_sources 0 4 2 200746049996363362 200746049996363362 200746049996363362 endpoint_9_37_p4 endpoint_9_37_w4
private theorem endpoint_9_37_w6 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 6 2 200746049996363362 = some 200746049996363362 := by decide +kernel
private theorem endpoint_9_37_p8 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 8 200746049996363362 = some 200746049996363362 :=
  join_receipt_window endpoint_9_37_flag endpoint_9_37_sources 0 6 2 200746049996363362 200746049996363362 200746049996363362 endpoint_9_37_p6 endpoint_9_37_w6
def endpoint_9_37 : CertifiedEndpoint :=
  ⟨⟨9, 37, 4398⟩, 200746049996363362, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_37_flag endpoint_9_37_sources 8 200746049996363362 200746049996363362 rfl endpoint_9_37_base endpoint_9_37_p8) (by decide)⟩
private def endpoint_9_38_flag : Flag := ⟨9, 38, 4369⟩
private def endpoint_9_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_38_base : receiptBase endpoint_9_38_flag endpoint_9_38_sources = some 203938412705030260 := by decide +kernel
private theorem endpoint_9_38_w0 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 2 203938412705030260 = some 203938412705030260 := by decide +kernel
private theorem endpoint_9_38_w2 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 2 2 203938412705030260 = some 203938412705030260 := by decide +kernel
private theorem endpoint_9_38_p4 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 4 203938412705030260 = some 203938412705030260 :=
  join_receipt_window endpoint_9_38_flag endpoint_9_38_sources 0 2 2 203938412705030260 203938412705030260 203938412705030260 endpoint_9_38_w0 endpoint_9_38_w2
private theorem endpoint_9_38_w4 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 4 2 203938412705030260 = some 203938412705030260 := by decide +kernel
private theorem endpoint_9_38_p6 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 6 203938412705030260 = some 203938412705030260 :=
  join_receipt_window endpoint_9_38_flag endpoint_9_38_sources 0 4 2 203938412705030260 203938412705030260 203938412705030260 endpoint_9_38_p4 endpoint_9_38_w4
private theorem endpoint_9_38_w6 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 6 2 203938412705030260 = some 203938412705030260 := by decide +kernel
private theorem endpoint_9_38_p8 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 8 203938412705030260 = some 203938412705030260 :=
  join_receipt_window endpoint_9_38_flag endpoint_9_38_sources 0 6 2 203938412705030260 203938412705030260 203938412705030260 endpoint_9_38_p6 endpoint_9_38_w6
def endpoint_9_38 : CertifiedEndpoint :=
  ⟨⟨9, 38, 4369⟩, 203938412705030260, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_38_flag endpoint_9_38_sources 8 203938412705030260 203938412705030260 rfl endpoint_9_38_base endpoint_9_38_p8) (by decide)⟩
private def endpoint_9_39_flag : Flag := ⟨9, 39, 4341⟩
private def endpoint_9_39_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_39_base : receiptBase endpoint_9_39_flag endpoint_9_39_sources = some 207117983723733072 := by decide +kernel
private theorem endpoint_9_39_w0 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 2 207117983723733072 = some 207117983723733072 := by decide +kernel
private theorem endpoint_9_39_w2 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 2 2 207117983723733072 = some 207117983723733072 := by decide +kernel
private theorem endpoint_9_39_p4 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 4 207117983723733072 = some 207117983723733072 :=
  join_receipt_window endpoint_9_39_flag endpoint_9_39_sources 0 2 2 207117983723733072 207117983723733072 207117983723733072 endpoint_9_39_w0 endpoint_9_39_w2
private theorem endpoint_9_39_w4 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 4 2 207117983723733072 = some 207117983723733072 := by decide +kernel
private theorem endpoint_9_39_p6 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 6 207117983723733072 = some 207117983723733072 :=
  join_receipt_window endpoint_9_39_flag endpoint_9_39_sources 0 4 2 207117983723733072 207117983723733072 207117983723733072 endpoint_9_39_p4 endpoint_9_39_w4
private theorem endpoint_9_39_w6 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 6 2 207117983723733072 = some 207117983723733072 := by decide +kernel
private theorem endpoint_9_39_p8 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 8 207117983723733072 = some 207117983723733072 :=
  join_receipt_window endpoint_9_39_flag endpoint_9_39_sources 0 6 2 207117983723733072 207117983723733072 207117983723733072 endpoint_9_39_p6 endpoint_9_39_w6
def endpoint_9_39 : CertifiedEndpoint :=
  ⟨⟨9, 39, 4341⟩, 207117983723733072, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_39_flag endpoint_9_39_sources 8 207117983723733072 207117983723733072 rfl endpoint_9_39_base endpoint_9_39_p8) (by decide)⟩
private def endpoint_9_40_flag : Flag := ⟨9, 40, 4312⟩
private def endpoint_9_40_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_40_base : receiptBase endpoint_9_40_flag endpoint_9_40_sources = some 210191582153974964 := by decide +kernel
private theorem endpoint_9_40_w0 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 2 210191582153974964 = some 210191582153974964 := by decide +kernel
private theorem endpoint_9_40_w2 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 2 2 210191582153974964 = some 210191582153974964 := by decide +kernel
private theorem endpoint_9_40_p4 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 4 210191582153974964 = some 210191582153974964 :=
  join_receipt_window endpoint_9_40_flag endpoint_9_40_sources 0 2 2 210191582153974964 210191582153974964 210191582153974964 endpoint_9_40_w0 endpoint_9_40_w2
private theorem endpoint_9_40_w4 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 4 2 210191582153974964 = some 210191582153974964 := by decide +kernel
private theorem endpoint_9_40_p6 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 6 210191582153974964 = some 210191582153974964 :=
  join_receipt_window endpoint_9_40_flag endpoint_9_40_sources 0 4 2 210191582153974964 210191582153974964 210191582153974964 endpoint_9_40_p4 endpoint_9_40_w4
private theorem endpoint_9_40_w6 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 6 2 210191582153974964 = some 210191582153974964 := by decide +kernel
private theorem endpoint_9_40_p8 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 8 210191582153974964 = some 210191582153974964 :=
  join_receipt_window endpoint_9_40_flag endpoint_9_40_sources 0 6 2 210191582153974964 210191582153974964 210191582153974964 endpoint_9_40_p6 endpoint_9_40_w6
def endpoint_9_40 : CertifiedEndpoint :=
  ⟨⟨9, 40, 4312⟩, 210191582153974964, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_40_flag endpoint_9_40_sources 8 210191582153974964 210191582153974964 rfl endpoint_9_40_base endpoint_9_40_p8) (by decide)⟩
private def endpoint_9_41_flag : Flag := ⟨9, 41, 4282⟩
private def endpoint_9_41_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_41_base : receiptBase endpoint_9_41_flag endpoint_9_41_sources = some 213691293734120936 := by decide +kernel
private theorem endpoint_9_41_w0 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 2 213691293734120936 = some 213691293734120936 := by decide +kernel
private theorem endpoint_9_41_w2 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 2 2 213691293734120936 = some 213691293734120936 := by decide +kernel
private theorem endpoint_9_41_p4 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 4 213691293734120936 = some 213691293734120936 :=
  join_receipt_window endpoint_9_41_flag endpoint_9_41_sources 0 2 2 213691293734120936 213691293734120936 213691293734120936 endpoint_9_41_w0 endpoint_9_41_w2
private theorem endpoint_9_41_w4 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 4 2 213691293734120936 = some 213691293734120936 := by decide +kernel
private theorem endpoint_9_41_p6 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 6 213691293734120936 = some 213691293734120936 :=
  join_receipt_window endpoint_9_41_flag endpoint_9_41_sources 0 4 2 213691293734120936 213691293734120936 213691293734120936 endpoint_9_41_p4 endpoint_9_41_w4
private theorem endpoint_9_41_w6 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 6 2 213691293734120936 = some 213691293734120936 := by decide +kernel
private theorem endpoint_9_41_p8 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 8 213691293734120936 = some 213691293734120936 :=
  join_receipt_window endpoint_9_41_flag endpoint_9_41_sources 0 6 2 213691293734120936 213691293734120936 213691293734120936 endpoint_9_41_p6 endpoint_9_41_w6
def endpoint_9_41 : CertifiedEndpoint :=
  ⟨⟨9, 41, 4282⟩, 213691293734120936, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_41_flag endpoint_9_41_sources 8 213691293734120936 213691293734120936 rfl endpoint_9_41_base endpoint_9_41_p8) (by decide)⟩
private def endpoint_9_42_flag : Flag := ⟨9, 42, 4252⟩
private def endpoint_9_42_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_42_base : receiptBase endpoint_9_42_flag endpoint_9_42_sources = some 216562676160703509 := by decide +kernel
private theorem endpoint_9_42_w0 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 2 216562676160703509 = some 216562676160703509 := by decide +kernel
private theorem endpoint_9_42_w2 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 2 2 216562676160703509 = some 216562676160703509 := by decide +kernel
private theorem endpoint_9_42_p4 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 4 216562676160703509 = some 216562676160703509 :=
  join_receipt_window endpoint_9_42_flag endpoint_9_42_sources 0 2 2 216562676160703509 216562676160703509 216562676160703509 endpoint_9_42_w0 endpoint_9_42_w2
private theorem endpoint_9_42_w4 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 4 2 216562676160703509 = some 216562676160703509 := by decide +kernel
private theorem endpoint_9_42_p6 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 6 216562676160703509 = some 216562676160703509 :=
  join_receipt_window endpoint_9_42_flag endpoint_9_42_sources 0 4 2 216562676160703509 216562676160703509 216562676160703509 endpoint_9_42_p4 endpoint_9_42_w4
private theorem endpoint_9_42_w6 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 6 2 216562676160703509 = some 216562676160703509 := by decide +kernel
private theorem endpoint_9_42_p8 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 8 216562676160703509 = some 216562676160703509 :=
  join_receipt_window endpoint_9_42_flag endpoint_9_42_sources 0 6 2 216562676160703509 216562676160703509 216562676160703509 endpoint_9_42_p6 endpoint_9_42_w6
def endpoint_9_42 : CertifiedEndpoint :=
  ⟨⟨9, 42, 4252⟩, 216562676160703509, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_42_flag endpoint_9_42_sources 8 216562676160703509 216562676160703509 rfl endpoint_9_42_base endpoint_9_42_p8) (by decide)⟩
private def endpoint_9_43_flag : Flag := ⟨9, 43, 4221⟩
private def endpoint_9_43_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_43_base : receiptBase endpoint_9_43_flag endpoint_9_43_sources = some 219321080047616216 := by decide +kernel
private theorem endpoint_9_43_w0 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 2 219321080047616216 = some 219321080047616216 := by decide +kernel
private theorem endpoint_9_43_w2 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 2 2 219321080047616216 = some 219321080047616216 := by decide +kernel
private theorem endpoint_9_43_p4 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 4 219321080047616216 = some 219321080047616216 :=
  join_receipt_window endpoint_9_43_flag endpoint_9_43_sources 0 2 2 219321080047616216 219321080047616216 219321080047616216 endpoint_9_43_w0 endpoint_9_43_w2
private theorem endpoint_9_43_w4 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 4 2 219321080047616216 = some 219321080047616216 := by decide +kernel
private theorem endpoint_9_43_p6 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 6 219321080047616216 = some 219321080047616216 :=
  join_receipt_window endpoint_9_43_flag endpoint_9_43_sources 0 4 2 219321080047616216 219321080047616216 219321080047616216 endpoint_9_43_p4 endpoint_9_43_w4
private theorem endpoint_9_43_w6 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 6 2 219321080047616216 = some 219321080047616216 := by decide +kernel
private theorem endpoint_9_43_p8 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 8 219321080047616216 = some 219321080047616216 :=
  join_receipt_window endpoint_9_43_flag endpoint_9_43_sources 0 6 2 219321080047616216 219321080047616216 219321080047616216 endpoint_9_43_p6 endpoint_9_43_w6
def endpoint_9_43 : CertifiedEndpoint :=
  ⟨⟨9, 43, 4221⟩, 219321080047616216, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_43_flag endpoint_9_43_sources 8 219321080047616216 219321080047616216 rfl endpoint_9_43_base endpoint_9_43_p8) (by decide)⟩
private def endpoint_9_44_flag : Flag := ⟨9, 44, 4190⟩
private def endpoint_9_44_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_44_base : receiptBase endpoint_9_44_flag endpoint_9_44_sources = some 222015822211449587 := by decide +kernel
private theorem endpoint_9_44_w0 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 2 222015822211449587 = some 222015822211449587 := by decide +kernel
private theorem endpoint_9_44_w2 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 2 2 222015822211449587 = some 222015822211449587 := by decide +kernel
private theorem endpoint_9_44_p4 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 4 222015822211449587 = some 222015822211449587 :=
  join_receipt_window endpoint_9_44_flag endpoint_9_44_sources 0 2 2 222015822211449587 222015822211449587 222015822211449587 endpoint_9_44_w0 endpoint_9_44_w2
private theorem endpoint_9_44_w4 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 4 2 222015822211449587 = some 222015822211449587 := by decide +kernel
private theorem endpoint_9_44_p6 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 6 222015822211449587 = some 222015822211449587 :=
  join_receipt_window endpoint_9_44_flag endpoint_9_44_sources 0 4 2 222015822211449587 222015822211449587 222015822211449587 endpoint_9_44_p4 endpoint_9_44_w4
private theorem endpoint_9_44_w6 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 6 2 222015822211449587 = some 222015822211449587 := by decide +kernel
private theorem endpoint_9_44_p8 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 8 222015822211449587 = some 222015822211449587 :=
  join_receipt_window endpoint_9_44_flag endpoint_9_44_sources 0 6 2 222015822211449587 222015822211449587 222015822211449587 endpoint_9_44_p6 endpoint_9_44_w6
def endpoint_9_44 : CertifiedEndpoint :=
  ⟨⟨9, 44, 4190⟩, 222015822211449587, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_44_flag endpoint_9_44_sources 8 222015822211449587 222015822211449587 rfl endpoint_9_44_base endpoint_9_44_p8) (by decide)⟩
private def endpoint_9_45_flag : Flag := ⟨9, 45, 4159⟩
private def endpoint_9_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_45_base : receiptBase endpoint_9_45_flag endpoint_9_45_sources = some 224646902652203622 := by decide +kernel
private theorem endpoint_9_45_w0 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 2 224646902652203622 = some 224646902652203622 := by decide +kernel
private theorem endpoint_9_45_w2 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 2 2 224646902652203622 = some 224646902652203622 := by decide +kernel
private theorem endpoint_9_45_p4 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 4 224646902652203622 = some 224646902652203622 :=
  join_receipt_window endpoint_9_45_flag endpoint_9_45_sources 0 2 2 224646902652203622 224646902652203622 224646902652203622 endpoint_9_45_w0 endpoint_9_45_w2
private theorem endpoint_9_45_w4 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 4 2 224646902652203622 = some 224646902652203622 := by decide +kernel
private theorem endpoint_9_45_p6 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 6 224646902652203622 = some 224646902652203622 :=
  join_receipt_window endpoint_9_45_flag endpoint_9_45_sources 0 4 2 224646902652203622 224646902652203622 224646902652203622 endpoint_9_45_p4 endpoint_9_45_w4
private theorem endpoint_9_45_w6 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 6 2 224646902652203622 = some 224646902652203622 := by decide +kernel
private theorem endpoint_9_45_p8 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 8 224646902652203622 = some 224646902652203622 :=
  join_receipt_window endpoint_9_45_flag endpoint_9_45_sources 0 6 2 224646902652203622 224646902652203622 224646902652203622 endpoint_9_45_p6 endpoint_9_45_w6
def endpoint_9_45 : CertifiedEndpoint :=
  ⟨⟨9, 45, 4159⟩, 224646902652203622, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_45_flag endpoint_9_45_sources 8 224646902652203622 224646902652203622 rfl endpoint_9_45_base endpoint_9_45_p8) (by decide)⟩
private def endpoint_9_46_flag : Flag := ⟨9, 46, 4126⟩
private def endpoint_9_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_46_base : receiptBase endpoint_9_46_flag endpoint_9_46_sources = some 227105582701287840 := by decide +kernel
private theorem endpoint_9_46_w0 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 2 227105582701287840 = some 227105582701287840 := by decide +kernel
private theorem endpoint_9_46_w2 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 2 2 227105582701287840 = some 227105582701287840 := by decide +kernel
private theorem endpoint_9_46_p4 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 4 227105582701287840 = some 227105582701287840 :=
  join_receipt_window endpoint_9_46_flag endpoint_9_46_sources 0 2 2 227105582701287840 227105582701287840 227105582701287840 endpoint_9_46_w0 endpoint_9_46_w2
private theorem endpoint_9_46_w4 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 4 2 227105582701287840 = some 227105582701287840 := by decide +kernel
private theorem endpoint_9_46_p6 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 6 227105582701287840 = some 227105582701287840 :=
  join_receipt_window endpoint_9_46_flag endpoint_9_46_sources 0 4 2 227105582701287840 227105582701287840 227105582701287840 endpoint_9_46_p4 endpoint_9_46_w4
private theorem endpoint_9_46_w6 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 6 2 227105582701287840 = some 227105582701287840 := by decide +kernel
private theorem endpoint_9_46_p8 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 8 227105582701287840 = some 227105582701287840 :=
  join_receipt_window endpoint_9_46_flag endpoint_9_46_sources 0 6 2 227105582701287840 227105582701287840 227105582701287840 endpoint_9_46_p6 endpoint_9_46_w6
def endpoint_9_46 : CertifiedEndpoint :=
  ⟨⟨9, 46, 4126⟩, 227105582701287840, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_46_flag endpoint_9_46_sources 8 227105582701287840 227105582701287840 rfl endpoint_9_46_base endpoint_9_46_p8) (by decide)⟩
private def endpoint_9_47_flag : Flag := ⟨9, 47, 4094⟩
private def endpoint_9_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_47_base : receiptBase endpoint_9_47_flag endpoint_9_47_sources = some 229551938850965138 := by decide +kernel
private theorem endpoint_9_47_w0 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 2 229551938850965138 = some 229551938850965138 := by decide +kernel
private theorem endpoint_9_47_w2 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 2 2 229551938850965138 = some 229551938850965138 := by decide +kernel
private theorem endpoint_9_47_p4 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 4 229551938850965138 = some 229551938850965138 :=
  join_receipt_window endpoint_9_47_flag endpoint_9_47_sources 0 2 2 229551938850965138 229551938850965138 229551938850965138 endpoint_9_47_w0 endpoint_9_47_w2
private theorem endpoint_9_47_w4 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 4 2 229551938850965138 = some 229551938850965138 := by decide +kernel
private theorem endpoint_9_47_p6 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 6 229551938850965138 = some 229551938850965138 :=
  join_receipt_window endpoint_9_47_flag endpoint_9_47_sources 0 4 2 229551938850965138 229551938850965138 229551938850965138 endpoint_9_47_p4 endpoint_9_47_w4
private theorem endpoint_9_47_w6 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 6 2 229551938850965138 = some 229551938850965138 := by decide +kernel
private theorem endpoint_9_47_p8 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 8 229551938850965138 = some 229551938850965138 :=
  join_receipt_window endpoint_9_47_flag endpoint_9_47_sources 0 6 2 229551938850965138 229551938850965138 229551938850965138 endpoint_9_47_p6 endpoint_9_47_w6
def endpoint_9_47 : CertifiedEndpoint :=
  ⟨⟨9, 47, 4094⟩, 229551938850965138, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_47_flag endpoint_9_47_sources 8 229551938850965138 229551938850965138 rfl endpoint_9_47_base endpoint_9_47_p8) (by decide)⟩
private def endpoint_9_48_flag : Flag := ⟨9, 48, 4060⟩
private def endpoint_9_48_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_48_base : receiptBase endpoint_9_48_flag endpoint_9_48_sources = some 231819831587726968 := by decide +kernel
private theorem endpoint_9_48_w0 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 2 231819831587726968 = some 231819831587726968 := by decide +kernel
private theorem endpoint_9_48_w2 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 2 2 231819831587726968 = some 231819831587726968 := by decide +kernel
private theorem endpoint_9_48_p4 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 4 231819831587726968 = some 231819831587726968 :=
  join_receipt_window endpoint_9_48_flag endpoint_9_48_sources 0 2 2 231819831587726968 231819831587726968 231819831587726968 endpoint_9_48_w0 endpoint_9_48_w2
private theorem endpoint_9_48_w4 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 4 2 231819831587726968 = some 231819831587726968 := by decide +kernel
private theorem endpoint_9_48_p6 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 6 231819831587726968 = some 231819831587726968 :=
  join_receipt_window endpoint_9_48_flag endpoint_9_48_sources 0 4 2 231819831587726968 231819831587726968 231819831587726968 endpoint_9_48_p4 endpoint_9_48_w4
private theorem endpoint_9_48_w6 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 6 2 231819831587726968 = some 231819831587726968 := by decide +kernel
private theorem endpoint_9_48_p8 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 8 231819831587726968 = some 231819831587726968 :=
  join_receipt_window endpoint_9_48_flag endpoint_9_48_sources 0 6 2 231819831587726968 231819831587726968 231819831587726968 endpoint_9_48_p6 endpoint_9_48_w6
def endpoint_9_48 : CertifiedEndpoint :=
  ⟨⟨9, 48, 4060⟩, 231819831587726968, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_48_flag endpoint_9_48_sources 8 231819831587726968 231819831587726968 rfl endpoint_9_48_base endpoint_9_48_p8) (by decide)⟩
private def endpoint_9_49_flag : Flag := ⟨9, 49, 4026⟩
private def endpoint_9_49_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_49_base : receiptBase endpoint_9_49_flag endpoint_9_49_sources = some 234017999580163811 := by decide +kernel
private theorem endpoint_9_49_w0 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 2 234017999580163811 = some 234017999580163811 := by decide +kernel
private theorem endpoint_9_49_w2 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 2 2 234017999580163811 = some 234017999580163811 := by decide +kernel
private theorem endpoint_9_49_p4 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 4 234017999580163811 = some 234017999580163811 :=
  join_receipt_window endpoint_9_49_flag endpoint_9_49_sources 0 2 2 234017999580163811 234017999580163811 234017999580163811 endpoint_9_49_w0 endpoint_9_49_w2
private theorem endpoint_9_49_w4 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 4 2 234017999580163811 = some 234017999580163811 := by decide +kernel
private theorem endpoint_9_49_p6 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 6 234017999580163811 = some 234017999580163811 :=
  join_receipt_window endpoint_9_49_flag endpoint_9_49_sources 0 4 2 234017999580163811 234017999580163811 234017999580163811 endpoint_9_49_p4 endpoint_9_49_w4
private theorem endpoint_9_49_w6 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 6 2 234017999580163811 = some 234017999580163811 := by decide +kernel
private theorem endpoint_9_49_p8 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 8 234017999580163811 = some 234017999580163811 :=
  join_receipt_window endpoint_9_49_flag endpoint_9_49_sources 0 6 2 234017999580163811 234017999580163811 234017999580163811 endpoint_9_49_p6 endpoint_9_49_w6
def endpoint_9_49 : CertifiedEndpoint :=
  ⟨⟨9, 49, 4026⟩, 234017999580163811, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_49_flag endpoint_9_49_sources 8 234017999580163811 234017999580163811 rfl endpoint_9_49_base endpoint_9_49_p8) (by decide)⟩
private def endpoint_9_50_flag : Flag := ⟨9, 50, 3991⟩
private def endpoint_9_50_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_50_base : receiptBase endpoint_9_50_flag endpoint_9_50_sources = some 236088031479816659 := by decide +kernel
private theorem endpoint_9_50_w0 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 2 236088031479816659 = some 236088031479816659 := by decide +kernel
private theorem endpoint_9_50_w2 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 2 2 236088031479816659 = some 236088031479816659 := by decide +kernel
private theorem endpoint_9_50_p4 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 4 236088031479816659 = some 236088031479816659 :=
  join_receipt_window endpoint_9_50_flag endpoint_9_50_sources 0 2 2 236088031479816659 236088031479816659 236088031479816659 endpoint_9_50_w0 endpoint_9_50_w2
private theorem endpoint_9_50_w4 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 4 2 236088031479816659 = some 236088031479816659 := by decide +kernel
private theorem endpoint_9_50_p6 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 6 236088031479816659 = some 236088031479816659 :=
  join_receipt_window endpoint_9_50_flag endpoint_9_50_sources 0 4 2 236088031479816659 236088031479816659 236088031479816659 endpoint_9_50_p4 endpoint_9_50_w4
private theorem endpoint_9_50_w6 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 6 2 236088031479816659 = some 236088031479816659 := by decide +kernel
private theorem endpoint_9_50_p8 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 8 236088031479816659 = some 236088031479816659 :=
  join_receipt_window endpoint_9_50_flag endpoint_9_50_sources 0 6 2 236088031479816659 236088031479816659 236088031479816659 endpoint_9_50_p6 endpoint_9_50_w6
def endpoint_9_50 : CertifiedEndpoint :=
  ⟨⟨9, 50, 3991⟩, 236088031479816659, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_50_flag endpoint_9_50_sources 8 236088031479816659 236088031479816659 rfl endpoint_9_50_base endpoint_9_50_p8) (by decide)⟩
private def endpoint_9_51_flag : Flag := ⟨9, 51, 3955⟩
private def endpoint_9_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_51_base : receiptBase endpoint_9_51_flag endpoint_9_51_sources = some 238026895776062688 := by decide +kernel
private theorem endpoint_9_51_w0 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 2 238026895776062688 = some 238026895776062688 := by decide +kernel
private theorem endpoint_9_51_w2 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 2 2 238026895776062688 = some 238026895776062688 := by decide +kernel
private theorem endpoint_9_51_p4 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 4 238026895776062688 = some 238026895776062688 :=
  join_receipt_window endpoint_9_51_flag endpoint_9_51_sources 0 2 2 238026895776062688 238026895776062688 238026895776062688 endpoint_9_51_w0 endpoint_9_51_w2
private theorem endpoint_9_51_w4 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 4 2 238026895776062688 = some 238026895776062688 := by decide +kernel
private theorem endpoint_9_51_p6 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 6 238026895776062688 = some 238026895776062688 :=
  join_receipt_window endpoint_9_51_flag endpoint_9_51_sources 0 4 2 238026895776062688 238026895776062688 238026895776062688 endpoint_9_51_p4 endpoint_9_51_w4
private theorem endpoint_9_51_w6 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 6 2 238026895776062688 = some 238026895776062688 := by decide +kernel
private theorem endpoint_9_51_p8 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 8 238026895776062688 = some 238026895776062688 :=
  join_receipt_window endpoint_9_51_flag endpoint_9_51_sources 0 6 2 238026895776062688 238026895776062688 238026895776062688 endpoint_9_51_p6 endpoint_9_51_w6
def endpoint_9_51 : CertifiedEndpoint :=
  ⟨⟨9, 51, 3955⟩, 238026895776062688, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_51_flag endpoint_9_51_sources 8 238026895776062688 238026895776062688 rfl endpoint_9_51_base endpoint_9_51_p8) (by decide)⟩
private def endpoint_9_52_flag : Flag := ⟨9, 52, 3919⟩
private def endpoint_9_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_52_base : receiptBase endpoint_9_52_flag endpoint_9_52_sources = some 239891993313819962 := by decide +kernel
private theorem endpoint_9_52_w0 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 2 239891993313819962 = some 239891993313819962 := by decide +kernel
private theorem endpoint_9_52_w2 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 2 2 239891993313819962 = some 239891993313819962 := by decide +kernel
private theorem endpoint_9_52_p4 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 4 239891993313819962 = some 239891993313819962 :=
  join_receipt_window endpoint_9_52_flag endpoint_9_52_sources 0 2 2 239891993313819962 239891993313819962 239891993313819962 endpoint_9_52_w0 endpoint_9_52_w2
private theorem endpoint_9_52_w4 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 4 2 239891993313819962 = some 239891993313819962 := by decide +kernel
private theorem endpoint_9_52_p6 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 6 239891993313819962 = some 239891993313819962 :=
  join_receipt_window endpoint_9_52_flag endpoint_9_52_sources 0 4 2 239891993313819962 239891993313819962 239891993313819962 endpoint_9_52_p4 endpoint_9_52_w4
private theorem endpoint_9_52_w6 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 6 2 239891993313819962 = some 239891993313819962 := by decide +kernel
private theorem endpoint_9_52_p8 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 8 239891993313819962 = some 239891993313819962 :=
  join_receipt_window endpoint_9_52_flag endpoint_9_52_sources 0 6 2 239891993313819962 239891993313819962 239891993313819962 endpoint_9_52_p6 endpoint_9_52_w6
def endpoint_9_52 : CertifiedEndpoint :=
  ⟨⟨9, 52, 3919⟩, 239891993313819962, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_52_flag endpoint_9_52_sources 8 239891993313819962 239891993313819962 rfl endpoint_9_52_base endpoint_9_52_p8) (by decide)⟩
private def endpoint_9_53_flag : Flag := ⟨9, 53, 3881⟩
private def endpoint_9_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_53_base : receiptBase endpoint_9_53_flag endpoint_9_53_sources = some 241560438374924816 := by decide +kernel
private theorem endpoint_9_53_w0 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 2 241560438374924816 = some 241560438374924816 := by decide +kernel
private theorem endpoint_9_53_w2 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 2 2 241560438374924816 = some 241560438374924816 := by decide +kernel
private theorem endpoint_9_53_p4 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 4 241560438374924816 = some 241560438374924816 :=
  join_receipt_window endpoint_9_53_flag endpoint_9_53_sources 0 2 2 241560438374924816 241560438374924816 241560438374924816 endpoint_9_53_w0 endpoint_9_53_w2
private theorem endpoint_9_53_w4 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 4 2 241560438374924816 = some 241560438374924816 := by decide +kernel
private theorem endpoint_9_53_p6 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 6 241560438374924816 = some 241560438374924816 :=
  join_receipt_window endpoint_9_53_flag endpoint_9_53_sources 0 4 2 241560438374924816 241560438374924816 241560438374924816 endpoint_9_53_p4 endpoint_9_53_w4
private theorem endpoint_9_53_w6 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 6 2 241560438374924816 = some 241560438374924816 := by decide +kernel
private theorem endpoint_9_53_p8 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 8 241560438374924816 = some 241560438374924816 :=
  join_receipt_window endpoint_9_53_flag endpoint_9_53_sources 0 6 2 241560438374924816 241560438374924816 241560438374924816 endpoint_9_53_p6 endpoint_9_53_w6
def endpoint_9_53 : CertifiedEndpoint :=
  ⟨⟨9, 53, 3881⟩, 241560438374924816, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_53_flag endpoint_9_53_sources 8 241560438374924816 241560438374924816 rfl endpoint_9_53_base endpoint_9_53_p8) (by decide)⟩
private def endpoint_9_54_flag : Flag := ⟨9, 54, 3843⟩
private def endpoint_9_54_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_54_base : receiptBase endpoint_9_54_flag endpoint_9_54_sources = some 243151074663377148 := by decide +kernel
private theorem endpoint_9_54_w0 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 2 243151074663377148 = some 243151074663377148 := by decide +kernel
private theorem endpoint_9_54_w2 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 2 2 243151074663377148 = some 243151074663377148 := by decide +kernel
private theorem endpoint_9_54_p4 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 4 243151074663377148 = some 243151074663377148 :=
  join_receipt_window endpoint_9_54_flag endpoint_9_54_sources 0 2 2 243151074663377148 243151074663377148 243151074663377148 endpoint_9_54_w0 endpoint_9_54_w2
private theorem endpoint_9_54_w4 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 4 2 243151074663377148 = some 243151074663377148 := by decide +kernel
private theorem endpoint_9_54_p6 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 6 243151074663377148 = some 243151074663377148 :=
  join_receipt_window endpoint_9_54_flag endpoint_9_54_sources 0 4 2 243151074663377148 243151074663377148 243151074663377148 endpoint_9_54_p4 endpoint_9_54_w4
private theorem endpoint_9_54_w6 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 6 2 243151074663377148 = some 243151074663377148 := by decide +kernel
private theorem endpoint_9_54_p8 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 8 243151074663377148 = some 243151074663377148 :=
  join_receipt_window endpoint_9_54_flag endpoint_9_54_sources 0 6 2 243151074663377148 243151074663377148 243151074663377148 endpoint_9_54_p6 endpoint_9_54_w6
def endpoint_9_54 : CertifiedEndpoint :=
  ⟨⟨9, 54, 3843⟩, 243151074663377148, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_54_flag endpoint_9_54_sources 8 243151074663377148 243151074663377148 rfl endpoint_9_54_base endpoint_9_54_p8) (by decide)⟩
private def endpoint_9_55_flag : Flag := ⟨9, 55, 3803⟩
private def endpoint_9_55_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_9_55_base : receiptBase endpoint_9_55_flag endpoint_9_55_sources = some 245312838426784991 := by decide +kernel
private theorem endpoint_9_55_w0 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 2 245312838426784991 = some 245312838426784991 := by decide +kernel
private theorem endpoint_9_55_w2 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 2 2 245312838426784991 = some 245312838426784991 := by decide +kernel
private theorem endpoint_9_55_p4 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 4 245312838426784991 = some 245312838426784991 :=
  join_receipt_window endpoint_9_55_flag endpoint_9_55_sources 0 2 2 245312838426784991 245312838426784991 245312838426784991 endpoint_9_55_w0 endpoint_9_55_w2
private theorem endpoint_9_55_w4 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 4 2 245312838426784991 = some 245312838426784991 := by decide +kernel
private theorem endpoint_9_55_p6 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 6 245312838426784991 = some 245312838426784991 :=
  join_receipt_window endpoint_9_55_flag endpoint_9_55_sources 0 4 2 245312838426784991 245312838426784991 245312838426784991 endpoint_9_55_p4 endpoint_9_55_w4
private theorem endpoint_9_55_w6 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 6 2 245312838426784991 = some 245312838426784991 := by decide +kernel
private theorem endpoint_9_55_p8 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 8 245312838426784991 = some 245312838426784991 :=
  join_receipt_window endpoint_9_55_flag endpoint_9_55_sources 0 6 2 245312838426784991 245312838426784991 245312838426784991 endpoint_9_55_p6 endpoint_9_55_w6
def endpoint_9_55 : CertifiedEndpoint :=
  ⟨⟨9, 55, 3803⟩, 245312838426784991, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_9_55_flag endpoint_9_55_sources 8 245312838426784991 245312838426784991 rfl endpoint_9_55_base endpoint_9_55_p8) (by decide)⟩
private def endpoint_9_56_flag : Flag := ⟨9, 56, 3762⟩
private def endpoint_9_56_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_9_56_base : receiptBase endpoint_9_56_flag endpoint_9_56_sources = some 246560396025659773 := by decide +kernel
private theorem endpoint_9_56_w0 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 2 246560396025659773 = some 246560396025659773 := by decide +kernel
private theorem endpoint_9_56_w2 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 2 2 246560396025659773 = some 246560396025659773 := by decide +kernel
private theorem endpoint_9_56_p4 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 4 246560396025659773 = some 246560396025659773 :=
  join_receipt_window endpoint_9_56_flag endpoint_9_56_sources 0 2 2 246560396025659773 246560396025659773 246560396025659773 endpoint_9_56_w0 endpoint_9_56_w2
private theorem endpoint_9_56_w4 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 4 2 246560396025659773 = some 246560396025659773 := by decide +kernel
private theorem endpoint_9_56_p6 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 6 246560396025659773 = some 246560396025659773 :=
  join_receipt_window endpoint_9_56_flag endpoint_9_56_sources 0 4 2 246560396025659773 246560396025659773 246560396025659773 endpoint_9_56_p4 endpoint_9_56_w4
private theorem endpoint_9_56_w6 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 6 2 246560396025659773 = some 246560396025659773 := by decide +kernel
private theorem endpoint_9_56_p8 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 8 246560396025659773 = some 246560396025659773 :=
  join_receipt_window endpoint_9_56_flag endpoint_9_56_sources 0 6 2 246560396025659773 246560396025659773 246560396025659773 endpoint_9_56_p6 endpoint_9_56_w6
def endpoint_9_56 : CertifiedEndpoint :=
  ⟨⟨9, 56, 3762⟩, 246560396025659773, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_9_56_flag endpoint_9_56_sources 8 246560396025659773 246560396025659773 rfl endpoint_9_56_base endpoint_9_56_p8) (by decide)⟩
private def endpoint_9_57_flag : Flag := ⟨9, 57, 3720⟩
private def endpoint_9_57_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_9_57_base : receiptBase endpoint_9_57_flag endpoint_9_57_sources = some 247658002910033291 := by decide +kernel
private theorem endpoint_9_57_w0 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 2 247658002910033291 = some 247658002910033291 := by decide +kernel
private theorem endpoint_9_57_w2 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 2 2 247658002910033291 = some 247658002910033291 := by decide +kernel
private theorem endpoint_9_57_p4 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 4 247658002910033291 = some 247658002910033291 :=
  join_receipt_window endpoint_9_57_flag endpoint_9_57_sources 0 2 2 247658002910033291 247658002910033291 247658002910033291 endpoint_9_57_w0 endpoint_9_57_w2
private theorem endpoint_9_57_w4 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 4 2 247658002910033291 = some 247658002910033291 := by decide +kernel
private theorem endpoint_9_57_p6 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 6 247658002910033291 = some 247658002910033291 :=
  join_receipt_window endpoint_9_57_flag endpoint_9_57_sources 0 4 2 247658002910033291 247658002910033291 247658002910033291 endpoint_9_57_p4 endpoint_9_57_w4
private theorem endpoint_9_57_w6 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 6 2 247658002910033291 = some 247658002910033291 := by decide +kernel
private theorem endpoint_9_57_p8 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 8 247658002910033291 = some 247658002910033291 :=
  join_receipt_window endpoint_9_57_flag endpoint_9_57_sources 0 6 2 247658002910033291 247658002910033291 247658002910033291 endpoint_9_57_p6 endpoint_9_57_w6
def endpoint_9_57 : CertifiedEndpoint :=
  ⟨⟨9, 57, 3720⟩, 247658002910033291, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_9_57_flag endpoint_9_57_sources 8 247658002910033291 247658002910033291 rfl endpoint_9_57_base endpoint_9_57_p8) (by decide)⟩
private def endpoint_9_58_flag : Flag := ⟨9, 58, 3677⟩
private def endpoint_9_58_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_9_58_base : receiptBase endpoint_9_58_flag endpoint_9_58_sources = some 248684033851734860 := by decide +kernel
private theorem endpoint_9_58_w0 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 2 248684033851734860 = some 248684033851734860 := by decide +kernel
private theorem endpoint_9_58_w2 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 2 2 248684033851734860 = some 248684033851734860 := by decide +kernel
private theorem endpoint_9_58_p4 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 4 248684033851734860 = some 248684033851734860 :=
  join_receipt_window endpoint_9_58_flag endpoint_9_58_sources 0 2 2 248684033851734860 248684033851734860 248684033851734860 endpoint_9_58_w0 endpoint_9_58_w2
private theorem endpoint_9_58_w4 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 4 2 248684033851734860 = some 248684033851734860 := by decide +kernel
private theorem endpoint_9_58_p6 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 6 248684033851734860 = some 248684033851734860 :=
  join_receipt_window endpoint_9_58_flag endpoint_9_58_sources 0 4 2 248684033851734860 248684033851734860 248684033851734860 endpoint_9_58_p4 endpoint_9_58_w4
private theorem endpoint_9_58_w6 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 6 2 248684033851734860 = some 248684033851734860 := by decide +kernel
private theorem endpoint_9_58_p8 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 8 248684033851734860 = some 248684033851734860 :=
  join_receipt_window endpoint_9_58_flag endpoint_9_58_sources 0 6 2 248684033851734860 248684033851734860 248684033851734860 endpoint_9_58_p6 endpoint_9_58_w6
def endpoint_9_58 : CertifiedEndpoint :=
  ⟨⟨9, 58, 3677⟩, 248684033851734860, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_9_58_flag endpoint_9_58_sources 8 248684033851734860 248684033851734860 rfl endpoint_9_58_base endpoint_9_58_p8) (by decide)⟩
private def endpoint_9_59_flag : Flag := ⟨9, 59, 3632⟩
private def endpoint_9_59_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_59_base : receiptBase endpoint_9_59_flag endpoint_9_59_sources = some 251860613141258755 := by decide +kernel
private theorem endpoint_9_59_w0 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 2 251860613141258755 = some 251860613141258755 := by decide +kernel
private theorem endpoint_9_59_w2 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 2 2 251860613141258755 = some 251860613141258755 := by decide +kernel
private theorem endpoint_9_59_p4 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 4 251860613141258755 = some 251860613141258755 :=
  join_receipt_window endpoint_9_59_flag endpoint_9_59_sources 0 2 2 251860613141258755 251860613141258755 251860613141258755 endpoint_9_59_w0 endpoint_9_59_w2
private theorem endpoint_9_59_w4 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 4 2 251860613141258755 = some 251860613141258755 := by decide +kernel
private theorem endpoint_9_59_p6 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 6 251860613141258755 = some 251860613141258755 :=
  join_receipt_window endpoint_9_59_flag endpoint_9_59_sources 0 4 2 251860613141258755 251860613141258755 251860613141258755 endpoint_9_59_p4 endpoint_9_59_w4
private theorem endpoint_9_59_w6 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 6 2 251860613141258755 = some 251860613141258755 := by decide +kernel
private theorem endpoint_9_59_p8 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 8 251860613141258755 = some 251860613141258755 :=
  join_receipt_window endpoint_9_59_flag endpoint_9_59_sources 0 6 2 251860613141258755 251860613141258755 251860613141258755 endpoint_9_59_p6 endpoint_9_59_w6
def endpoint_9_59 : CertifiedEndpoint :=
  ⟨⟨9, 59, 3632⟩, 251860613141258755, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_59_flag endpoint_9_59_sources 8 251860613141258755 251860613141258755 rfl endpoint_9_59_base endpoint_9_59_p8) (by decide)⟩
private def endpoint_9_60_flag : Flag := ⟨9, 60, 3586⟩
private def endpoint_9_60_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_60_base : receiptBase endpoint_9_60_flag endpoint_9_60_sources = some 252383657532410573 := by decide +kernel
private theorem endpoint_9_60_w0 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 2 252383657532410573 = some 252383657532410573 := by decide +kernel
private theorem endpoint_9_60_w2 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 2 2 252383657532410573 = some 252383657532410573 := by decide +kernel
private theorem endpoint_9_60_p4 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 4 252383657532410573 = some 252383657532410573 :=
  join_receipt_window endpoint_9_60_flag endpoint_9_60_sources 0 2 2 252383657532410573 252383657532410573 252383657532410573 endpoint_9_60_w0 endpoint_9_60_w2
private theorem endpoint_9_60_w4 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 4 2 252383657532410573 = some 252383657532410573 := by decide +kernel
private theorem endpoint_9_60_p6 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 6 252383657532410573 = some 252383657532410573 :=
  join_receipt_window endpoint_9_60_flag endpoint_9_60_sources 0 4 2 252383657532410573 252383657532410573 252383657532410573 endpoint_9_60_p4 endpoint_9_60_w4
private theorem endpoint_9_60_w6 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 6 2 252383657532410573 = some 252383657532410573 := by decide +kernel
private theorem endpoint_9_60_p8 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 8 252383657532410573 = some 252383657532410573 :=
  join_receipt_window endpoint_9_60_flag endpoint_9_60_sources 0 6 2 252383657532410573 252383657532410573 252383657532410573 endpoint_9_60_p6 endpoint_9_60_w6
def endpoint_9_60 : CertifiedEndpoint :=
  ⟨⟨9, 60, 3586⟩, 252383657532410573, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_60_flag endpoint_9_60_sources 8 252383657532410573 252383657532410573 rfl endpoint_9_60_base endpoint_9_60_p8) (by decide)⟩
private def endpoint_9_61_flag : Flag := ⟨9, 61, 3538⟩
private def endpoint_9_61_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_61_base : receiptBase endpoint_9_61_flag endpoint_9_61_sources = some 252670582386076429 := by decide +kernel
private theorem endpoint_9_61_w0 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 2 252670582386076429 = some 252670582386076429 := by decide +kernel
private theorem endpoint_9_61_w2 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 2 2 252670582386076429 = some 252670582386076429 := by decide +kernel
private theorem endpoint_9_61_p4 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 4 252670582386076429 = some 252670582386076429 :=
  join_receipt_window endpoint_9_61_flag endpoint_9_61_sources 0 2 2 252670582386076429 252670582386076429 252670582386076429 endpoint_9_61_w0 endpoint_9_61_w2
private theorem endpoint_9_61_w4 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 4 2 252670582386076429 = some 252670582386076429 := by decide +kernel
private theorem endpoint_9_61_p6 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 6 252670582386076429 = some 252670582386076429 :=
  join_receipt_window endpoint_9_61_flag endpoint_9_61_sources 0 4 2 252670582386076429 252670582386076429 252670582386076429 endpoint_9_61_p4 endpoint_9_61_w4
private theorem endpoint_9_61_w6 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 6 2 252670582386076429 = some 252670582386076429 := by decide +kernel
private theorem endpoint_9_61_p8 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 8 252670582386076429 = some 252670582386076429 :=
  join_receipt_window endpoint_9_61_flag endpoint_9_61_sources 0 6 2 252670582386076429 252670582386076429 252670582386076429 endpoint_9_61_p6 endpoint_9_61_w6
def endpoint_9_61 : CertifiedEndpoint :=
  ⟨⟨9, 61, 3538⟩, 252670582386076429, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_61_flag endpoint_9_61_sources 8 252670582386076429 252670582386076429 rfl endpoint_9_61_base endpoint_9_61_p8) (by decide)⟩
private def endpoint_9_62_flag : Flag := ⟨9, 62, 3487⟩
private def endpoint_9_62_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_62_base : receiptBase endpoint_9_62_flag endpoint_9_62_sources = some 252643598142174463 := by decide +kernel
private theorem endpoint_9_62_w0 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 2 252643598142174463 = some 252643598142174463 := by decide +kernel
private theorem endpoint_9_62_w2 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 2 2 252643598142174463 = some 252643598142174463 := by decide +kernel
private theorem endpoint_9_62_p4 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 4 252643598142174463 = some 252643598142174463 :=
  join_receipt_window endpoint_9_62_flag endpoint_9_62_sources 0 2 2 252643598142174463 252643598142174463 252643598142174463 endpoint_9_62_w0 endpoint_9_62_w2
private theorem endpoint_9_62_w4 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 4 2 252643598142174463 = some 252643598142174463 := by decide +kernel
private theorem endpoint_9_62_p6 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 6 252643598142174463 = some 252643598142174463 :=
  join_receipt_window endpoint_9_62_flag endpoint_9_62_sources 0 4 2 252643598142174463 252643598142174463 252643598142174463 endpoint_9_62_p4 endpoint_9_62_w4
private theorem endpoint_9_62_w6 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 6 2 252643598142174463 = some 252643598142174463 := by decide +kernel
private theorem endpoint_9_62_p8 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 8 252643598142174463 = some 252643598142174463 :=
  join_receipt_window endpoint_9_62_flag endpoint_9_62_sources 0 6 2 252643598142174463 252643598142174463 252643598142174463 endpoint_9_62_p6 endpoint_9_62_w6
def endpoint_9_62 : CertifiedEndpoint :=
  ⟨⟨9, 62, 3487⟩, 252643598142174463, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_62_flag endpoint_9_62_sources 8 252643598142174463 252643598142174463 rfl endpoint_9_62_base endpoint_9_62_p8) (by decide)⟩
private def endpoint_9_63_flag : Flag := ⟨9, 63, 3435⟩
private def endpoint_9_63_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_63_base : receiptBase endpoint_9_63_flag endpoint_9_63_sources = some 252438913440752920 := by decide +kernel
private theorem endpoint_9_63_w0 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 2 252438913440752920 = some 252438913440752920 := by decide +kernel
private theorem endpoint_9_63_w2 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 2 2 252438913440752920 = some 252438913440752920 := by decide +kernel
private theorem endpoint_9_63_p4 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 4 252438913440752920 = some 252438913440752920 :=
  join_receipt_window endpoint_9_63_flag endpoint_9_63_sources 0 2 2 252438913440752920 252438913440752920 252438913440752920 endpoint_9_63_w0 endpoint_9_63_w2
private theorem endpoint_9_63_w4 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 4 2 252438913440752920 = some 252438913440752920 := by decide +kernel
private theorem endpoint_9_63_p6 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 6 252438913440752920 = some 252438913440752920 :=
  join_receipt_window endpoint_9_63_flag endpoint_9_63_sources 0 4 2 252438913440752920 252438913440752920 252438913440752920 endpoint_9_63_p4 endpoint_9_63_w4
private theorem endpoint_9_63_w6 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 6 2 252438913440752920 = some 252438913440752920 := by decide +kernel
private theorem endpoint_9_63_p8 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 8 252438913440752920 = some 252438913440752920 :=
  join_receipt_window endpoint_9_63_flag endpoint_9_63_sources 0 6 2 252438913440752920 252438913440752920 252438913440752920 endpoint_9_63_p6 endpoint_9_63_w6
def endpoint_9_63 : CertifiedEndpoint :=
  ⟨⟨9, 63, 3435⟩, 252438913440752920, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_63_flag endpoint_9_63_sources 8 252438913440752920 252438913440752920 rfl endpoint_9_63_base endpoint_9_63_p8) (by decide)⟩
private def endpoint_9_64_flag : Flag := ⟨9, 64, 3379⟩
private def endpoint_9_64_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_9_64_base : receiptBase endpoint_9_64_flag endpoint_9_64_sources = some 253291294866612600 := by decide +kernel
private theorem endpoint_9_64_w0 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 2 253291294866612600 = some 253291294866612600 := by decide +kernel
private theorem endpoint_9_64_w2 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 2 2 253291294866612600 = some 253291294866612600 := by decide +kernel
private theorem endpoint_9_64_p4 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 4 253291294866612600 = some 253291294866612600 :=
  join_receipt_window endpoint_9_64_flag endpoint_9_64_sources 0 2 2 253291294866612600 253291294866612600 253291294866612600 endpoint_9_64_w0 endpoint_9_64_w2
private theorem endpoint_9_64_w4 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 4 2 253291294866612600 = some 253291294866612600 := by decide +kernel
private theorem endpoint_9_64_p6 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 6 253291294866612600 = some 253291294866612600 :=
  join_receipt_window endpoint_9_64_flag endpoint_9_64_sources 0 4 2 253291294866612600 253291294866612600 253291294866612600 endpoint_9_64_p4 endpoint_9_64_w4
private theorem endpoint_9_64_w6 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 6 2 253291294866612600 = some 253291294866612600 := by decide +kernel
private theorem endpoint_9_64_p8 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 8 253291294866612600 = some 253291294866612600 :=
  join_receipt_window endpoint_9_64_flag endpoint_9_64_sources 0 6 2 253291294866612600 253291294866612600 253291294866612600 endpoint_9_64_p6 endpoint_9_64_w6
def endpoint_9_64 : CertifiedEndpoint :=
  ⟨⟨9, 64, 3379⟩, 253291294866612600, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_9_64_flag endpoint_9_64_sources 8 253291294866612600 253291294866612600 rfl endpoint_9_64_base endpoint_9_64_p8) (by decide)⟩
private def endpoint_9_65_flag : Flag := ⟨9, 65, 3321⟩
private def endpoint_9_65_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_9_65_base : receiptBase endpoint_9_65_flag endpoint_9_65_sources = some 252417436569150982 := by decide +kernel
private theorem endpoint_9_65_w0 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 2 252417436569150982 = some 252417436569150982 := by decide +kernel
private theorem endpoint_9_65_w2 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 2 2 252417436569150982 = some 252417436569150982 := by decide +kernel
private theorem endpoint_9_65_p4 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 4 252417436569150982 = some 252417436569150982 :=
  join_receipt_window endpoint_9_65_flag endpoint_9_65_sources 0 2 2 252417436569150982 252417436569150982 252417436569150982 endpoint_9_65_w0 endpoint_9_65_w2
private theorem endpoint_9_65_w4 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 4 2 252417436569150982 = some 252417436569150982 := by decide +kernel
private theorem endpoint_9_65_p6 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 6 252417436569150982 = some 252417436569150982 :=
  join_receipt_window endpoint_9_65_flag endpoint_9_65_sources 0 4 2 252417436569150982 252417436569150982 252417436569150982 endpoint_9_65_p4 endpoint_9_65_w4
private theorem endpoint_9_65_w6 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 6 2 252417436569150982 = some 252417436569150982 := by decide +kernel
private theorem endpoint_9_65_p8 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 8 252417436569150982 = some 252417436569150982 :=
  join_receipt_window endpoint_9_65_flag endpoint_9_65_sources 0 6 2 252417436569150982 252417436569150982 252417436569150982 endpoint_9_65_p6 endpoint_9_65_w6
def endpoint_9_65 : CertifiedEndpoint :=
  ⟨⟨9, 65, 3321⟩, 252417436569150982, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_9_65_flag endpoint_9_65_sources 8 252417436569150982 252417436569150982 rfl endpoint_9_65_base endpoint_9_65_p8) (by decide)⟩
private def endpoint_9_66_flag : Flag := ⟨9, 66, 3260⟩
private def endpoint_9_66_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_9_66_base : receiptBase endpoint_9_66_flag endpoint_9_66_sources = some 252698042961680092 := by decide +kernel
private theorem endpoint_9_66_w0 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 2 252698042961680092 = some 252698042961680092 := by decide +kernel
private theorem endpoint_9_66_w2 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 2 2 252698042961680092 = some 252698042961680092 := by decide +kernel
private theorem endpoint_9_66_p4 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 4 252698042961680092 = some 252698042961680092 :=
  join_receipt_window endpoint_9_66_flag endpoint_9_66_sources 0 2 2 252698042961680092 252698042961680092 252698042961680092 endpoint_9_66_w0 endpoint_9_66_w2
private theorem endpoint_9_66_w4 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 4 2 252698042961680092 = some 252698042961680092 := by decide +kernel
private theorem endpoint_9_66_p6 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 6 252698042961680092 = some 252698042961680092 :=
  join_receipt_window endpoint_9_66_flag endpoint_9_66_sources 0 4 2 252698042961680092 252698042961680092 252698042961680092 endpoint_9_66_p4 endpoint_9_66_w4
private theorem endpoint_9_66_w6 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 6 2 252698042961680092 = some 252698042961680092 := by decide +kernel
private theorem endpoint_9_66_p8 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 8 252698042961680092 = some 252698042961680092 :=
  join_receipt_window endpoint_9_66_flag endpoint_9_66_sources 0 6 2 252698042961680092 252698042961680092 252698042961680092 endpoint_9_66_p6 endpoint_9_66_w6
def endpoint_9_66 : CertifiedEndpoint :=
  ⟨⟨9, 66, 3260⟩, 252698042961680092, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_9_66_flag endpoint_9_66_sources 8 252698042961680092 252698042961680092 rfl endpoint_9_66_base endpoint_9_66_p8) (by decide)⟩
private def endpoint_9_67_flag : Flag := ⟨9, 67, 3196⟩
private def endpoint_9_67_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_9_67_base : receiptBase endpoint_9_67_flag endpoint_9_67_sources = some 251109768735302336 := by decide +kernel
private theorem endpoint_9_67_w0 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 2 251109768735302336 = some 251109768735302336 := by decide +kernel
private theorem endpoint_9_67_w2 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 2 2 251109768735302336 = some 251109768735302336 := by decide +kernel
private theorem endpoint_9_67_p4 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 4 251109768735302336 = some 251109768735302336 :=
  join_receipt_window endpoint_9_67_flag endpoint_9_67_sources 0 2 2 251109768735302336 251109768735302336 251109768735302336 endpoint_9_67_w0 endpoint_9_67_w2
private theorem endpoint_9_67_w4 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 4 2 251109768735302336 = some 251109768735302336 := by decide +kernel
private theorem endpoint_9_67_p6 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 6 251109768735302336 = some 251109768735302336 :=
  join_receipt_window endpoint_9_67_flag endpoint_9_67_sources 0 4 2 251109768735302336 251109768735302336 251109768735302336 endpoint_9_67_p4 endpoint_9_67_w4
private theorem endpoint_9_67_w6 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 6 2 251109768735302336 = some 251109768735302336 := by decide +kernel
private theorem endpoint_9_67_p8 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 8 251109768735302336 = some 251109768735302336 :=
  join_receipt_window endpoint_9_67_flag endpoint_9_67_sources 0 6 2 251109768735302336 251109768735302336 251109768735302336 endpoint_9_67_p6 endpoint_9_67_w6
def endpoint_9_67 : CertifiedEndpoint :=
  ⟨⟨9, 67, 3196⟩, 251109768735302336, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_9_67_flag endpoint_9_67_sources 8 251109768735302336 251109768735302336 rfl endpoint_9_67_base endpoint_9_67_p8) (by decide)⟩
private def endpoint_9_68_flag : Flag := ⟨9, 68, 3129⟩
private def endpoint_9_68_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_9_68_base : receiptBase endpoint_9_68_flag endpoint_9_68_sources = some 250687674123041717 := by decide +kernel
private theorem endpoint_9_68_w0 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 2 250687674123041717 = some 250687674123041717 := by decide +kernel
private theorem endpoint_9_68_w2 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 2 2 250687674123041717 = some 250687674123041717 := by decide +kernel
private theorem endpoint_9_68_p4 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 4 250687674123041717 = some 250687674123041717 :=
  join_receipt_window endpoint_9_68_flag endpoint_9_68_sources 0 2 2 250687674123041717 250687674123041717 250687674123041717 endpoint_9_68_w0 endpoint_9_68_w2
private theorem endpoint_9_68_w4 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 4 2 250687674123041717 = some 250687674123041717 := by decide +kernel
private theorem endpoint_9_68_p6 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 6 250687674123041717 = some 250687674123041717 :=
  join_receipt_window endpoint_9_68_flag endpoint_9_68_sources 0 4 2 250687674123041717 250687674123041717 250687674123041717 endpoint_9_68_p4 endpoint_9_68_w4
private theorem endpoint_9_68_w6 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 6 2 250687674123041717 = some 250687674123041717 := by decide +kernel
private theorem endpoint_9_68_p8 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 8 250687674123041717 = some 250687674123041717 :=
  join_receipt_window endpoint_9_68_flag endpoint_9_68_sources 0 6 2 250687674123041717 250687674123041717 250687674123041717 endpoint_9_68_p6 endpoint_9_68_w6
def endpoint_9_68 : CertifiedEndpoint :=
  ⟨⟨9, 68, 3129⟩, 250687674123041717, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_9_68_flag endpoint_9_68_sources 8 250687674123041717 250687674123041717 rfl endpoint_9_68_base endpoint_9_68_p8) (by decide)⟩
private def endpoint_9_69_flag : Flag := ⟨9, 69, 3059⟩
private def endpoint_9_69_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_9_69_base : receiptBase endpoint_9_69_flag endpoint_9_69_sources = some 249898591343210369 := by decide +kernel
private theorem endpoint_9_69_w0 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 2 249898591343210369 = some 249898591343210369 := by decide +kernel
private theorem endpoint_9_69_w2 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 2 2 249898591343210369 = some 249898591343210369 := by decide +kernel
private theorem endpoint_9_69_p4 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 4 249898591343210369 = some 249898591343210369 :=
  join_receipt_window endpoint_9_69_flag endpoint_9_69_sources 0 2 2 249898591343210369 249898591343210369 249898591343210369 endpoint_9_69_w0 endpoint_9_69_w2
private theorem endpoint_9_69_w4 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 4 2 249898591343210369 = some 249898591343210369 := by decide +kernel
private theorem endpoint_9_69_p6 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 6 249898591343210369 = some 249898591343210369 :=
  join_receipt_window endpoint_9_69_flag endpoint_9_69_sources 0 4 2 249898591343210369 249898591343210369 249898591343210369 endpoint_9_69_p4 endpoint_9_69_w4
private theorem endpoint_9_69_w6 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 6 2 249898591343210369 = some 249898591343210369 := by decide +kernel
private theorem endpoint_9_69_p8 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 8 249898591343210369 = some 249898591343210369 :=
  join_receipt_window endpoint_9_69_flag endpoint_9_69_sources 0 6 2 249898591343210369 249898591343210369 249898591343210369 endpoint_9_69_p6 endpoint_9_69_w6
def endpoint_9_69 : CertifiedEndpoint :=
  ⟨⟨9, 69, 3059⟩, 249898591343210369, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_9_69_flag endpoint_9_69_sources 8 249898591343210369 249898591343210369 rfl endpoint_9_69_base endpoint_9_69_p8) (by decide)⟩
private def endpoint_9_70_flag : Flag := ⟨9, 70, 2986⟩
private def endpoint_9_70_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_9_70_base : receiptBase endpoint_9_70_flag endpoint_9_70_sources = some 248579201543679976 := by decide +kernel
private theorem endpoint_9_70_w0 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 2 248579201543679976 = some 248579201543679976 := by decide +kernel
private theorem endpoint_9_70_w2 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 2 2 248579201543679976 = some 248579201543679976 := by decide +kernel
private theorem endpoint_9_70_p4 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 4 248579201543679976 = some 248579201543679976 :=
  join_receipt_window endpoint_9_70_flag endpoint_9_70_sources 0 2 2 248579201543679976 248579201543679976 248579201543679976 endpoint_9_70_w0 endpoint_9_70_w2
private theorem endpoint_9_70_w4 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 4 2 248579201543679976 = some 248579201543679976 := by decide +kernel
private theorem endpoint_9_70_p6 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 6 248579201543679976 = some 248579201543679976 :=
  join_receipt_window endpoint_9_70_flag endpoint_9_70_sources 0 4 2 248579201543679976 248579201543679976 248579201543679976 endpoint_9_70_p4 endpoint_9_70_w4
private theorem endpoint_9_70_w6 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 6 2 248579201543679976 = some 248579201543679976 := by decide +kernel
private theorem endpoint_9_70_p8 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 8 248579201543679976 = some 248579201543679976 :=
  join_receipt_window endpoint_9_70_flag endpoint_9_70_sources 0 6 2 248579201543679976 248579201543679976 248579201543679976 endpoint_9_70_p6 endpoint_9_70_w6
def endpoint_9_70 : CertifiedEndpoint :=
  ⟨⟨9, 70, 2986⟩, 248579201543679976, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_9_70_flag endpoint_9_70_sources 8 248579201543679976 248579201543679976 rfl endpoint_9_70_base endpoint_9_70_p8) (by decide)⟩
private def endpoint_9_71_flag : Flag := ⟨9, 71, 2909⟩
private def endpoint_9_71_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_9_71_base : receiptBase endpoint_9_71_flag endpoint_9_71_sources = some 245316563490140668 := by decide +kernel
private theorem endpoint_9_71_w0 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 2 245316563490140668 = some 245316563490140668 := by decide +kernel
private theorem endpoint_9_71_w2 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 2 2 245316563490140668 = some 245316563490140668 := by decide +kernel
private theorem endpoint_9_71_p4 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 4 245316563490140668 = some 245316563490140668 :=
  join_receipt_window endpoint_9_71_flag endpoint_9_71_sources 0 2 2 245316563490140668 245316563490140668 245316563490140668 endpoint_9_71_w0 endpoint_9_71_w2
private theorem endpoint_9_71_w4 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 4 2 245316563490140668 = some 245316563490140668 := by decide +kernel
private theorem endpoint_9_71_p6 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 6 245316563490140668 = some 245316563490140668 :=
  join_receipt_window endpoint_9_71_flag endpoint_9_71_sources 0 4 2 245316563490140668 245316563490140668 245316563490140668 endpoint_9_71_p4 endpoint_9_71_w4
private theorem endpoint_9_71_w6 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 6 2 245316563490140668 = some 245316563490140668 := by decide +kernel
private theorem endpoint_9_71_p8 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 8 245316563490140668 = some 245316563490140668 :=
  join_receipt_window endpoint_9_71_flag endpoint_9_71_sources 0 6 2 245316563490140668 245316563490140668 245316563490140668 endpoint_9_71_p6 endpoint_9_71_w6
def endpoint_9_71 : CertifiedEndpoint :=
  ⟨⟨9, 71, 2909⟩, 245316563490140668, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_9_71_flag endpoint_9_71_sources 8 245316563490140668 245316563490140668 rfl endpoint_9_71_base endpoint_9_71_p8) (by decide)⟩
private def endpoint_9_72_flag : Flag := ⟨9, 72, 2830⟩
private def endpoint_9_72_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_9_72_base : receiptBase endpoint_9_72_flag endpoint_9_72_sources = some 241719555565785304 := by decide +kernel
private theorem endpoint_9_72_w0 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 2 241719555565785304 = some 241719555565785304 := by decide +kernel
private theorem endpoint_9_72_w2 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 2 2 241719555565785304 = some 241719555565785304 := by decide +kernel
private theorem endpoint_9_72_p4 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 4 241719555565785304 = some 241719555565785304 :=
  join_receipt_window endpoint_9_72_flag endpoint_9_72_sources 0 2 2 241719555565785304 241719555565785304 241719555565785304 endpoint_9_72_w0 endpoint_9_72_w2
private theorem endpoint_9_72_w4 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 4 2 241719555565785304 = some 241719555565785304 := by decide +kernel
private theorem endpoint_9_72_p6 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 6 241719555565785304 = some 241719555565785304 :=
  join_receipt_window endpoint_9_72_flag endpoint_9_72_sources 0 4 2 241719555565785304 241719555565785304 241719555565785304 endpoint_9_72_p4 endpoint_9_72_w4
private theorem endpoint_9_72_w6 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 6 2 241719555565785304 = some 241719555565785304 := by decide +kernel
private theorem endpoint_9_72_p8 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 8 241719555565785304 = some 241719555565785304 :=
  join_receipt_window endpoint_9_72_flag endpoint_9_72_sources 0 6 2 241719555565785304 241719555565785304 241719555565785304 endpoint_9_72_p6 endpoint_9_72_w6
def endpoint_9_72 : CertifiedEndpoint :=
  ⟨⟨9, 72, 2830⟩, 241719555565785304, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_9_72_flag endpoint_9_72_sources 8 241719555565785304 241719555565785304 rfl endpoint_9_72_base endpoint_9_72_p8) (by decide)⟩
private def endpoint_9_73_flag : Flag := ⟨9, 73, 2747⟩
private def endpoint_9_73_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_9_73_base : receiptBase endpoint_9_73_flag endpoint_9_73_sources = some 242355735747124495 := by decide +kernel
private theorem endpoint_9_73_w0 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 2 242355735747124495 = some 242355735747124495 := by decide +kernel
private theorem endpoint_9_73_w2 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 2 2 242355735747124495 = some 242355735747124495 := by decide +kernel
private theorem endpoint_9_73_p4 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 4 242355735747124495 = some 242355735747124495 :=
  join_receipt_window endpoint_9_73_flag endpoint_9_73_sources 0 2 2 242355735747124495 242355735747124495 242355735747124495 endpoint_9_73_w0 endpoint_9_73_w2
private theorem endpoint_9_73_w4 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 4 2 242355735747124495 = some 242355735747124495 := by decide +kernel
private theorem endpoint_9_73_p6 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 6 242355735747124495 = some 242355735747124495 :=
  join_receipt_window endpoint_9_73_flag endpoint_9_73_sources 0 4 2 242355735747124495 242355735747124495 242355735747124495 endpoint_9_73_p4 endpoint_9_73_w4
private theorem endpoint_9_73_w6 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 6 2 242355735747124495 = some 242355735747124495 := by decide +kernel
private theorem endpoint_9_73_p8 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 8 242355735747124495 = some 242355735747124495 :=
  join_receipt_window endpoint_9_73_flag endpoint_9_73_sources 0 6 2 242355735747124495 242355735747124495 242355735747124495 endpoint_9_73_p6 endpoint_9_73_w6
def endpoint_9_73 : CertifiedEndpoint :=
  ⟨⟨9, 73, 2747⟩, 242355735747124495, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_9_73_flag endpoint_9_73_sources 8 242355735747124495 242355735747124495 rfl endpoint_9_73_base endpoint_9_73_p8) (by decide)⟩
private def endpoint_9_74_flag : Flag := ⟨9, 74, 2662⟩
private def endpoint_9_74_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_9_74_base : receiptBase endpoint_9_74_flag endpoint_9_74_sources = some 237852323006496113 := by decide +kernel
private theorem endpoint_9_74_w0 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 2 237852323006496113 = some 237852323006496113 := by decide +kernel
private theorem endpoint_9_74_w2 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 2 2 237852323006496113 = some 237852323006496113 := by decide +kernel
private theorem endpoint_9_74_p4 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 4 237852323006496113 = some 237852323006496113 :=
  join_receipt_window endpoint_9_74_flag endpoint_9_74_sources 0 2 2 237852323006496113 237852323006496113 237852323006496113 endpoint_9_74_w0 endpoint_9_74_w2
private theorem endpoint_9_74_w4 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 4 2 237852323006496113 = some 237852323006496113 := by decide +kernel
private theorem endpoint_9_74_p6 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 6 237852323006496113 = some 237852323006496113 :=
  join_receipt_window endpoint_9_74_flag endpoint_9_74_sources 0 4 2 237852323006496113 237852323006496113 237852323006496113 endpoint_9_74_p4 endpoint_9_74_w4
private theorem endpoint_9_74_w6 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 6 2 237852323006496113 = some 237852323006496113 := by decide +kernel
private theorem endpoint_9_74_p8 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 8 237852323006496113 = some 237852323006496113 :=
  join_receipt_window endpoint_9_74_flag endpoint_9_74_sources 0 6 2 237852323006496113 237852323006496113 237852323006496113 endpoint_9_74_p6 endpoint_9_74_w6
def endpoint_9_74 : CertifiedEndpoint :=
  ⟨⟨9, 74, 2662⟩, 237852323006496113, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_9_74_flag endpoint_9_74_sources 8 237852323006496113 237852323006496113 rfl endpoint_9_74_base endpoint_9_74_p8) (by decide)⟩
private def endpoint_9_75_flag : Flag := ⟨9, 75, 2573⟩
private def endpoint_9_75_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_9_75_base : receiptBase endpoint_9_75_flag endpoint_9_75_sources = some 232811150600190098 := by decide +kernel
private theorem endpoint_9_75_w0 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 2 232811150600190098 = some 232811150600190098 := by decide +kernel
private theorem endpoint_9_75_w2 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 2 2 232811150600190098 = some 232811150600190098 := by decide +kernel
private theorem endpoint_9_75_p4 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 4 232811150600190098 = some 232811150600190098 :=
  join_receipt_window endpoint_9_75_flag endpoint_9_75_sources 0 2 2 232811150600190098 232811150600190098 232811150600190098 endpoint_9_75_w0 endpoint_9_75_w2
private theorem endpoint_9_75_w4 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 4 2 232811150600190098 = some 232811150600190098 := by decide +kernel
private theorem endpoint_9_75_p6 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 6 232811150600190098 = some 232811150600190098 :=
  join_receipt_window endpoint_9_75_flag endpoint_9_75_sources 0 4 2 232811150600190098 232811150600190098 232811150600190098 endpoint_9_75_p4 endpoint_9_75_w4
private theorem endpoint_9_75_w6 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 6 2 232811150600190098 = some 232811150600190098 := by decide +kernel
private theorem endpoint_9_75_p8 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 8 232811150600190098 = some 232811150600190098 :=
  join_receipt_window endpoint_9_75_flag endpoint_9_75_sources 0 6 2 232811150600190098 232811150600190098 232811150600190098 endpoint_9_75_p6 endpoint_9_75_w6
def endpoint_9_75 : CertifiedEndpoint :=
  ⟨⟨9, 75, 2573⟩, 232811150600190098, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_9_75_flag endpoint_9_75_sources 8 232811150600190098 232811150600190098 rfl endpoint_9_75_base endpoint_9_75_p8) (by decide)⟩
private def endpoint_9_76_flag : Flag := ⟨9, 76, 2482⟩
private def endpoint_9_76_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_9_76_base : receiptBase endpoint_9_76_flag endpoint_9_76_sources = some 229567692500460635 := by decide +kernel
private theorem endpoint_9_76_w0 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 2 229567692500460635 = some 229567692500460635 := by decide +kernel
private theorem endpoint_9_76_w2 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 2 2 229567692500460635 = some 229567692500460635 := by decide +kernel
private theorem endpoint_9_76_p4 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 4 229567692500460635 = some 229567692500460635 :=
  join_receipt_window endpoint_9_76_flag endpoint_9_76_sources 0 2 2 229567692500460635 229567692500460635 229567692500460635 endpoint_9_76_w0 endpoint_9_76_w2
private theorem endpoint_9_76_w4 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 4 2 229567692500460635 = some 229567692500460635 := by decide +kernel
private theorem endpoint_9_76_p6 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 6 229567692500460635 = some 229567692500460635 :=
  join_receipt_window endpoint_9_76_flag endpoint_9_76_sources 0 4 2 229567692500460635 229567692500460635 229567692500460635 endpoint_9_76_p4 endpoint_9_76_w4
private theorem endpoint_9_76_w6 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 6 2 229567692500460635 = some 229567692500460635 := by decide +kernel
private theorem endpoint_9_76_p8 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 8 229567692500460635 = some 229567692500460635 :=
  join_receipt_window endpoint_9_76_flag endpoint_9_76_sources 0 6 2 229567692500460635 229567692500460635 229567692500460635 endpoint_9_76_p6 endpoint_9_76_w6
def endpoint_9_76 : CertifiedEndpoint :=
  ⟨⟨9, 76, 2482⟩, 229567692500460635, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_9_76_flag endpoint_9_76_sources 8 229567692500460635 229567692500460635 rfl endpoint_9_76_base endpoint_9_76_p8) (by decide)⟩
private def endpoint_9_77_flag : Flag := ⟨9, 77, 2387⟩
private def endpoint_9_77_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_9_77_base : receiptBase endpoint_9_77_flag endpoint_9_77_sources = some 223458957748994753 := by decide +kernel
private theorem endpoint_9_77_w0 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 2 223458957748994753 = some 223458957748994753 := by decide +kernel
private theorem endpoint_9_77_w2 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 2 2 223458957748994753 = some 223458957748994753 := by decide +kernel
private theorem endpoint_9_77_p4 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 4 223458957748994753 = some 223458957748994753 :=
  join_receipt_window endpoint_9_77_flag endpoint_9_77_sources 0 2 2 223458957748994753 223458957748994753 223458957748994753 endpoint_9_77_w0 endpoint_9_77_w2
private theorem endpoint_9_77_w4 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 4 2 223458957748994753 = some 223458957748994753 := by decide +kernel
private theorem endpoint_9_77_p6 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 6 223458957748994753 = some 223458957748994753 :=
  join_receipt_window endpoint_9_77_flag endpoint_9_77_sources 0 4 2 223458957748994753 223458957748994753 223458957748994753 endpoint_9_77_p4 endpoint_9_77_w4
private theorem endpoint_9_77_w6 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 6 2 223458957748994753 = some 223458957748994753 := by decide +kernel
private theorem endpoint_9_77_p8 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 8 223458957748994753 = some 223458957748994753 :=
  join_receipt_window endpoint_9_77_flag endpoint_9_77_sources 0 6 2 223458957748994753 223458957748994753 223458957748994753 endpoint_9_77_p6 endpoint_9_77_w6
def endpoint_9_77 : CertifiedEndpoint :=
  ⟨⟨9, 77, 2387⟩, 223458957748994753, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_9_77_flag endpoint_9_77_sources 8 223458957748994753 223458957748994753 rfl endpoint_9_77_base endpoint_9_77_p8) (by decide)⟩
private def endpoint_9_78_flag : Flag := ⟨9, 78, 2289⟩
private def endpoint_9_78_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_9_78_base : receiptBase endpoint_9_78_flag endpoint_9_78_sources = some 216862509446027822 := by decide +kernel
private theorem endpoint_9_78_w0 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 2 216862509446027822 = some 216862509446027822 := by decide +kernel
private theorem endpoint_9_78_w2 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 2 2 216862509446027822 = some 216862509446027822 := by decide +kernel
private theorem endpoint_9_78_p4 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 4 216862509446027822 = some 216862509446027822 :=
  join_receipt_window endpoint_9_78_flag endpoint_9_78_sources 0 2 2 216862509446027822 216862509446027822 216862509446027822 endpoint_9_78_w0 endpoint_9_78_w2
private theorem endpoint_9_78_w4 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 4 2 216862509446027822 = some 216862509446027822 := by decide +kernel
private theorem endpoint_9_78_p6 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 6 216862509446027822 = some 216862509446027822 :=
  join_receipt_window endpoint_9_78_flag endpoint_9_78_sources 0 4 2 216862509446027822 216862509446027822 216862509446027822 endpoint_9_78_p4 endpoint_9_78_w4
private theorem endpoint_9_78_w6 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 6 2 216862509446027822 = some 216862509446027822 := by decide +kernel
private theorem endpoint_9_78_p8 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 8 216862509446027822 = some 216862509446027822 :=
  join_receipt_window endpoint_9_78_flag endpoint_9_78_sources 0 6 2 216862509446027822 216862509446027822 216862509446027822 endpoint_9_78_p6 endpoint_9_78_w6
def endpoint_9_78 : CertifiedEndpoint :=
  ⟨⟨9, 78, 2289⟩, 216862509446027822, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_9_78_flag endpoint_9_78_sources 8 216862509446027822 216862509446027822 rfl endpoint_9_78_base endpoint_9_78_p8) (by decide)⟩
private def endpoint_9_79_flag : Flag := ⟨9, 79, 2188⟩
private def endpoint_9_79_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_9_79_base : receiptBase endpoint_9_79_flag endpoint_9_79_sources = some 211869485839032361 := by decide +kernel
private theorem endpoint_9_79_w0 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 2 211869485839032361 = some 211869485839032361 := by decide +kernel
private theorem endpoint_9_79_w2 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 2 2 211869485839032361 = some 211869485839032361 := by decide +kernel
private theorem endpoint_9_79_p4 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 4 211869485839032361 = some 211869485839032361 :=
  join_receipt_window endpoint_9_79_flag endpoint_9_79_sources 0 2 2 211869485839032361 211869485839032361 211869485839032361 endpoint_9_79_w0 endpoint_9_79_w2
private theorem endpoint_9_79_w4 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 4 2 211869485839032361 = some 211869485839032361 := by decide +kernel
private theorem endpoint_9_79_p6 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 6 211869485839032361 = some 211869485839032361 :=
  join_receipt_window endpoint_9_79_flag endpoint_9_79_sources 0 4 2 211869485839032361 211869485839032361 211869485839032361 endpoint_9_79_p4 endpoint_9_79_w4
private theorem endpoint_9_79_w6 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 6 2 211869485839032361 = some 211869485839032361 := by decide +kernel
private theorem endpoint_9_79_p8 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 8 211869485839032361 = some 211869485839032361 :=
  join_receipt_window endpoint_9_79_flag endpoint_9_79_sources 0 6 2 211869485839032361 211869485839032361 211869485839032361 endpoint_9_79_p6 endpoint_9_79_w6
def endpoint_9_79 : CertifiedEndpoint :=
  ⟨⟨9, 79, 2188⟩, 211869485839032361, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_9_79_flag endpoint_9_79_sources 8 211869485839032361 211869485839032361 rfl endpoint_9_79_base endpoint_9_79_p8) (by decide)⟩
private def endpoint_9_80_flag : Flag := ⟨9, 80, 2084⟩
private def endpoint_9_80_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_80_base : receiptBase endpoint_9_80_flag endpoint_9_80_sources = some 206289452122307191 := by decide +kernel
private theorem endpoint_9_80_w0 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 2 206289452122307191 = some 206289452122307191 := by decide +kernel
private theorem endpoint_9_80_w2 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 2 2 206289452122307191 = some 206289452122307191 := by decide +kernel
private theorem endpoint_9_80_p4 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 4 206289452122307191 = some 206289452122307191 :=
  join_receipt_window endpoint_9_80_flag endpoint_9_80_sources 0 2 2 206289452122307191 206289452122307191 206289452122307191 endpoint_9_80_w0 endpoint_9_80_w2
private theorem endpoint_9_80_w4 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 4 2 206289452122307191 = some 206289452122307191 := by decide +kernel
private theorem endpoint_9_80_p6 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 6 206289452122307191 = some 206289452122307191 :=
  join_receipt_window endpoint_9_80_flag endpoint_9_80_sources 0 4 2 206289452122307191 206289452122307191 206289452122307191 endpoint_9_80_p4 endpoint_9_80_w4
private theorem endpoint_9_80_w6 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 6 2 206289452122307191 = some 206289452122307191 := by decide +kernel
private theorem endpoint_9_80_p8 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 8 206289452122307191 = some 206289452122307191 :=
  join_receipt_window endpoint_9_80_flag endpoint_9_80_sources 0 6 2 206289452122307191 206289452122307191 206289452122307191 endpoint_9_80_p6 endpoint_9_80_w6
def endpoint_9_80 : CertifiedEndpoint :=
  ⟨⟨9, 80, 2084⟩, 206289452122307191, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_80_flag endpoint_9_80_sources 8 206289452122307191 206289452122307191 rfl endpoint_9_80_base endpoint_9_80_p8) (by decide)⟩
private def endpoint_9_81_flag : Flag := ⟨9, 81, 1977⟩
private def endpoint_9_81_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_81_base : receiptBase endpoint_9_81_flag endpoint_9_81_sources = some 197958124415875198 := by decide +kernel
private theorem endpoint_9_81_w0 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 2 197958124415875198 = some 197958124415875198 := by decide +kernel
private theorem endpoint_9_81_w2 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 2 2 197958124415875198 = some 197958124415875198 := by decide +kernel
private theorem endpoint_9_81_p4 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 4 197958124415875198 = some 197958124415875198 :=
  join_receipt_window endpoint_9_81_flag endpoint_9_81_sources 0 2 2 197958124415875198 197958124415875198 197958124415875198 endpoint_9_81_w0 endpoint_9_81_w2
private theorem endpoint_9_81_w4 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 4 2 197958124415875198 = some 197958124415875198 := by decide +kernel
private theorem endpoint_9_81_p6 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 6 197958124415875198 = some 197958124415875198 :=
  join_receipt_window endpoint_9_81_flag endpoint_9_81_sources 0 4 2 197958124415875198 197958124415875198 197958124415875198 endpoint_9_81_p4 endpoint_9_81_w4
private theorem endpoint_9_81_w6 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 6 2 197958124415875198 = some 197958124415875198 := by decide +kernel
private theorem endpoint_9_81_p8 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 8 197958124415875198 = some 197958124415875198 :=
  join_receipt_window endpoint_9_81_flag endpoint_9_81_sources 0 6 2 197958124415875198 197958124415875198 197958124415875198 endpoint_9_81_p6 endpoint_9_81_w6
def endpoint_9_81 : CertifiedEndpoint :=
  ⟨⟨9, 81, 1977⟩, 197958124415875198, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_81_flag endpoint_9_81_sources 8 197958124415875198 197958124415875198 rfl endpoint_9_81_base endpoint_9_81_p8) (by decide)⟩
private def endpoint_9_82_flag : Flag := ⟨9, 82, 1867⟩
private def endpoint_9_82_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_82_base : receiptBase endpoint_9_82_flag endpoint_9_82_sources = some 189085840286517430 := by decide +kernel
private theorem endpoint_9_82_w0 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 2 189085840286517430 = some 189085840286517430 := by decide +kernel
private theorem endpoint_9_82_w2 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 2 2 189085840286517430 = some 189085840286517430 := by decide +kernel
private theorem endpoint_9_82_p4 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 4 189085840286517430 = some 189085840286517430 :=
  join_receipt_window endpoint_9_82_flag endpoint_9_82_sources 0 2 2 189085840286517430 189085840286517430 189085840286517430 endpoint_9_82_w0 endpoint_9_82_w2
private theorem endpoint_9_82_w4 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 4 2 189085840286517430 = some 189085840286517430 := by decide +kernel
private theorem endpoint_9_82_p6 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 6 189085840286517430 = some 189085840286517430 :=
  join_receipt_window endpoint_9_82_flag endpoint_9_82_sources 0 4 2 189085840286517430 189085840286517430 189085840286517430 endpoint_9_82_p4 endpoint_9_82_w4
private theorem endpoint_9_82_w6 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 6 2 189085840286517430 = some 189085840286517430 := by decide +kernel
private theorem endpoint_9_82_p8 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 8 189085840286517430 = some 189085840286517430 :=
  join_receipt_window endpoint_9_82_flag endpoint_9_82_sources 0 6 2 189085840286517430 189085840286517430 189085840286517430 endpoint_9_82_p6 endpoint_9_82_w6
def endpoint_9_82 : CertifiedEndpoint :=
  ⟨⟨9, 82, 1867⟩, 189085840286517430, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_82_flag endpoint_9_82_sources 8 189085840286517430 189085840286517430 rfl endpoint_9_82_base endpoint_9_82_p8) (by decide)⟩
private def endpoint_9_83_flag : Flag := ⟨9, 83, 1753⟩
private def endpoint_9_83_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_83_base : receiptBase endpoint_9_83_flag endpoint_9_83_sources = some 179560974488063338 := by decide +kernel
private theorem endpoint_9_83_w0 : receiptWindow endpoint_9_83_flag endpoint_9_83_sources 0 2 179560974488063338 = some 179560974488063338 := by decide +kernel
private theorem endpoint_9_83_w2 : receiptWindow endpoint_9_83_flag endpoint_9_83_sources 2 2 179560974488063338 = some 179560974488063338 := by decide +kernel
private theorem endpoint_9_83_p4 : receiptWindow endpoint_9_83_flag endpoint_9_83_sources 0 4 179560974488063338 = some 179560974488063338 :=
  join_receipt_window endpoint_9_83_flag endpoint_9_83_sources 0 2 2 179560974488063338 179560974488063338 179560974488063338 endpoint_9_83_w0 endpoint_9_83_w2
private theorem endpoint_9_83_w4 : receiptWindow endpoint_9_83_flag endpoint_9_83_sources 4 2 179560974488063338 = some 179560974488063338 := by decide +kernel
private theorem endpoint_9_83_p6 : receiptWindow endpoint_9_83_flag endpoint_9_83_sources 0 6 179560974488063338 = some 179560974488063338 :=
  join_receipt_window endpoint_9_83_flag endpoint_9_83_sources 0 4 2 179560974488063338 179560974488063338 179560974488063338 endpoint_9_83_p4 endpoint_9_83_w4
private theorem endpoint_9_83_w6 : receiptWindow endpoint_9_83_flag endpoint_9_83_sources 6 2 179560974488063338 = some 179560974488063338 := by decide +kernel
private theorem endpoint_9_83_p8 : receiptWindow endpoint_9_83_flag endpoint_9_83_sources 0 8 179560974488063338 = some 179560974488063338 :=
  join_receipt_window endpoint_9_83_flag endpoint_9_83_sources 0 6 2 179560974488063338 179560974488063338 179560974488063338 endpoint_9_83_p6 endpoint_9_83_w6
def endpoint_9_83 : CertifiedEndpoint :=
  ⟨⟨9, 83, 1753⟩, 179560974488063338, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_83_flag endpoint_9_83_sources 8 179560974488063338 179560974488063338 rfl endpoint_9_83_base endpoint_9_83_p8) (by decide)⟩
private def endpoint_9_84_flag : Flag := ⟨9, 84, 1637⟩
private def endpoint_9_84_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_84_base : receiptBase endpoint_9_84_flag endpoint_9_84_sources = some 169575586922780535 := by decide +kernel
private theorem endpoint_9_84_w0 : receiptWindow endpoint_9_84_flag endpoint_9_84_sources 0 2 169575586922780535 = some 169575586922780535 := by decide +kernel
private theorem endpoint_9_84_w2 : receiptWindow endpoint_9_84_flag endpoint_9_84_sources 2 2 169575586922780535 = some 169575586922780535 := by decide +kernel
private theorem endpoint_9_84_p4 : receiptWindow endpoint_9_84_flag endpoint_9_84_sources 0 4 169575586922780535 = some 169575586922780535 :=
  join_receipt_window endpoint_9_84_flag endpoint_9_84_sources 0 2 2 169575586922780535 169575586922780535 169575586922780535 endpoint_9_84_w0 endpoint_9_84_w2
private theorem endpoint_9_84_w4 : receiptWindow endpoint_9_84_flag endpoint_9_84_sources 4 2 169575586922780535 = some 169575586922780535 := by decide +kernel
private theorem endpoint_9_84_p6 : receiptWindow endpoint_9_84_flag endpoint_9_84_sources 0 6 169575586922780535 = some 169575586922780535 :=
  join_receipt_window endpoint_9_84_flag endpoint_9_84_sources 0 4 2 169575586922780535 169575586922780535 169575586922780535 endpoint_9_84_p4 endpoint_9_84_w4
private theorem endpoint_9_84_w6 : receiptWindow endpoint_9_84_flag endpoint_9_84_sources 6 2 169575586922780535 = some 169575586922780535 := by decide +kernel
private theorem endpoint_9_84_p8 : receiptWindow endpoint_9_84_flag endpoint_9_84_sources 0 8 169575586922780535 = some 169575586922780535 :=
  join_receipt_window endpoint_9_84_flag endpoint_9_84_sources 0 6 2 169575586922780535 169575586922780535 169575586922780535 endpoint_9_84_p6 endpoint_9_84_w6
def endpoint_9_84 : CertifiedEndpoint :=
  ⟨⟨9, 84, 1637⟩, 169575586922780535, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_84_flag endpoint_9_84_sources 8 169575586922780535 169575586922780535 rfl endpoint_9_84_base endpoint_9_84_p8) (by decide)⟩
def endpoint_9_85 : CertifiedEndpoint :=
  ⟨⟨9, 85, 1517⟩, 258983182361567690, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_86 : CertifiedEndpoint :=
  ⟨⟨9, 86, 1394⟩, 240220682788847874, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_87 : CertifiedEndpoint :=
  ⟨⟨9, 87, 1268⟩, 220374011572249115, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_88 : CertifiedEndpoint :=
  ⟨⟨9, 88, 1139⟩, 199423377003477371, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_89 : CertifiedEndpoint :=
  ⟨⟨9, 89, 1007⟩, 177348987374238600, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_90 : CertifiedEndpoint :=
  ⟨⟨9, 90, 871⟩, 153944120671759927, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_91 : CertifiedEndpoint :=
  ⟨⟨9, 91, 733⟩, 129560646718005638, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_92 : CertifiedEndpoint :=
  ⟨⟨9, 92, 591⟩, 103802714117024687, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_93 : CertifiedEndpoint :=
  ⟨⟨9, 93, 446⟩, 76837461465001865, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_94 : CertifiedEndpoint :=
  ⟨⟨9, 94, 298⟩, 48645097053643130, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_95 : CertifiedEndpoint :=
  ⟨⟨9, 95, 147⟩, 19205829174654440, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_10 : CertifiedEndpoint :=
  ⟨⟨10, 10, 4951⟩, 71083749224258411, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_11 : CertifiedEndpoint :=
  ⟨⟨10, 11, 4930⟩, 74710683488359180, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_12 : CertifiedEndpoint :=
  ⟨⟨10, 12, 4908⟩, 78288086904368188, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_13 : CertifiedEndpoint :=
  ⟨⟨10, 13, 4887⟩, 89928143918910912, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_14 : CertifiedEndpoint :=
  ⟨⟨10, 14, 4865⟩, 101441667989628075, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_15 : CertifiedEndpoint :=
  ⟨⟨10, 15, 4843⟩, 112844636824058688, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_16 : CertifiedEndpoint :=
  ⟨⟨10, 16, 4820⟩, 124111245582549380, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_17 : CertifiedEndpoint :=
  ⟨⟨10, 17, 4798⟩, 135290647161378303, .intrinsic (by decide +kernel) (by decide)⟩

def endpointBlock06 : List CertifiedEndpoint := [
  endpoint_8_68, endpoint_8_69, endpoint_8_70, endpoint_8_71, endpoint_8_72, endpoint_8_73, endpoint_8_74,
  endpoint_8_75, endpoint_8_76, endpoint_8_77, endpoint_8_78, endpoint_8_79, endpoint_8_80, endpoint_8_81,
  endpoint_8_82, endpoint_8_83, endpoint_8_84, endpoint_8_85, endpoint_8_86, endpoint_8_87, endpoint_8_88,
  endpoint_8_89, endpoint_8_90, endpoint_8_91, endpoint_8_92, endpoint_8_93, endpoint_8_94, endpoint_8_95,
  endpoint_8_96, endpoint_9_9, endpoint_9_10, endpoint_9_11, endpoint_9_12, endpoint_9_13, endpoint_9_14,
  endpoint_9_15, endpoint_9_16, endpoint_9_17, endpoint_9_18, endpoint_9_19, endpoint_9_20, endpoint_9_21,
  endpoint_9_22, endpoint_9_23, endpoint_9_24, endpoint_9_25, endpoint_9_26, endpoint_9_27, endpoint_9_28,
  endpoint_9_29, endpoint_9_30, endpoint_9_31, endpoint_9_32, endpoint_9_33, endpoint_9_34, endpoint_9_35,
  endpoint_9_36, endpoint_9_37, endpoint_9_38, endpoint_9_39, endpoint_9_40, endpoint_9_41, endpoint_9_42,
  endpoint_9_43, endpoint_9_44, endpoint_9_45, endpoint_9_46, endpoint_9_47, endpoint_9_48, endpoint_9_49,
  endpoint_9_50, endpoint_9_51, endpoint_9_52, endpoint_9_53, endpoint_9_54, endpoint_9_55, endpoint_9_56,
  endpoint_9_57, endpoint_9_58, endpoint_9_59, endpoint_9_60, endpoint_9_61, endpoint_9_62, endpoint_9_63,
  endpoint_9_64, endpoint_9_65, endpoint_9_66, endpoint_9_67, endpoint_9_68, endpoint_9_69, endpoint_9_70,
  endpoint_9_71, endpoint_9_72, endpoint_9_73, endpoint_9_74, endpoint_9_75, endpoint_9_76, endpoint_9_77,
  endpoint_9_78, endpoint_9_79, endpoint_9_80, endpoint_9_81, endpoint_9_82, endpoint_9_83, endpoint_9_84,
  endpoint_9_85, endpoint_9_86, endpoint_9_87, endpoint_9_88, endpoint_9_89, endpoint_9_90, endpoint_9_91,
  endpoint_9_92, endpoint_9_93, endpoint_9_94, endpoint_9_95, endpoint_10_10, endpoint_10_11, endpoint_10_12,
  endpoint_10_13, endpoint_10_14, endpoint_10_15, endpoint_10_16, endpoint_10_17
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
