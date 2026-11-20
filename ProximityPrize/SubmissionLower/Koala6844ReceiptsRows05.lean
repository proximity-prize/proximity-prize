import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


private def endpoint_9_66_flag : Flag := ⟨9, 66, 2846⟩
private def endpoint_9_66_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_9_66_base : receiptBase endpoint_9_66_flag endpoint_9_66_sources = some 220837329365240501 := by decide +kernel
private theorem endpoint_9_66_window_0 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 2 220837329365240501 = some 220837329365240501 := by decide +kernel
private theorem endpoint_9_66_window_2 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 2 2 220837329365240501 = some 220837329365240501 := by decide +kernel
private theorem endpoint_9_66_prefix_4 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 4 220837329365240501 = some 220837329365240501 :=
  join_receipt_window endpoint_9_66_flag endpoint_9_66_sources 0 2 2 220837329365240501 220837329365240501 220837329365240501 endpoint_9_66_window_0 endpoint_9_66_window_2
private theorem endpoint_9_66_window_4 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 4 2 220837329365240501 = some 220837329365240501 := by decide +kernel
private theorem endpoint_9_66_prefix_6 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 6 220837329365240501 = some 220837329365240501 :=
  join_receipt_window endpoint_9_66_flag endpoint_9_66_sources 0 4 2 220837329365240501 220837329365240501 220837329365240501 endpoint_9_66_prefix_4 endpoint_9_66_window_4
private theorem endpoint_9_66_window_6 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 6 2 220837329365240501 = some 220837329365240501 := by decide +kernel
private theorem endpoint_9_66_prefix_8 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 8 220837329365240501 = some 220837329365240501 :=
  join_receipt_window endpoint_9_66_flag endpoint_9_66_sources 0 6 2 220837329365240501 220837329365240501 220837329365240501 endpoint_9_66_prefix_6 endpoint_9_66_window_6

def endpoint_9_66 : CertifiedEndpoint :=
  ⟨⟨9, 66, 2846⟩, 220837329365240501, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_9_66_flag endpoint_9_66_sources 8 220837329365240501 220837329365240501 rfl endpoint_9_66_base endpoint_9_66_prefix_8) (by decide)⟩
private def endpoint_9_67_flag : Flag := ⟨9, 67, 2790⟩
private def endpoint_9_67_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_9_67_base : receiptBase endpoint_9_67_flag endpoint_9_67_sources = some 219440703156587646 := by decide +kernel
private theorem endpoint_9_67_window_0 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 2 219440703156587646 = some 219440703156587646 := by decide +kernel
private theorem endpoint_9_67_window_2 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 2 2 219440703156587646 = some 219440703156587646 := by decide +kernel
private theorem endpoint_9_67_prefix_4 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 4 219440703156587646 = some 219440703156587646 :=
  join_receipt_window endpoint_9_67_flag endpoint_9_67_sources 0 2 2 219440703156587646 219440703156587646 219440703156587646 endpoint_9_67_window_0 endpoint_9_67_window_2
private theorem endpoint_9_67_window_4 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 4 2 219440703156587646 = some 219440703156587646 := by decide +kernel
private theorem endpoint_9_67_prefix_6 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 6 219440703156587646 = some 219440703156587646 :=
  join_receipt_window endpoint_9_67_flag endpoint_9_67_sources 0 4 2 219440703156587646 219440703156587646 219440703156587646 endpoint_9_67_prefix_4 endpoint_9_67_window_4
private theorem endpoint_9_67_window_6 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 6 2 219440703156587646 = some 219440703156587646 := by decide +kernel
private theorem endpoint_9_67_prefix_8 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 8 219440703156587646 = some 219440703156587646 :=
  join_receipt_window endpoint_9_67_flag endpoint_9_67_sources 0 6 2 219440703156587646 219440703156587646 219440703156587646 endpoint_9_67_prefix_6 endpoint_9_67_window_6

def endpoint_9_67 : CertifiedEndpoint :=
  ⟨⟨9, 67, 2790⟩, 219440703156587646, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_9_67_flag endpoint_9_67_sources 8 219440703156587646 219440703156587646 rfl endpoint_9_67_base endpoint_9_67_prefix_8) (by decide)⟩
private def endpoint_9_68_flag : Flag := ⟨9, 68, 2732⟩
private def endpoint_9_68_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_9_68_base : receiptBase endpoint_9_68_flag endpoint_9_68_sources = some 219098537370743316 := by decide +kernel
private theorem endpoint_9_68_window_0 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 2 219098537370743316 = some 219098537370743316 := by decide +kernel
private theorem endpoint_9_68_window_2 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 2 2 219098537370743316 = some 219098537370743316 := by decide +kernel
private theorem endpoint_9_68_prefix_4 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 4 219098537370743316 = some 219098537370743316 :=
  join_receipt_window endpoint_9_68_flag endpoint_9_68_sources 0 2 2 219098537370743316 219098537370743316 219098537370743316 endpoint_9_68_window_0 endpoint_9_68_window_2
private theorem endpoint_9_68_window_4 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 4 2 219098537370743316 = some 219098537370743316 := by decide +kernel
private theorem endpoint_9_68_prefix_6 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 6 219098537370743316 = some 219098537370743316 :=
  join_receipt_window endpoint_9_68_flag endpoint_9_68_sources 0 4 2 219098537370743316 219098537370743316 219098537370743316 endpoint_9_68_prefix_4 endpoint_9_68_window_4
private theorem endpoint_9_68_window_6 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 6 2 219098537370743316 = some 219098537370743316 := by decide +kernel
private theorem endpoint_9_68_prefix_8 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 8 219098537370743316 = some 219098537370743316 :=
  join_receipt_window endpoint_9_68_flag endpoint_9_68_sources 0 6 2 219098537370743316 219098537370743316 219098537370743316 endpoint_9_68_prefix_6 endpoint_9_68_window_6

def endpoint_9_68 : CertifiedEndpoint :=
  ⟨⟨9, 68, 2732⟩, 219098537370743316, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_9_68_flag endpoint_9_68_sources 8 219098537370743316 219098537370743316 rfl endpoint_9_68_base endpoint_9_68_prefix_8) (by decide)⟩
private def endpoint_9_69_flag : Flag := ⟨9, 69, 2671⟩
private def endpoint_9_69_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_9_69_base : receiptBase endpoint_9_69_flag endpoint_9_69_sources = some 218408253585689114 := by decide +kernel
private theorem endpoint_9_69_window_0 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 2 218408253585689114 = some 218408253585689114 := by decide +kernel
private theorem endpoint_9_69_window_2 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 2 2 218408253585689114 = some 218408253585689114 := by decide +kernel
private theorem endpoint_9_69_prefix_4 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 4 218408253585689114 = some 218408253585689114 :=
  join_receipt_window endpoint_9_69_flag endpoint_9_69_sources 0 2 2 218408253585689114 218408253585689114 218408253585689114 endpoint_9_69_window_0 endpoint_9_69_window_2
private theorem endpoint_9_69_window_4 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 4 2 218408253585689114 = some 218408253585689114 := by decide +kernel
private theorem endpoint_9_69_prefix_6 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 6 218408253585689114 = some 218408253585689114 :=
  join_receipt_window endpoint_9_69_flag endpoint_9_69_sources 0 4 2 218408253585689114 218408253585689114 218408253585689114 endpoint_9_69_prefix_4 endpoint_9_69_window_4
private theorem endpoint_9_69_window_6 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 6 2 218408253585689114 = some 218408253585689114 := by decide +kernel
private theorem endpoint_9_69_prefix_8 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 8 218408253585689114 = some 218408253585689114 :=
  join_receipt_window endpoint_9_69_flag endpoint_9_69_sources 0 6 2 218408253585689114 218408253585689114 218408253585689114 endpoint_9_69_prefix_6 endpoint_9_69_window_6

def endpoint_9_69 : CertifiedEndpoint :=
  ⟨⟨9, 69, 2671⟩, 218408253585689114, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_9_69_flag endpoint_9_69_sources 8 218408253585689114 218408253585689114 rfl endpoint_9_69_base endpoint_9_69_prefix_8) (by decide)⟩
private def endpoint_9_70_flag : Flag := ⟨9, 70, 2607⟩
private def endpoint_9_70_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_9_70_base : receiptBase endpoint_9_70_flag endpoint_9_70_sources = some 217214297625256046 := by decide +kernel
private theorem endpoint_9_70_window_0 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 2 217214297625256046 = some 217214297625256046 := by decide +kernel
private theorem endpoint_9_70_window_2 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 2 2 217214297625256046 = some 217214297625256046 := by decide +kernel
private theorem endpoint_9_70_prefix_4 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 4 217214297625256046 = some 217214297625256046 :=
  join_receipt_window endpoint_9_70_flag endpoint_9_70_sources 0 2 2 217214297625256046 217214297625256046 217214297625256046 endpoint_9_70_window_0 endpoint_9_70_window_2
private theorem endpoint_9_70_window_4 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 4 2 217214297625256046 = some 217214297625256046 := by decide +kernel
private theorem endpoint_9_70_prefix_6 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 6 217214297625256046 = some 217214297625256046 :=
  join_receipt_window endpoint_9_70_flag endpoint_9_70_sources 0 4 2 217214297625256046 217214297625256046 217214297625256046 endpoint_9_70_prefix_4 endpoint_9_70_window_4
private theorem endpoint_9_70_window_6 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 6 2 217214297625256046 = some 217214297625256046 := by decide +kernel
private theorem endpoint_9_70_prefix_8 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 8 217214297625256046 = some 217214297625256046 :=
  join_receipt_window endpoint_9_70_flag endpoint_9_70_sources 0 6 2 217214297625256046 217214297625256046 217214297625256046 endpoint_9_70_prefix_6 endpoint_9_70_window_6

def endpoint_9_70 : CertifiedEndpoint :=
  ⟨⟨9, 70, 2607⟩, 217214297625256046, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_9_70_flag endpoint_9_70_sources 8 217214297625256046 217214297625256046 rfl endpoint_9_70_base endpoint_9_70_prefix_8) (by decide)⟩
private def endpoint_9_71_flag : Flag := ⟨9, 71, 2541⟩
private def endpoint_9_71_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_9_71_base : receiptBase endpoint_9_71_flag endpoint_9_71_sources = some 214466887069740073 := by decide +kernel
private theorem endpoint_9_71_window_0 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 2 214466887069740073 = some 214466887069740073 := by decide +kernel
private theorem endpoint_9_71_window_2 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 2 2 214466887069740073 = some 214466887069740073 := by decide +kernel
private theorem endpoint_9_71_prefix_4 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 4 214466887069740073 = some 214466887069740073 :=
  join_receipt_window endpoint_9_71_flag endpoint_9_71_sources 0 2 2 214466887069740073 214466887069740073 214466887069740073 endpoint_9_71_window_0 endpoint_9_71_window_2
private theorem endpoint_9_71_window_4 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 4 2 214466887069740073 = some 214466887069740073 := by decide +kernel
private theorem endpoint_9_71_prefix_6 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 6 214466887069740073 = some 214466887069740073 :=
  join_receipt_window endpoint_9_71_flag endpoint_9_71_sources 0 4 2 214466887069740073 214466887069740073 214466887069740073 endpoint_9_71_prefix_4 endpoint_9_71_window_4
private theorem endpoint_9_71_window_6 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 6 2 214466887069740073 = some 214466887069740073 := by decide +kernel
private theorem endpoint_9_71_prefix_8 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 8 214466887069740073 = some 214466887069740073 :=
  join_receipt_window endpoint_9_71_flag endpoint_9_71_sources 0 6 2 214466887069740073 214466887069740073 214466887069740073 endpoint_9_71_prefix_6 endpoint_9_71_window_6

def endpoint_9_71 : CertifiedEndpoint :=
  ⟨⟨9, 71, 2541⟩, 214466887069740073, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_9_71_flag endpoint_9_71_sources 8 214466887069740073 214466887069740073 rfl endpoint_9_71_base endpoint_9_71_prefix_8) (by decide)⟩
private def endpoint_9_72_flag : Flag := ⟨9, 72, 2472⟩
private def endpoint_9_72_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_9_72_base : receiptBase endpoint_9_72_flag endpoint_9_72_sources = some 211323839415567049 := by decide +kernel
private theorem endpoint_9_72_window_0 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 2 211323839415567049 = some 211323839415567049 := by decide +kernel
private theorem endpoint_9_72_window_2 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 2 2 211323839415567049 = some 211323839415567049 := by decide +kernel
private theorem endpoint_9_72_prefix_4 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 4 211323839415567049 = some 211323839415567049 :=
  join_receipt_window endpoint_9_72_flag endpoint_9_72_sources 0 2 2 211323839415567049 211323839415567049 211323839415567049 endpoint_9_72_window_0 endpoint_9_72_window_2
private theorem endpoint_9_72_window_4 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 4 2 211323839415567049 = some 211323839415567049 := by decide +kernel
private theorem endpoint_9_72_prefix_6 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 6 211323839415567049 = some 211323839415567049 :=
  join_receipt_window endpoint_9_72_flag endpoint_9_72_sources 0 4 2 211323839415567049 211323839415567049 211323839415567049 endpoint_9_72_prefix_4 endpoint_9_72_window_4
private theorem endpoint_9_72_window_6 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 6 2 211323839415567049 = some 211323839415567049 := by decide +kernel
private theorem endpoint_9_72_prefix_8 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 8 211323839415567049 = some 211323839415567049 :=
  join_receipt_window endpoint_9_72_flag endpoint_9_72_sources 0 6 2 211323839415567049 211323839415567049 211323839415567049 endpoint_9_72_prefix_6 endpoint_9_72_window_6

def endpoint_9_72 : CertifiedEndpoint :=
  ⟨⟨9, 72, 2472⟩, 211323839415567049, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_9_72_flag endpoint_9_72_sources 8 211323839415567049 211323839415567049 rfl endpoint_9_72_base endpoint_9_72_prefix_8) (by decide)⟩
private def endpoint_9_73_flag : Flag := ⟨9, 73, 2400⟩
private def endpoint_9_73_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_9_73_base : receiptBase endpoint_9_73_flag endpoint_9_73_sources = some 212117908954972679 := by decide +kernel
private theorem endpoint_9_73_window_0 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 2 212117908954972679 = some 212117908954972679 := by decide +kernel
private theorem endpoint_9_73_window_2 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 2 2 212117908954972679 = some 212117908954972679 := by decide +kernel
private theorem endpoint_9_73_prefix_4 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 4 212117908954972679 = some 212117908954972679 :=
  join_receipt_window endpoint_9_73_flag endpoint_9_73_sources 0 2 2 212117908954972679 212117908954972679 212117908954972679 endpoint_9_73_window_0 endpoint_9_73_window_2
private theorem endpoint_9_73_window_4 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 4 2 212117908954972679 = some 212117908954972679 := by decide +kernel
private theorem endpoint_9_73_prefix_6 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 6 212117908954972679 = some 212117908954972679 :=
  join_receipt_window endpoint_9_73_flag endpoint_9_73_sources 0 4 2 212117908954972679 212117908954972679 212117908954972679 endpoint_9_73_prefix_4 endpoint_9_73_window_4
private theorem endpoint_9_73_window_6 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 6 2 212117908954972679 = some 212117908954972679 := by decide +kernel
private theorem endpoint_9_73_prefix_8 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 8 212117908954972679 = some 212117908954972679 :=
  join_receipt_window endpoint_9_73_flag endpoint_9_73_sources 0 6 2 212117908954972679 212117908954972679 212117908954972679 endpoint_9_73_prefix_6 endpoint_9_73_window_6

def endpoint_9_73 : CertifiedEndpoint :=
  ⟨⟨9, 73, 2400⟩, 212117908954972679, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_9_73_flag endpoint_9_73_sources 8 212117908954972679 212117908954972679 rfl endpoint_9_73_base endpoint_9_73_prefix_8) (by decide)⟩
private def endpoint_9_74_flag : Flag := ⟨9, 74, 2326⟩
private def endpoint_9_74_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_9_74_base : receiptBase endpoint_9_74_flag endpoint_9_74_sources = some 208207574437036509 := by decide +kernel
private theorem endpoint_9_74_window_0 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 2 208207574437036509 = some 208207574437036509 := by decide +kernel
private theorem endpoint_9_74_window_2 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 2 2 208207574437036509 = some 208207574437036509 := by decide +kernel
private theorem endpoint_9_74_prefix_4 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 4 208207574437036509 = some 208207574437036509 :=
  join_receipt_window endpoint_9_74_flag endpoint_9_74_sources 0 2 2 208207574437036509 208207574437036509 208207574437036509 endpoint_9_74_window_0 endpoint_9_74_window_2
private theorem endpoint_9_74_window_4 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 4 2 208207574437036509 = some 208207574437036509 := by decide +kernel
private theorem endpoint_9_74_prefix_6 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 6 208207574437036509 = some 208207574437036509 :=
  join_receipt_window endpoint_9_74_flag endpoint_9_74_sources 0 4 2 208207574437036509 208207574437036509 208207574437036509 endpoint_9_74_prefix_4 endpoint_9_74_window_4
private theorem endpoint_9_74_window_6 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 6 2 208207574437036509 = some 208207574437036509 := by decide +kernel
private theorem endpoint_9_74_prefix_8 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 8 208207574437036509 = some 208207574437036509 :=
  join_receipt_window endpoint_9_74_flag endpoint_9_74_sources 0 6 2 208207574437036509 208207574437036509 208207574437036509 endpoint_9_74_prefix_6 endpoint_9_74_window_6

def endpoint_9_74 : CertifiedEndpoint :=
  ⟨⟨9, 74, 2326⟩, 208207574437036509, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_9_74_flag endpoint_9_74_sources 8 208207574437036509 208207574437036509 rfl endpoint_9_74_base endpoint_9_74_prefix_8) (by decide)⟩
private def endpoint_9_75_flag : Flag := ⟨9, 75, 2248⟩
private def endpoint_9_75_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_9_75_base : receiptBase endpoint_9_75_flag endpoint_9_75_sources = some 203782947403644794 := by decide +kernel
private theorem endpoint_9_75_window_0 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 2 203782947403644794 = some 203782947403644794 := by decide +kernel
private theorem endpoint_9_75_window_2 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 2 2 203782947403644794 = some 203782947403644794 := by decide +kernel
private theorem endpoint_9_75_prefix_4 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 4 203782947403644794 = some 203782947403644794 :=
  join_receipt_window endpoint_9_75_flag endpoint_9_75_sources 0 2 2 203782947403644794 203782947403644794 203782947403644794 endpoint_9_75_window_0 endpoint_9_75_window_2
private theorem endpoint_9_75_window_4 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 4 2 203782947403644794 = some 203782947403644794 := by decide +kernel
private theorem endpoint_9_75_prefix_6 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 6 203782947403644794 = some 203782947403644794 :=
  join_receipt_window endpoint_9_75_flag endpoint_9_75_sources 0 4 2 203782947403644794 203782947403644794 203782947403644794 endpoint_9_75_prefix_4 endpoint_9_75_window_4
private theorem endpoint_9_75_window_6 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 6 2 203782947403644794 = some 203782947403644794 := by decide +kernel
private theorem endpoint_9_75_prefix_8 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 8 203782947403644794 = some 203782947403644794 :=
  join_receipt_window endpoint_9_75_flag endpoint_9_75_sources 0 6 2 203782947403644794 203782947403644794 203782947403644794 endpoint_9_75_prefix_6 endpoint_9_75_window_6

def endpoint_9_75 : CertifiedEndpoint :=
  ⟨⟨9, 75, 2248⟩, 203782947403644794, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_9_75_flag endpoint_9_75_sources 8 203782947403644794 203782947403644794 rfl endpoint_9_75_base endpoint_9_75_prefix_8) (by decide)⟩
private def endpoint_9_76_flag : Flag := ⟨9, 76, 2169⟩
private def endpoint_9_76_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_9_76_base : receiptBase endpoint_9_76_flag endpoint_9_76_sources = some 200835511710029401 := by decide +kernel
private theorem endpoint_9_76_window_0 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 2 200835511710029401 = some 200835511710029401 := by decide +kernel
private theorem endpoint_9_76_window_2 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 2 2 200835511710029401 = some 200835511710029401 := by decide +kernel
private theorem endpoint_9_76_prefix_4 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 4 200835511710029401 = some 200835511710029401 :=
  join_receipt_window endpoint_9_76_flag endpoint_9_76_sources 0 2 2 200835511710029401 200835511710029401 200835511710029401 endpoint_9_76_window_0 endpoint_9_76_window_2
private theorem endpoint_9_76_window_4 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 4 2 200835511710029401 = some 200835511710029401 := by decide +kernel
private theorem endpoint_9_76_prefix_6 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 6 200835511710029401 = some 200835511710029401 :=
  join_receipt_window endpoint_9_76_flag endpoint_9_76_sources 0 4 2 200835511710029401 200835511710029401 200835511710029401 endpoint_9_76_prefix_4 endpoint_9_76_window_4
private theorem endpoint_9_76_window_6 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 6 2 200835511710029401 = some 200835511710029401 := by decide +kernel
private theorem endpoint_9_76_prefix_8 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 8 200835511710029401 = some 200835511710029401 :=
  join_receipt_window endpoint_9_76_flag endpoint_9_76_sources 0 6 2 200835511710029401 200835511710029401 200835511710029401 endpoint_9_76_prefix_6 endpoint_9_76_window_6

def endpoint_9_76 : CertifiedEndpoint :=
  ⟨⟨9, 76, 2169⟩, 200835511710029401, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_9_76_flag endpoint_9_76_sources 8 200835511710029401 200835511710029401 rfl endpoint_9_76_base endpoint_9_76_prefix_8) (by decide)⟩
private def endpoint_9_77_flag : Flag := ⟨9, 77, 2086⟩
private def endpoint_9_77_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_9_77_base : receiptBase endpoint_9_77_flag endpoint_9_77_sources = some 195497430340903989 := by decide +kernel
private theorem endpoint_9_77_window_0 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 2 195497430340903989 = some 195497430340903989 := by decide +kernel
private theorem endpoint_9_77_window_2 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 2 2 195497430340903989 = some 195497430340903989 := by decide +kernel
private theorem endpoint_9_77_prefix_4 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 4 195497430340903989 = some 195497430340903989 :=
  join_receipt_window endpoint_9_77_flag endpoint_9_77_sources 0 2 2 195497430340903989 195497430340903989 195497430340903989 endpoint_9_77_window_0 endpoint_9_77_window_2
private theorem endpoint_9_77_window_4 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 4 2 195497430340903989 = some 195497430340903989 := by decide +kernel
private theorem endpoint_9_77_prefix_6 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 6 195497430340903989 = some 195497430340903989 :=
  join_receipt_window endpoint_9_77_flag endpoint_9_77_sources 0 4 2 195497430340903989 195497430340903989 195497430340903989 endpoint_9_77_prefix_4 endpoint_9_77_window_4
private theorem endpoint_9_77_window_6 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 6 2 195497430340903989 = some 195497430340903989 := by decide +kernel
private theorem endpoint_9_77_prefix_8 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 8 195497430340903989 = some 195497430340903989 :=
  join_receipt_window endpoint_9_77_flag endpoint_9_77_sources 0 6 2 195497430340903989 195497430340903989 195497430340903989 endpoint_9_77_prefix_6 endpoint_9_77_window_6

def endpoint_9_77 : CertifiedEndpoint :=
  ⟨⟨9, 77, 2086⟩, 195497430340903989, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_9_77_flag endpoint_9_77_sources 8 195497430340903989 195497430340903989 rfl endpoint_9_77_base endpoint_9_77_prefix_8) (by decide)⟩
private def endpoint_9_78_flag : Flag := ⟨9, 78, 2001⟩
private def endpoint_9_78_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_9_78_base : receiptBase endpoint_9_78_flag endpoint_9_78_sources = some 189791269446430391 := by decide +kernel
private theorem endpoint_9_78_window_0 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 2 189791269446430391 = some 189791269446430391 := by decide +kernel
private theorem endpoint_9_78_window_2 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 2 2 189791269446430391 = some 189791269446430391 := by decide +kernel
private theorem endpoint_9_78_prefix_4 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 4 189791269446430391 = some 189791269446430391 :=
  join_receipt_window endpoint_9_78_flag endpoint_9_78_sources 0 2 2 189791269446430391 189791269446430391 189791269446430391 endpoint_9_78_window_0 endpoint_9_78_window_2
private theorem endpoint_9_78_window_4 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 4 2 189791269446430391 = some 189791269446430391 := by decide +kernel
private theorem endpoint_9_78_prefix_6 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 6 189791269446430391 = some 189791269446430391 :=
  join_receipt_window endpoint_9_78_flag endpoint_9_78_sources 0 4 2 189791269446430391 189791269446430391 189791269446430391 endpoint_9_78_prefix_4 endpoint_9_78_window_4
private theorem endpoint_9_78_window_6 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 6 2 189791269446430391 = some 189791269446430391 := by decide +kernel
private theorem endpoint_9_78_prefix_8 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 8 189791269446430391 = some 189791269446430391 :=
  join_receipt_window endpoint_9_78_flag endpoint_9_78_sources 0 6 2 189791269446430391 189791269446430391 189791269446430391 endpoint_9_78_prefix_6 endpoint_9_78_window_6

def endpoint_9_78 : CertifiedEndpoint :=
  ⟨⟨9, 78, 2001⟩, 189791269446430391, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_9_78_flag endpoint_9_78_sources 8 189791269446430391 189791269446430391 rfl endpoint_9_78_base endpoint_9_78_prefix_8) (by decide)⟩
private def endpoint_9_79_flag : Flag := ⟨9, 79, 1913⟩
private def endpoint_9_79_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_9_79_base : receiptBase endpoint_9_79_flag endpoint_9_79_sources = some 185419971855024149 := by decide +kernel
private theorem endpoint_9_79_window_0 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 2 185419971855024149 = some 185419971855024149 := by decide +kernel
private theorem endpoint_9_79_window_2 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 2 2 185419971855024149 = some 185419971855024149 := by decide +kernel
private theorem endpoint_9_79_prefix_4 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 4 185419971855024149 = some 185419971855024149 :=
  join_receipt_window endpoint_9_79_flag endpoint_9_79_sources 0 2 2 185419971855024149 185419971855024149 185419971855024149 endpoint_9_79_window_0 endpoint_9_79_window_2
private theorem endpoint_9_79_window_4 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 4 2 185419971855024149 = some 185419971855024149 := by decide +kernel
private theorem endpoint_9_79_prefix_6 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 6 185419971855024149 = some 185419971855024149 :=
  join_receipt_window endpoint_9_79_flag endpoint_9_79_sources 0 4 2 185419971855024149 185419971855024149 185419971855024149 endpoint_9_79_prefix_4 endpoint_9_79_window_4
private theorem endpoint_9_79_window_6 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 6 2 185419971855024149 = some 185419971855024149 := by decide +kernel
private theorem endpoint_9_79_prefix_8 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 8 185419971855024149 = some 185419971855024149 :=
  join_receipt_window endpoint_9_79_flag endpoint_9_79_sources 0 6 2 185419971855024149 185419971855024149 185419971855024149 endpoint_9_79_prefix_6 endpoint_9_79_window_6

def endpoint_9_79 : CertifiedEndpoint :=
  ⟨⟨9, 79, 1913⟩, 185419971855024149, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_9_79_flag endpoint_9_79_sources 8 185419971855024149 185419971855024149 rfl endpoint_9_79_base endpoint_9_79_prefix_8) (by decide)⟩
private def endpoint_9_80_flag : Flag := ⟨9, 80, 1823⟩
private def endpoint_9_80_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_80_base : receiptBase endpoint_9_80_flag endpoint_9_80_sources = some 180577663303858695 := by decide +kernel
private theorem endpoint_9_80_window_0 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 2 180577663303858695 = some 180577663303858695 := by decide +kernel
private theorem endpoint_9_80_window_2 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 2 2 180577663303858695 = some 180577663303858695 := by decide +kernel
private theorem endpoint_9_80_prefix_4 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 4 180577663303858695 = some 180577663303858695 :=
  join_receipt_window endpoint_9_80_flag endpoint_9_80_sources 0 2 2 180577663303858695 180577663303858695 180577663303858695 endpoint_9_80_window_0 endpoint_9_80_window_2
private theorem endpoint_9_80_window_4 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 4 2 180577663303858695 = some 180577663303858695 := by decide +kernel
private theorem endpoint_9_80_prefix_6 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 6 180577663303858695 = some 180577663303858695 :=
  join_receipt_window endpoint_9_80_flag endpoint_9_80_sources 0 4 2 180577663303858695 180577663303858695 180577663303858695 endpoint_9_80_prefix_4 endpoint_9_80_window_4
private theorem endpoint_9_80_window_6 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 6 2 180577663303858695 = some 180577663303858695 := by decide +kernel
private theorem endpoint_9_80_prefix_8 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 8 180577663303858695 = some 180577663303858695 :=
  join_receipt_window endpoint_9_80_flag endpoint_9_80_sources 0 6 2 180577663303858695 180577663303858695 180577663303858695 endpoint_9_80_prefix_6 endpoint_9_80_window_6

def endpoint_9_80 : CertifiedEndpoint :=
  ⟨⟨9, 80, 1823⟩, 180577663303858695, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_80_flag endpoint_9_80_sources 8 180577663303858695 180577663303858695 rfl endpoint_9_80_base endpoint_9_80_prefix_8) (by decide)⟩
private def endpoint_9_81_flag : Flag := ⟨9, 81, 1730⟩
private def endpoint_9_81_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_81_base : receiptBase endpoint_9_81_flag endpoint_9_81_sources = some 173345882659566943 := by decide +kernel
private theorem endpoint_9_81_window_0 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 2 173345882659566943 = some 173345882659566943 := by decide +kernel
private theorem endpoint_9_81_window_2 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 2 2 173345882659566943 = some 173345882659566943 := by decide +kernel
private theorem endpoint_9_81_prefix_4 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 4 173345882659566943 = some 173345882659566943 :=
  join_receipt_window endpoint_9_81_flag endpoint_9_81_sources 0 2 2 173345882659566943 173345882659566943 173345882659566943 endpoint_9_81_window_0 endpoint_9_81_window_2
private theorem endpoint_9_81_window_4 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 4 2 173345882659566943 = some 173345882659566943 := by decide +kernel
private theorem endpoint_9_81_prefix_6 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 6 173345882659566943 = some 173345882659566943 :=
  join_receipt_window endpoint_9_81_flag endpoint_9_81_sources 0 4 2 173345882659566943 173345882659566943 173345882659566943 endpoint_9_81_prefix_4 endpoint_9_81_window_4
private theorem endpoint_9_81_window_6 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 6 2 173345882659566943 = some 173345882659566943 := by decide +kernel
private theorem endpoint_9_81_prefix_8 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 8 173345882659566943 = some 173345882659566943 :=
  join_receipt_window endpoint_9_81_flag endpoint_9_81_sources 0 6 2 173345882659566943 173345882659566943 173345882659566943 endpoint_9_81_prefix_6 endpoint_9_81_window_6

def endpoint_9_81 : CertifiedEndpoint :=
  ⟨⟨9, 81, 1730⟩, 173345882659566943, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_81_flag endpoint_9_81_sources 8 173345882659566943 173345882659566943 rfl endpoint_9_81_base endpoint_9_81_prefix_8) (by decide)⟩
private def endpoint_9_82_flag : Flag := ⟨9, 82, 1634⟩
private def endpoint_9_82_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_82_base : receiptBase endpoint_9_82_flag endpoint_9_82_sources = some 165604336183477697 := by decide +kernel
private theorem endpoint_9_82_window_0 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 2 165604336183477697 = some 165604336183477697 := by decide +kernel
private theorem endpoint_9_82_window_2 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 2 2 165604336183477697 = some 165604336183477697 := by decide +kernel
private theorem endpoint_9_82_prefix_4 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 4 165604336183477697 = some 165604336183477697 :=
  join_receipt_window endpoint_9_82_flag endpoint_9_82_sources 0 2 2 165604336183477697 165604336183477697 165604336183477697 endpoint_9_82_window_0 endpoint_9_82_window_2
private theorem endpoint_9_82_window_4 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 4 2 165604336183477697 = some 165604336183477697 := by decide +kernel
private theorem endpoint_9_82_prefix_6 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 6 165604336183477697 = some 165604336183477697 :=
  join_receipt_window endpoint_9_82_flag endpoint_9_82_sources 0 4 2 165604336183477697 165604336183477697 165604336183477697 endpoint_9_82_prefix_4 endpoint_9_82_window_4
private theorem endpoint_9_82_window_6 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 6 2 165604336183477697 = some 165604336183477697 := by decide +kernel
private theorem endpoint_9_82_prefix_8 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 8 165604336183477697 = some 165604336183477697 :=
  join_receipt_window endpoint_9_82_flag endpoint_9_82_sources 0 6 2 165604336183477697 165604336183477697 165604336183477697 endpoint_9_82_prefix_6 endpoint_9_82_window_6

def endpoint_9_82 : CertifiedEndpoint :=
  ⟨⟨9, 82, 1634⟩, 165604336183477697, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_82_flag endpoint_9_82_sources 8 165604336183477697 165604336183477697 rfl endpoint_9_82_base endpoint_9_82_prefix_8) (by decide)⟩
def endpoint_9_83 : CertifiedEndpoint :=
  ⟨⟨9, 83, 1535⟩, 255768284373767388, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_84 : CertifiedEndpoint :=
  ⟨⟨9, 84, 1433⟩, 241239192213010385, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_85 : CertifiedEndpoint :=
  ⟨⟨9, 85, 1329⟩, 225907419096924806, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_86 : CertifiedEndpoint :=
  ⟨⟨9, 86, 1222⟩, 209581636563633142, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_87 : CertifiedEndpoint :=
  ⟨⟨9, 87, 1113⟩, 192422385973222170, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_88 : CertifiedEndpoint :=
  ⟨⟨9, 88, 1001⟩, 174233940706415705, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_89 : CertifiedEndpoint :=
  ⟨⟨9, 89, 885⟩, 154811777829140210, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_90 : CertifiedEndpoint :=
  ⟨⟨9, 90, 768⟩, 134690299310440128, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_91 : CertifiedEndpoint :=
  ⟨⟨9, 91, 647⟩, 113295519764682932, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_92 : CertifiedEndpoint :=
  ⟨⟨9, 92, 524⟩, 90983707171231584, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_93 : CertifiedEndpoint :=
  ⟨⟨9, 93, 398⟩, 67548139517313209, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_94 : CertifiedEndpoint :=
  ⟨⟨9, 94, 269⟩, 42969025094633765, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_95 : CertifiedEndpoint :=
  ⟨⟨9, 95, 137⟩, 17226572194899210, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_10 : CertifiedEndpoint :=
  ⟨⟨10, 10, 4316⟩, 61952487996557676, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_11 : CertifiedEndpoint :=
  ⟨⟨10, 11, 4297⟩, 65102488377353092, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_12 : CertifiedEndpoint :=
  ⟨⟨10, 12, 4278⟩, 68222131154791258, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_13 : CertifiedEndpoint :=
  ⟨⟨10, 13, 4259⟩, 78351283842457484, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_14 : CertifiedEndpoint :=
  ⟨⟨10, 14, 4240⟩, 88384621992008700, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_15 : CertifiedEndpoint :=
  ⟨⟨10, 15, 4221⟩, 98322145603444906, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_16 : CertifiedEndpoint :=
  ⟨⟨10, 16, 4202⟩, 108163854676766102, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_17 : CertifiedEndpoint :=
  ⟨⟨10, 17, 4182⟩, 117881487589290327, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_18 : CertifiedEndpoint :=
  ⟨⟨10, 18, 4163⟩, 127529110803352913, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_19 : CertifiedEndpoint :=
  ⟨⟨10, 19, 4143⟩, 137047744290561348, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_20 : CertifiedEndpoint :=
  ⟨⟨10, 20, 4123⟩, 146465649673597593, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_21 : CertifiedEndpoint :=
  ⟨⟨10, 21, 4102⟩, 155744738197665327, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_22 : CertifiedEndpoint :=
  ⟨⟨10, 22, 4082⟩, 164958730589328602, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_23 : CertifiedEndpoint :=
  ⟨⟨10, 23, 4061⟩, 174028992555966186, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_24 : CertifiedEndpoint :=
  ⟨⟨10, 24, 4040⟩, 182993612852374400, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_25 : CertifiedEndpoint :=
  ⟨⟨10, 25, 4019⟩, 191852591478553244, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_26 : CertifiedEndpoint :=
  ⟨⟨10, 26, 3997⟩, 200555555764563447, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_27 : CertifiedEndpoint :=
  ⟨⟨10, 27, 3976⟩, 209200794267254961, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_28 : CertifiedEndpoint :=
  ⟨⟨10, 28, 3954⟩, 217685104863720654, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_29 : CertifiedEndpoint :=
  ⟨⟨10, 29, 3932⟩, 226058860223899797, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_30 : CertifiedEndpoint :=
  ⟨⟨10, 30, 3909⟩, 234261860545738759, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_31 : CertifiedEndpoint :=
  ⟨⟨10, 31, 3886⟩, 242349392065233991, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_32 : CertifiedEndpoint :=
  ⟨⟨10, 32, 3863⟩, 250321454782385493, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_10_33_flag : Flag := ⟨10, 33, 3840⟩
private def endpoint_10_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_33_base : receiptBase endpoint_10_33_flag endpoint_10_33_sources = some 170804734459825603 := by decide +kernel
private theorem endpoint_10_33_window_0 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 2 170804734459825603 = some 170804734459825603 := by decide +kernel
private theorem endpoint_10_33_window_2 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 2 2 170804734459825603 = some 170804734459825603 := by decide +kernel
private theorem endpoint_10_33_prefix_4 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 4 170804734459825603 = some 170804734459825603 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 2 2 170804734459825603 170804734459825603 170804734459825603 endpoint_10_33_window_0 endpoint_10_33_window_2
private theorem endpoint_10_33_window_4 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 4 2 170804734459825603 = some 170804734459825603 := by decide +kernel
private theorem endpoint_10_33_prefix_6 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 6 170804734459825603 = some 170804734459825603 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 4 2 170804734459825603 170804734459825603 170804734459825603 endpoint_10_33_prefix_4 endpoint_10_33_window_4
private theorem endpoint_10_33_window_6 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 6 2 170804734459825603 = some 170804734459825603 := by decide +kernel
private theorem endpoint_10_33_prefix_8 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 8 170804734459825603 = some 170804734459825603 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 6 2 170804734459825603 170804734459825603 170804734459825603 endpoint_10_33_prefix_6 endpoint_10_33_window_6
private theorem endpoint_10_33_window_8 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 8 1 170804734459825603 = some 170804734459825603 := by decide +kernel
private theorem endpoint_10_33_prefix_9 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 9 170804734459825603 = some 170804734459825603 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 8 1 170804734459825603 170804734459825603 170804734459825603 endpoint_10_33_prefix_8 endpoint_10_33_window_8

def endpoint_10_33 : CertifiedEndpoint :=
  ⟨⟨10, 33, 3840⟩, 170804734459825603, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_33_flag endpoint_10_33_sources 9 170804734459825603 170804734459825603 rfl endpoint_10_33_base endpoint_10_33_prefix_9) (by decide)⟩
private def endpoint_10_34_flag : Flag := ⟨10, 34, 3816⟩
private def endpoint_10_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_34_base : receiptBase endpoint_10_34_flag endpoint_10_34_sources = some 173963835100331500 := by decide +kernel
private theorem endpoint_10_34_window_0 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 2 173963835100331500 = some 173963835100331500 := by decide +kernel
private theorem endpoint_10_34_window_2 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 2 2 173963835100331500 = some 173963835100331500 := by decide +kernel
private theorem endpoint_10_34_prefix_4 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 4 173963835100331500 = some 173963835100331500 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 2 2 173963835100331500 173963835100331500 173963835100331500 endpoint_10_34_window_0 endpoint_10_34_window_2
private theorem endpoint_10_34_window_4 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 4 2 173963835100331500 = some 173963835100331500 := by decide +kernel
private theorem endpoint_10_34_prefix_6 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 6 173963835100331500 = some 173963835100331500 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 4 2 173963835100331500 173963835100331500 173963835100331500 endpoint_10_34_prefix_4 endpoint_10_34_window_4
private theorem endpoint_10_34_window_6 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 6 2 173963835100331500 = some 173963835100331500 := by decide +kernel
private theorem endpoint_10_34_prefix_8 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 8 173963835100331500 = some 173963835100331500 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 6 2 173963835100331500 173963835100331500 173963835100331500 endpoint_10_34_prefix_6 endpoint_10_34_window_6
private theorem endpoint_10_34_window_8 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 8 1 173963835100331500 = some 173963835100331500 := by decide +kernel
private theorem endpoint_10_34_prefix_9 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 9 173963835100331500 = some 173963835100331500 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 8 1 173963835100331500 173963835100331500 173963835100331500 endpoint_10_34_prefix_8 endpoint_10_34_window_8

def endpoint_10_34 : CertifiedEndpoint :=
  ⟨⟨10, 34, 3816⟩, 173963835100331500, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_34_flag endpoint_10_34_sources 9 173963835100331500 173963835100331500 rfl endpoint_10_34_base endpoint_10_34_prefix_9) (by decide)⟩
private def endpoint_10_35_flag : Flag := ⟨10, 35, 3792⟩
private def endpoint_10_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_35_base : receiptBase endpoint_10_35_flag endpoint_10_35_sources = some 177069828818709737 := by decide +kernel
private theorem endpoint_10_35_window_0 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 2 177069828818709737 = some 177069828818709737 := by decide +kernel
private theorem endpoint_10_35_window_2 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 2 2 177069828818709737 = some 177069828818709737 := by decide +kernel
private theorem endpoint_10_35_prefix_4 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 4 177069828818709737 = some 177069828818709737 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 2 2 177069828818709737 177069828818709737 177069828818709737 endpoint_10_35_window_0 endpoint_10_35_window_2
private theorem endpoint_10_35_window_4 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 4 2 177069828818709737 = some 177069828818709737 := by decide +kernel
private theorem endpoint_10_35_prefix_6 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 6 177069828818709737 = some 177069828818709737 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 4 2 177069828818709737 177069828818709737 177069828818709737 endpoint_10_35_prefix_4 endpoint_10_35_window_4
private theorem endpoint_10_35_window_6 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 6 2 177069828818709737 = some 177069828818709737 := by decide +kernel
private theorem endpoint_10_35_prefix_8 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 8 177069828818709737 = some 177069828818709737 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 6 2 177069828818709737 177069828818709737 177069828818709737 endpoint_10_35_prefix_6 endpoint_10_35_window_6
private theorem endpoint_10_35_window_8 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 8 1 177069828818709737 = some 177069828818709737 := by decide +kernel
private theorem endpoint_10_35_prefix_9 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 9 177069828818709737 = some 177069828818709737 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 8 1 177069828818709737 177069828818709737 177069828818709737 endpoint_10_35_prefix_8 endpoint_10_35_window_8

def endpoint_10_35 : CertifiedEndpoint :=
  ⟨⟨10, 35, 3792⟩, 177069828818709737, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_35_flag endpoint_10_35_sources 9 177069828818709737 177069828818709737 rfl endpoint_10_35_base endpoint_10_35_prefix_9) (by decide)⟩
private def endpoint_10_36_flag : Flag := ⟨10, 36, 3768⟩
private def endpoint_10_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_36_base : receiptBase endpoint_10_36_flag endpoint_10_36_sources = some 180122715614960315 := by decide +kernel
private theorem endpoint_10_36_window_0 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 2 180122715614960315 = some 180122715614960315 := by decide +kernel
private theorem endpoint_10_36_window_2 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 2 2 180122715614960315 = some 180122715614960315 := by decide +kernel
private theorem endpoint_10_36_prefix_4 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 4 180122715614960315 = some 180122715614960315 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 2 2 180122715614960315 180122715614960315 180122715614960315 endpoint_10_36_window_0 endpoint_10_36_window_2
private theorem endpoint_10_36_window_4 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 4 2 180122715614960315 = some 180122715614960315 := by decide +kernel
private theorem endpoint_10_36_prefix_6 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 6 180122715614960315 = some 180122715614960315 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 4 2 180122715614960315 180122715614960315 180122715614960315 endpoint_10_36_prefix_4 endpoint_10_36_window_4
private theorem endpoint_10_36_window_6 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 6 2 180122715614960315 = some 180122715614960315 := by decide +kernel
private theorem endpoint_10_36_prefix_8 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 8 180122715614960315 = some 180122715614960315 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 6 2 180122715614960315 180122715614960315 180122715614960315 endpoint_10_36_prefix_6 endpoint_10_36_window_6
private theorem endpoint_10_36_window_8 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 8 1 180122715614960315 = some 180122715614960315 := by decide +kernel
private theorem endpoint_10_36_prefix_9 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 9 180122715614960315 = some 180122715614960315 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 8 1 180122715614960315 180122715614960315 180122715614960315 endpoint_10_36_prefix_8 endpoint_10_36_window_8

def endpoint_10_36 : CertifiedEndpoint :=
  ⟨⟨10, 36, 3768⟩, 180122715614960315, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_36_flag endpoint_10_36_sources 9 180122715614960315 180122715614960315 rfl endpoint_10_36_base endpoint_10_36_prefix_9) (by decide)⟩
private def endpoint_10_37_flag : Flag := ⟨10, 37, 3743⟩
private def endpoint_10_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_37_base : receiptBase endpoint_10_37_flag endpoint_10_37_sources = some 183074311979832732 := by decide +kernel
private theorem endpoint_10_37_window_0 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 2 183074311979832732 = some 183074311979832732 := by decide +kernel
private theorem endpoint_10_37_window_2 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 2 2 183074311979832732 = some 183074311979832732 := by decide +kernel
private theorem endpoint_10_37_prefix_4 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 4 183074311979832732 = some 183074311979832732 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 2 2 183074311979832732 183074311979832732 183074311979832732 endpoint_10_37_window_0 endpoint_10_37_window_2
private theorem endpoint_10_37_window_4 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 4 2 183074311979832732 = some 183074311979832732 := by decide +kernel
private theorem endpoint_10_37_prefix_6 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 6 183074311979832732 = some 183074311979832732 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 4 2 183074311979832732 183074311979832732 183074311979832732 endpoint_10_37_prefix_4 endpoint_10_37_window_4
private theorem endpoint_10_37_window_6 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 6 2 183074311979832732 = some 183074311979832732 := by decide +kernel
private theorem endpoint_10_37_prefix_8 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 8 183074311979832732 = some 183074311979832732 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 6 2 183074311979832732 183074311979832732 183074311979832732 endpoint_10_37_prefix_6 endpoint_10_37_window_6
private theorem endpoint_10_37_window_8 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 8 1 183074311979832732 = some 183074311979832732 := by decide +kernel
private theorem endpoint_10_37_prefix_9 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 9 183074311979832732 = some 183074311979832732 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 8 1 183074311979832732 183074311979832732 183074311979832732 endpoint_10_37_prefix_8 endpoint_10_37_window_8

def endpoint_10_37 : CertifiedEndpoint :=
  ⟨⟨10, 37, 3743⟩, 183074311979832732, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_37_flag endpoint_10_37_sources 9 183074311979832732 183074311979832732 rfl endpoint_10_37_base endpoint_10_37_prefix_9) (by decide)⟩
private def endpoint_10_38_flag : Flag := ⟨10, 38, 3718⟩
private def endpoint_10_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_38_base : receiptBase endpoint_10_38_flag endpoint_10_38_sources = some 185970633976760239 := by decide +kernel
private theorem endpoint_10_38_window_0 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 2 185970633976760239 = some 185970633976760239 := by decide +kernel
private theorem endpoint_10_38_window_2 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 2 2 185970633976760239 = some 185970633976760239 := by decide +kernel
private theorem endpoint_10_38_prefix_4 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 4 185970633976760239 = some 185970633976760239 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 2 2 185970633976760239 185970633976760239 185970633976760239 endpoint_10_38_window_0 endpoint_10_38_window_2
private theorem endpoint_10_38_window_4 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 4 2 185970633976760239 = some 185970633976760239 := by decide +kernel
private theorem endpoint_10_38_prefix_6 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 6 185970633976760239 = some 185970633976760239 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 4 2 185970633976760239 185970633976760239 185970633976760239 endpoint_10_38_prefix_4 endpoint_10_38_window_4
private theorem endpoint_10_38_window_6 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 6 2 185970633976760239 = some 185970633976760239 := by decide +kernel
private theorem endpoint_10_38_prefix_8 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 8 185970633976760239 = some 185970633976760239 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 6 2 185970633976760239 185970633976760239 185970633976760239 endpoint_10_38_prefix_6 endpoint_10_38_window_6
private theorem endpoint_10_38_window_8 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 8 1 185970633976760239 = some 185970633976760239 := by decide +kernel
private theorem endpoint_10_38_prefix_9 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 9 185970633976760239 = some 185970633976760239 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 8 1 185970633976760239 185970633976760239 185970633976760239 endpoint_10_38_prefix_8 endpoint_10_38_window_8

def endpoint_10_38 : CertifiedEndpoint :=
  ⟨⟨10, 38, 3718⟩, 185970633976760239, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_38_flag endpoint_10_38_sources 9 185970633976760239 185970633976760239 rfl endpoint_10_38_base endpoint_10_38_prefix_9) (by decide)⟩
private def endpoint_10_39_flag : Flag := ⟨10, 39, 3693⟩
private def endpoint_10_39_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_39_base : receiptBase endpoint_10_39_flag endpoint_10_39_sources = some 188811681605742836 := by decide +kernel
private theorem endpoint_10_39_window_0 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 2 188811681605742836 = some 188811681605742836 := by decide +kernel
private theorem endpoint_10_39_window_2 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 2 2 188811681605742836 = some 188811681605742836 := by decide +kernel
private theorem endpoint_10_39_prefix_4 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 4 188811681605742836 = some 188811681605742836 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 2 2 188811681605742836 188811681605742836 188811681605742836 endpoint_10_39_window_0 endpoint_10_39_window_2
private theorem endpoint_10_39_window_4 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 4 2 188811681605742836 = some 188811681605742836 := by decide +kernel
private theorem endpoint_10_39_prefix_6 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 6 188811681605742836 = some 188811681605742836 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 4 2 188811681605742836 188811681605742836 188811681605742836 endpoint_10_39_prefix_4 endpoint_10_39_window_4
private theorem endpoint_10_39_window_6 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 6 2 188811681605742836 = some 188811681605742836 := by decide +kernel
private theorem endpoint_10_39_prefix_8 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 8 188811681605742836 = some 188811681605742836 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 6 2 188811681605742836 188811681605742836 188811681605742836 endpoint_10_39_prefix_6 endpoint_10_39_window_6
private theorem endpoint_10_39_window_8 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 8 1 188811681605742836 = some 188811681605742836 := by decide +kernel
private theorem endpoint_10_39_prefix_9 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 9 188811681605742836 = some 188811681605742836 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 8 1 188811681605742836 188811681605742836 188811681605742836 endpoint_10_39_prefix_8 endpoint_10_39_window_8

def endpoint_10_39 : CertifiedEndpoint :=
  ⟨⟨10, 39, 3693⟩, 188811681605742836, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_39_flag endpoint_10_39_sources 9 188811681605742836 188811681605742836 rfl endpoint_10_39_base endpoint_10_39_prefix_9) (by decide)⟩
private def endpoint_10_40_flag : Flag := ⟨10, 40, 3667⟩
private def endpoint_10_40_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_40_base : receiptBase endpoint_10_40_flag endpoint_10_40_sources = some 191546020188804145 := by decide +kernel
private theorem endpoint_10_40_window_0 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 2 191546020188804145 = some 191546020188804145 := by decide +kernel
private theorem endpoint_10_40_window_2 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 2 2 191546020188804145 = some 191546020188804145 := by decide +kernel
private theorem endpoint_10_40_prefix_4 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 4 191546020188804145 = some 191546020188804145 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 2 2 191546020188804145 191546020188804145 191546020188804145 endpoint_10_40_window_0 endpoint_10_40_window_2
private theorem endpoint_10_40_window_4 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 4 2 191546020188804145 = some 191546020188804145 := by decide +kernel
private theorem endpoint_10_40_prefix_6 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 6 191546020188804145 = some 191546020188804145 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 4 2 191546020188804145 191546020188804145 191546020188804145 endpoint_10_40_prefix_4 endpoint_10_40_window_4
private theorem endpoint_10_40_window_6 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 6 2 191546020188804145 = some 191546020188804145 := by decide +kernel
private theorem endpoint_10_40_prefix_8 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 8 191546020188804145 = some 191546020188804145 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 6 2 191546020188804145 191546020188804145 191546020188804145 endpoint_10_40_prefix_6 endpoint_10_40_window_6
private theorem endpoint_10_40_window_8 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 8 1 191546020188804145 = some 191546020188804145 := by decide +kernel
private theorem endpoint_10_40_prefix_9 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 9 191546020188804145 = some 191546020188804145 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 8 1 191546020188804145 191546020188804145 191546020188804145 endpoint_10_40_prefix_8 endpoint_10_40_window_8

def endpoint_10_40 : CertifiedEndpoint :=
  ⟨⟨10, 40, 3667⟩, 191546020188804145, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_40_flag endpoint_10_40_sources 9 191546020188804145 191546020188804145 rfl endpoint_10_40_base endpoint_10_40_prefix_9) (by decide)⟩
private def endpoint_10_41_flag : Flag := ⟨10, 41, 3640⟩
private def endpoint_10_41_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_41_base : receiptBase endpoint_10_41_flag endpoint_10_41_sources = some 194170398557218290 := by decide +kernel
private theorem endpoint_10_41_window_0 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 2 194170398557218290 = some 194170398557218290 := by decide +kernel
private theorem endpoint_10_41_window_2 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 2 2 194170398557218290 = some 194170398557218290 := by decide +kernel
private theorem endpoint_10_41_prefix_4 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 4 194170398557218290 = some 194170398557218290 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 2 2 194170398557218290 194170398557218290 194170398557218290 endpoint_10_41_window_0 endpoint_10_41_window_2
private theorem endpoint_10_41_window_4 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 4 2 194170398557218290 = some 194170398557218290 := by decide +kernel
private theorem endpoint_10_41_prefix_6 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 6 194170398557218290 = some 194170398557218290 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 4 2 194170398557218290 194170398557218290 194170398557218290 endpoint_10_41_prefix_4 endpoint_10_41_window_4
private theorem endpoint_10_41_window_6 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 6 2 194170398557218290 = some 194170398557218290 := by decide +kernel
private theorem endpoint_10_41_prefix_8 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 8 194170398557218290 = some 194170398557218290 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 6 2 194170398557218290 194170398557218290 194170398557218290 endpoint_10_41_prefix_6 endpoint_10_41_window_6
private theorem endpoint_10_41_window_8 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 8 1 194170398557218290 = some 194170398557218290 := by decide +kernel
private theorem endpoint_10_41_prefix_9 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 9 194170398557218290 = some 194170398557218290 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 8 1 194170398557218290 194170398557218290 194170398557218290 endpoint_10_41_prefix_8 endpoint_10_41_window_8

def endpoint_10_41 : CertifiedEndpoint :=
  ⟨⟨10, 41, 3640⟩, 194170398557218290, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_41_flag endpoint_10_41_sources 9 194170398557218290 194170398557218290 rfl endpoint_10_41_base endpoint_10_41_prefix_9) (by decide)⟩
private def endpoint_10_42_flag : Flag := ⟨10, 42, 3614⟩
private def endpoint_10_42_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_42_base : receiptBase endpoint_10_42_flag endpoint_10_42_sources = some 196788769789846652 := by decide +kernel
private theorem endpoint_10_42_window_0 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 2 196788769789846652 = some 196788769789846652 := by decide +kernel
private theorem endpoint_10_42_window_2 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 2 2 196788769789846652 = some 196788769789846652 := by decide +kernel
private theorem endpoint_10_42_prefix_4 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 4 196788769789846652 = some 196788769789846652 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 2 2 196788769789846652 196788769789846652 196788769789846652 endpoint_10_42_window_0 endpoint_10_42_window_2
private theorem endpoint_10_42_window_4 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 4 2 196788769789846652 = some 196788769789846652 := by decide +kernel
private theorem endpoint_10_42_prefix_6 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 6 196788769789846652 = some 196788769789846652 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 4 2 196788769789846652 196788769789846652 196788769789846652 endpoint_10_42_prefix_4 endpoint_10_42_window_4
private theorem endpoint_10_42_window_6 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 6 2 196788769789846652 = some 196788769789846652 := by decide +kernel
private theorem endpoint_10_42_prefix_8 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 8 196788769789846652 = some 196788769789846652 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 6 2 196788769789846652 196788769789846652 196788769789846652 endpoint_10_42_prefix_6 endpoint_10_42_window_6
private theorem endpoint_10_42_window_8 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 8 1 196788769789846652 = some 196788769789846652 := by decide +kernel
private theorem endpoint_10_42_prefix_9 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 9 196788769789846652 = some 196788769789846652 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 8 1 196788769789846652 196788769789846652 196788769789846652 endpoint_10_42_prefix_8 endpoint_10_42_window_8

def endpoint_10_42 : CertifiedEndpoint :=
  ⟨⟨10, 42, 3614⟩, 196788769789846652, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_42_flag endpoint_10_42_sources 9 196788769789846652 196788769789846652 rfl endpoint_10_42_base endpoint_10_42_prefix_9) (by decide)⟩
private def endpoint_10_43_flag : Flag := ⟨10, 43, 3587⟩
private def endpoint_10_43_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_43_base : receiptBase endpoint_10_43_flag endpoint_10_43_sources = some 199785600504524882 := by decide +kernel
private theorem endpoint_10_43_window_0 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 2 199785600504524882 = some 199785600504524882 := by decide +kernel
private theorem endpoint_10_43_window_2 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 2 2 199785600504524882 = some 199785600504524882 := by decide +kernel
private theorem endpoint_10_43_prefix_4 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 4 199785600504524882 = some 199785600504524882 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 2 2 199785600504524882 199785600504524882 199785600504524882 endpoint_10_43_window_0 endpoint_10_43_window_2
private theorem endpoint_10_43_window_4 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 4 2 199785600504524882 = some 199785600504524882 := by decide +kernel
private theorem endpoint_10_43_prefix_6 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 6 199785600504524882 = some 199785600504524882 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 4 2 199785600504524882 199785600504524882 199785600504524882 endpoint_10_43_prefix_4 endpoint_10_43_window_4
private theorem endpoint_10_43_window_6 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 6 2 199785600504524882 = some 199785600504524882 := by decide +kernel
private theorem endpoint_10_43_prefix_8 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 8 199785600504524882 = some 199785600504524882 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 6 2 199785600504524882 199785600504524882 199785600504524882 endpoint_10_43_prefix_6 endpoint_10_43_window_6
private theorem endpoint_10_43_window_8 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 8 1 199785600504524882 = some 199785600504524882 := by decide +kernel
private theorem endpoint_10_43_prefix_9 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 9 199785600504524882 = some 199785600504524882 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 8 1 199785600504524882 199785600504524882 199785600504524882 endpoint_10_43_prefix_8 endpoint_10_43_window_8

def endpoint_10_43 : CertifiedEndpoint :=
  ⟨⟨10, 43, 3587⟩, 199785600504524882, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_43_flag endpoint_10_43_sources 9 199785600504524882 199785600504524882 rfl endpoint_10_43_base endpoint_10_43_prefix_9) (by decide)⟩
private def endpoint_10_44_flag : Flag := ⟨10, 44, 3559⟩
private def endpoint_10_44_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_44_base : receiptBase endpoint_10_44_flag endpoint_10_44_sources = some 202147256959357387 := by decide +kernel
private theorem endpoint_10_44_window_0 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 2 202147256959357387 = some 202147256959357387 := by decide +kernel
private theorem endpoint_10_44_window_2 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 2 2 202147256959357387 = some 202147256959357387 := by decide +kernel
private theorem endpoint_10_44_prefix_4 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 4 202147256959357387 = some 202147256959357387 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 2 2 202147256959357387 202147256959357387 202147256959357387 endpoint_10_44_window_0 endpoint_10_44_window_2
private theorem endpoint_10_44_window_4 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 4 2 202147256959357387 = some 202147256959357387 := by decide +kernel
private theorem endpoint_10_44_prefix_6 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 6 202147256959357387 = some 202147256959357387 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 4 2 202147256959357387 202147256959357387 202147256959357387 endpoint_10_44_prefix_4 endpoint_10_44_window_4
private theorem endpoint_10_44_window_6 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 6 2 202147256959357387 = some 202147256959357387 := by decide +kernel
private theorem endpoint_10_44_prefix_8 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 8 202147256959357387 = some 202147256959357387 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 6 2 202147256959357387 202147256959357387 202147256959357387 endpoint_10_44_prefix_6 endpoint_10_44_window_6
private theorem endpoint_10_44_window_8 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 8 1 202147256959357387 = some 202147256959357387 := by decide +kernel
private theorem endpoint_10_44_prefix_9 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 9 202147256959357387 = some 202147256959357387 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 8 1 202147256959357387 202147256959357387 202147256959357387 endpoint_10_44_prefix_8 endpoint_10_44_window_8

def endpoint_10_44 : CertifiedEndpoint :=
  ⟨⟨10, 44, 3559⟩, 202147256959357387, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_44_flag endpoint_10_44_sources 9 202147256959357387 202147256959357387 rfl endpoint_10_44_base endpoint_10_44_prefix_9) (by decide)⟩
private def endpoint_10_45_flag : Flag := ⟨10, 45, 3531⟩
private def endpoint_10_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_45_base : receiptBase endpoint_10_45_flag endpoint_10_45_sources = some 204447397642593327 := by decide +kernel
private theorem endpoint_10_45_window_0 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 2 204447397642593327 = some 204447397642593327 := by decide +kernel
private theorem endpoint_10_45_window_2 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 2 2 204447397642593327 = some 204447397642593327 := by decide +kernel
private theorem endpoint_10_45_prefix_4 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 4 204447397642593327 = some 204447397642593327 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 2 2 204447397642593327 204447397642593327 204447397642593327 endpoint_10_45_window_0 endpoint_10_45_window_2
private theorem endpoint_10_45_window_4 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 4 2 204447397642593327 = some 204447397642593327 := by decide +kernel
private theorem endpoint_10_45_prefix_6 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 6 204447397642593327 = some 204447397642593327 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 4 2 204447397642593327 204447397642593327 204447397642593327 endpoint_10_45_prefix_4 endpoint_10_45_window_4
private theorem endpoint_10_45_window_6 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 6 2 204447397642593327 = some 204447397642593327 := by decide +kernel
private theorem endpoint_10_45_prefix_8 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 8 204447397642593327 = some 204447397642593327 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 6 2 204447397642593327 204447397642593327 204447397642593327 endpoint_10_45_prefix_6 endpoint_10_45_window_6
private theorem endpoint_10_45_window_8 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 8 1 204447397642593327 = some 204447397642593327 := by decide +kernel
private theorem endpoint_10_45_prefix_9 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 9 204447397642593327 = some 204447397642593327 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 8 1 204447397642593327 204447397642593327 204447397642593327 endpoint_10_45_prefix_8 endpoint_10_45_window_8

def endpoint_10_45 : CertifiedEndpoint :=
  ⟨⟨10, 45, 3531⟩, 204447397642593327, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_45_flag endpoint_10_45_sources 9 204447397642593327 204447397642593327 rfl endpoint_10_45_base endpoint_10_45_prefix_9) (by decide)⟩
private def endpoint_10_46_flag : Flag := ⟨10, 46, 3502⟩
private def endpoint_10_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_46_base : receiptBase endpoint_10_46_flag endpoint_10_46_sources = some 206627876419334476 := by decide +kernel
private theorem endpoint_10_46_window_0 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 2 206627876419334476 = some 206627876419334476 := by decide +kernel
private theorem endpoint_10_46_window_2 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 2 2 206627876419334476 = some 206627876419334476 := by decide +kernel
private theorem endpoint_10_46_prefix_4 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 4 206627876419334476 = some 206627876419334476 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 2 2 206627876419334476 206627876419334476 206627876419334476 endpoint_10_46_window_0 endpoint_10_46_window_2
private theorem endpoint_10_46_window_4 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 4 2 206627876419334476 = some 206627876419334476 := by decide +kernel
private theorem endpoint_10_46_prefix_6 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 6 206627876419334476 = some 206627876419334476 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 4 2 206627876419334476 206627876419334476 206627876419334476 endpoint_10_46_prefix_4 endpoint_10_46_window_4
private theorem endpoint_10_46_window_6 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 6 2 206627876419334476 = some 206627876419334476 := by decide +kernel
private theorem endpoint_10_46_prefix_8 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 8 206627876419334476 = some 206627876419334476 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 6 2 206627876419334476 206627876419334476 206627876419334476 endpoint_10_46_prefix_6 endpoint_10_46_window_6
private theorem endpoint_10_46_window_8 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 8 1 206627876419334476 = some 206627876419334476 := by decide +kernel
private theorem endpoint_10_46_prefix_9 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 9 206627876419334476 = some 206627876419334476 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 8 1 206627876419334476 206627876419334476 206627876419334476 endpoint_10_46_prefix_8 endpoint_10_46_window_8

def endpoint_10_46 : CertifiedEndpoint :=
  ⟨⟨10, 46, 3502⟩, 206627876419334476, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_46_flag endpoint_10_46_sources 9 206627876419334476 206627876419334476 rfl endpoint_10_46_base endpoint_10_46_prefix_9) (by decide)⟩
private def endpoint_10_47_flag : Flag := ⟨10, 47, 3473⟩
private def endpoint_10_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_47_base : receiptBase endpoint_10_47_flag endpoint_10_47_sources = some 208744680976352864 := by decide +kernel
private theorem endpoint_10_47_window_0 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 2 208744680976352864 = some 208744680976352864 := by decide +kernel
private theorem endpoint_10_47_window_2 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 2 2 208744680976352864 = some 208744680976352864 := by decide +kernel
private theorem endpoint_10_47_prefix_4 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 4 208744680976352864 = some 208744680976352864 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 2 2 208744680976352864 208744680976352864 208744680976352864 endpoint_10_47_window_0 endpoint_10_47_window_2
private theorem endpoint_10_47_window_4 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 4 2 208744680976352864 = some 208744680976352864 := by decide +kernel
private theorem endpoint_10_47_prefix_6 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 6 208744680976352864 = some 208744680976352864 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 4 2 208744680976352864 208744680976352864 208744680976352864 endpoint_10_47_prefix_4 endpoint_10_47_window_4
private theorem endpoint_10_47_window_6 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 6 2 208744680976352864 = some 208744680976352864 := by decide +kernel
private theorem endpoint_10_47_prefix_8 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 8 208744680976352864 = some 208744680976352864 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 6 2 208744680976352864 208744680976352864 208744680976352864 endpoint_10_47_prefix_6 endpoint_10_47_window_6
private theorem endpoint_10_47_window_8 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 8 1 208744680976352864 = some 208744680976352864 := by decide +kernel
private theorem endpoint_10_47_prefix_9 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 9 208744680976352864 = some 208744680976352864 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 8 1 208744680976352864 208744680976352864 208744680976352864 endpoint_10_47_prefix_8 endpoint_10_47_window_8

def endpoint_10_47 : CertifiedEndpoint :=
  ⟨⟨10, 47, 3473⟩, 208744680976352864, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_47_flag endpoint_10_47_sources 9 208744680976352864 208744680976352864 rfl endpoint_10_47_base endpoint_10_47_prefix_9) (by decide)⟩
private def endpoint_10_48_flag : Flag := ⟨10, 48, 3443⟩
private def endpoint_10_48_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_48_base : receiptBase endpoint_10_48_flag endpoint_10_48_sources = some 210737506730624071 := by decide +kernel
private theorem endpoint_10_48_window_0 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 2 210737506730624071 = some 210737506730624071 := by decide +kernel
private theorem endpoint_10_48_window_2 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 2 2 210737506730624071 = some 210737506730624071 := by decide +kernel
private theorem endpoint_10_48_prefix_4 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 4 210737506730624071 = some 210737506730624071 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 2 2 210737506730624071 210737506730624071 210737506730624071 endpoint_10_48_window_0 endpoint_10_48_window_2
private theorem endpoint_10_48_window_4 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 4 2 210737506730624071 = some 210737506730624071 := by decide +kernel
private theorem endpoint_10_48_prefix_6 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 6 210737506730624071 = some 210737506730624071 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 4 2 210737506730624071 210737506730624071 210737506730624071 endpoint_10_48_prefix_4 endpoint_10_48_window_4
private theorem endpoint_10_48_window_6 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 6 2 210737506730624071 = some 210737506730624071 := by decide +kernel
private theorem endpoint_10_48_prefix_8 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 8 210737506730624071 = some 210737506730624071 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 6 2 210737506730624071 210737506730624071 210737506730624071 endpoint_10_48_prefix_6 endpoint_10_48_window_6
private theorem endpoint_10_48_window_8 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 8 1 210737506730624071 = some 210737506730624071 := by decide +kernel
private theorem endpoint_10_48_prefix_9 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 9 210737506730624071 = some 210737506730624071 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 8 1 210737506730624071 210737506730624071 210737506730624071 endpoint_10_48_prefix_8 endpoint_10_48_window_8

def endpoint_10_48 : CertifiedEndpoint :=
  ⟨⟨10, 48, 3443⟩, 210737506730624071, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_48_flag endpoint_10_48_sources 9 210737506730624071 210737506730624071 rfl endpoint_10_48_base endpoint_10_48_prefix_9) (by decide)⟩
private def endpoint_10_49_flag : Flag := ⟨10, 49, 3412⟩
private def endpoint_10_49_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_49_base : receiptBase endpoint_10_49_flag endpoint_10_49_sources = some 212603116009958803 := by decide +kernel
private theorem endpoint_10_49_window_0 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 2 212603116009958803 = some 212603116009958803 := by decide +kernel
private theorem endpoint_10_49_window_2 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 2 2 212603116009958803 = some 212603116009958803 := by decide +kernel
private theorem endpoint_10_49_prefix_4 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 4 212603116009958803 = some 212603116009958803 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 2 2 212603116009958803 212603116009958803 212603116009958803 endpoint_10_49_window_0 endpoint_10_49_window_2
private theorem endpoint_10_49_window_4 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 4 2 212603116009958803 = some 212603116009958803 := by decide +kernel
private theorem endpoint_10_49_prefix_6 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 6 212603116009958803 = some 212603116009958803 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 4 2 212603116009958803 212603116009958803 212603116009958803 endpoint_10_49_prefix_4 endpoint_10_49_window_4
private theorem endpoint_10_49_window_6 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 6 2 212603116009958803 = some 212603116009958803 := by decide +kernel
private theorem endpoint_10_49_prefix_8 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 8 212603116009958803 = some 212603116009958803 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 6 2 212603116009958803 212603116009958803 212603116009958803 endpoint_10_49_prefix_6 endpoint_10_49_window_6
private theorem endpoint_10_49_window_8 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 8 1 212603116009958803 = some 212603116009958803 := by decide +kernel
private theorem endpoint_10_49_prefix_9 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 9 212603116009958803 = some 212603116009958803 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 8 1 212603116009958803 212603116009958803 212603116009958803 endpoint_10_49_prefix_8 endpoint_10_49_window_8

def endpoint_10_49 : CertifiedEndpoint :=
  ⟨⟨10, 49, 3412⟩, 212603116009958803, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_49_flag endpoint_10_49_sources 9 212603116009958803 212603116009958803 rfl endpoint_10_49_base endpoint_10_49_prefix_9) (by decide)⟩
private def endpoint_10_50_flag : Flag := ⟨10, 50, 3381⟩
private def endpoint_10_50_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_50_base : receiptBase endpoint_10_50_flag endpoint_10_50_sources = some 214400734173318385 := by decide +kernel
private theorem endpoint_10_50_window_0 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 2 214400734173318385 = some 214400734173318385 := by decide +kernel
private theorem endpoint_10_50_window_2 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 2 2 214400734173318385 = some 214400734173318385 := by decide +kernel
private theorem endpoint_10_50_prefix_4 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 4 214400734173318385 = some 214400734173318385 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 2 2 214400734173318385 214400734173318385 214400734173318385 endpoint_10_50_window_0 endpoint_10_50_window_2
private theorem endpoint_10_50_window_4 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 4 2 214400734173318385 = some 214400734173318385 := by decide +kernel
private theorem endpoint_10_50_prefix_6 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 6 214400734173318385 = some 214400734173318385 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 4 2 214400734173318385 214400734173318385 214400734173318385 endpoint_10_50_prefix_4 endpoint_10_50_window_4
private theorem endpoint_10_50_window_6 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 6 2 214400734173318385 = some 214400734173318385 := by decide +kernel
private theorem endpoint_10_50_prefix_8 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 8 214400734173318385 = some 214400734173318385 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 6 2 214400734173318385 214400734173318385 214400734173318385 endpoint_10_50_prefix_6 endpoint_10_50_window_6
private theorem endpoint_10_50_window_8 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 8 1 214400734173318385 = some 214400734173318385 := by decide +kernel
private theorem endpoint_10_50_prefix_9 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 9 214400734173318385 = some 214400734173318385 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 8 1 214400734173318385 214400734173318385 214400734173318385 endpoint_10_50_prefix_8 endpoint_10_50_window_8

def endpoint_10_50 : CertifiedEndpoint :=
  ⟨⟨10, 50, 3381⟩, 214400734173318385, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_50_flag endpoint_10_50_sources 9 214400734173318385 214400734173318385 rfl endpoint_10_50_base endpoint_10_50_prefix_9) (by decide)⟩
private def endpoint_10_51_flag : Flag := ⟨10, 51, 3349⟩
private def endpoint_10_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_51_base : receiptBase endpoint_10_51_flag endpoint_10_51_sources = some 216066818965489102 := by decide +kernel
private theorem endpoint_10_51_window_0 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 2 216066818965489102 = some 216066818965489102 := by decide +kernel
private theorem endpoint_10_51_window_2 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 2 2 216066818965489102 = some 216066818965489102 := by decide +kernel
private theorem endpoint_10_51_prefix_4 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 4 216066818965489102 = some 216066818965489102 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 2 2 216066818965489102 216066818965489102 216066818965489102 endpoint_10_51_window_0 endpoint_10_51_window_2
private theorem endpoint_10_51_window_4 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 4 2 216066818965489102 = some 216066818965489102 := by decide +kernel
private theorem endpoint_10_51_prefix_6 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 6 216066818965489102 = some 216066818965489102 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 4 2 216066818965489102 216066818965489102 216066818965489102 endpoint_10_51_prefix_4 endpoint_10_51_window_4
private theorem endpoint_10_51_window_6 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 6 2 216066818965489102 = some 216066818965489102 := by decide +kernel
private theorem endpoint_10_51_prefix_8 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 8 216066818965489102 = some 216066818965489102 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 6 2 216066818965489102 216066818965489102 216066818965489102 endpoint_10_51_prefix_6 endpoint_10_51_window_6
private theorem endpoint_10_51_window_8 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 8 1 216066818965489102 = some 216066818965489102 := by decide +kernel
private theorem endpoint_10_51_prefix_9 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 9 216066818965489102 = some 216066818965489102 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 8 1 216066818965489102 216066818965489102 216066818965489102 endpoint_10_51_prefix_8 endpoint_10_51_window_8

def endpoint_10_51 : CertifiedEndpoint :=
  ⟨⟨10, 51, 3349⟩, 216066818965489102, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_51_flag endpoint_10_51_sources 9 216066818965489102 216066818965489102 rfl endpoint_10_51_base endpoint_10_51_prefix_9) (by decide)⟩
private def endpoint_10_52_flag : Flag := ⟨10, 52, 3316⟩
private def endpoint_10_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_52_base : receiptBase endpoint_10_52_flag endpoint_10_52_sources = some 217598132714281661 := by decide +kernel
private theorem endpoint_10_52_window_0 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 2 217598132714281661 = some 217598132714281661 := by decide +kernel
private theorem endpoint_10_52_window_2 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 2 2 217598132714281661 = some 217598132714281661 := by decide +kernel
private theorem endpoint_10_52_prefix_4 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 4 217598132714281661 = some 217598132714281661 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 2 2 217598132714281661 217598132714281661 217598132714281661 endpoint_10_52_window_0 endpoint_10_52_window_2
private theorem endpoint_10_52_window_4 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 4 2 217598132714281661 = some 217598132714281661 := by decide +kernel
private theorem endpoint_10_52_prefix_6 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 6 217598132714281661 = some 217598132714281661 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 4 2 217598132714281661 217598132714281661 217598132714281661 endpoint_10_52_prefix_4 endpoint_10_52_window_4
private theorem endpoint_10_52_window_6 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 6 2 217598132714281661 = some 217598132714281661 := by decide +kernel
private theorem endpoint_10_52_prefix_8 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 8 217598132714281661 = some 217598132714281661 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 6 2 217598132714281661 217598132714281661 217598132714281661 endpoint_10_52_prefix_6 endpoint_10_52_window_6
private theorem endpoint_10_52_window_8 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 8 1 217598132714281661 = some 217598132714281661 := by decide +kernel
private theorem endpoint_10_52_prefix_9 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 9 217598132714281661 = some 217598132714281661 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 8 1 217598132714281661 217598132714281661 217598132714281661 endpoint_10_52_prefix_8 endpoint_10_52_window_8

def endpoint_10_52 : CertifiedEndpoint :=
  ⟨⟨10, 52, 3316⟩, 217598132714281661, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_52_flag endpoint_10_52_sources 9 217598132714281661 217598132714281661 rfl endpoint_10_52_base endpoint_10_52_prefix_9) (by decide)⟩
private def endpoint_10_53_flag : Flag := ⟨10, 53, 3282⟩
private def endpoint_10_53_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_10_53_base : receiptBase endpoint_10_53_flag endpoint_10_53_sources = some 219616264743158235 := by decide +kernel
private theorem endpoint_10_53_window_0 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 2 219616264743158235 = some 219616264743158235 := by decide +kernel
private theorem endpoint_10_53_window_2 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 2 2 219616264743158235 = some 219616264743158235 := by decide +kernel
private theorem endpoint_10_53_prefix_4 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 4 219616264743158235 = some 219616264743158235 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 2 2 219616264743158235 219616264743158235 219616264743158235 endpoint_10_53_window_0 endpoint_10_53_window_2
private theorem endpoint_10_53_window_4 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 4 2 219616264743158235 = some 219616264743158235 := by decide +kernel
private theorem endpoint_10_53_prefix_6 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 6 219616264743158235 = some 219616264743158235 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 4 2 219616264743158235 219616264743158235 219616264743158235 endpoint_10_53_prefix_4 endpoint_10_53_window_4
private theorem endpoint_10_53_window_6 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 6 2 219616264743158235 = some 219616264743158235 := by decide +kernel
private theorem endpoint_10_53_prefix_8 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 8 219616264743158235 = some 219616264743158235 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 6 2 219616264743158235 219616264743158235 219616264743158235 endpoint_10_53_prefix_6 endpoint_10_53_window_6
private theorem endpoint_10_53_window_8 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 8 1 219616264743158235 = some 219616264743158235 := by decide +kernel
private theorem endpoint_10_53_prefix_9 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 9 219616264743158235 = some 219616264743158235 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 8 1 219616264743158235 219616264743158235 219616264743158235 endpoint_10_53_prefix_8 endpoint_10_53_window_8

def endpoint_10_53 : CertifiedEndpoint :=
  ⟨⟨10, 53, 3282⟩, 219616264743158235, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_10_53_flag endpoint_10_53_sources 9 219616264743158235 219616264743158235 rfl endpoint_10_53_base endpoint_10_53_prefix_9) (by decide)⟩
private def endpoint_10_54_flag : Flag := ⟨10, 54, 3248⟩
private def endpoint_10_54_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_10_54_base : receiptBase endpoint_10_54_flag endpoint_10_54_sources = some 220942703714423719 := by decide +kernel
private theorem endpoint_10_54_window_0 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 2 220942703714423719 = some 220942703714423719 := by decide +kernel
private theorem endpoint_10_54_window_2 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 2 2 220942703714423719 = some 220942703714423719 := by decide +kernel
private theorem endpoint_10_54_prefix_4 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 4 220942703714423719 = some 220942703714423719 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 2 2 220942703714423719 220942703714423719 220942703714423719 endpoint_10_54_window_0 endpoint_10_54_window_2
private theorem endpoint_10_54_window_4 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 4 2 220942703714423719 = some 220942703714423719 := by decide +kernel
private theorem endpoint_10_54_prefix_6 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 6 220942703714423719 = some 220942703714423719 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 4 2 220942703714423719 220942703714423719 220942703714423719 endpoint_10_54_prefix_4 endpoint_10_54_window_4
private theorem endpoint_10_54_window_6 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 6 2 220942703714423719 = some 220942703714423719 := by decide +kernel
private theorem endpoint_10_54_prefix_8 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 8 220942703714423719 = some 220942703714423719 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 6 2 220942703714423719 220942703714423719 220942703714423719 endpoint_10_54_prefix_6 endpoint_10_54_window_6
private theorem endpoint_10_54_window_8 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 8 1 220942703714423719 = some 220942703714423719 := by decide +kernel
private theorem endpoint_10_54_prefix_9 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 9 220942703714423719 = some 220942703714423719 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 8 1 220942703714423719 220942703714423719 220942703714423719 endpoint_10_54_prefix_8 endpoint_10_54_window_8

def endpoint_10_54 : CertifiedEndpoint :=
  ⟨⟨10, 54, 3248⟩, 220942703714423719, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_10_54_flag endpoint_10_54_sources 9 220942703714423719 220942703714423719 rfl endpoint_10_54_base endpoint_10_54_prefix_9) (by decide)⟩
private def endpoint_10_55_flag : Flag := ⟨10, 55, 3212⟩
private def endpoint_10_55_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_10_55_base : receiptBase endpoint_10_55_flag endpoint_10_55_sources = some 222058237864841797 := by decide +kernel
private theorem endpoint_10_55_window_0 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 2 222058237864841797 = some 222058237864841797 := by decide +kernel
private theorem endpoint_10_55_window_2 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 2 2 222058237864841797 = some 222058237864841797 := by decide +kernel
private theorem endpoint_10_55_prefix_4 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 4 222058237864841797 = some 222058237864841797 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 2 2 222058237864841797 222058237864841797 222058237864841797 endpoint_10_55_window_0 endpoint_10_55_window_2
private theorem endpoint_10_55_window_4 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 4 2 222058237864841797 = some 222058237864841797 := by decide +kernel
private theorem endpoint_10_55_prefix_6 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 6 222058237864841797 = some 222058237864841797 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 4 2 222058237864841797 222058237864841797 222058237864841797 endpoint_10_55_prefix_4 endpoint_10_55_window_4
private theorem endpoint_10_55_window_6 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 6 2 222058237864841797 = some 222058237864841797 := by decide +kernel
private theorem endpoint_10_55_prefix_8 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 8 222058237864841797 = some 222058237864841797 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 6 2 222058237864841797 222058237864841797 222058237864841797 endpoint_10_55_prefix_6 endpoint_10_55_window_6
private theorem endpoint_10_55_window_8 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 8 1 222058237864841797 = some 222058237864841797 := by decide +kernel
private theorem endpoint_10_55_prefix_9 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 9 222058237864841797 = some 222058237864841797 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 8 1 222058237864841797 222058237864841797 222058237864841797 endpoint_10_55_prefix_8 endpoint_10_55_window_8

def endpoint_10_55 : CertifiedEndpoint :=
  ⟨⟨10, 55, 3212⟩, 222058237864841797, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_10_55_flag endpoint_10_55_sources 9 222058237864841797 222058237864841797 rfl endpoint_10_55_base endpoint_10_55_prefix_9) (by decide)⟩
private def endpoint_10_56_flag : Flag := ⟨10, 56, 3175⟩
private def endpoint_10_56_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_10_56_base : receiptBase endpoint_10_56_flag endpoint_10_56_sources = some 223222010122674527 := by decide +kernel
private theorem endpoint_10_56_window_0 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 2 223222010122674527 = some 223222010122674527 := by decide +kernel
private theorem endpoint_10_56_window_2 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 2 2 223222010122674527 = some 223222010122674527 := by decide +kernel
private theorem endpoint_10_56_prefix_4 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 4 223222010122674527 = some 223222010122674527 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 2 2 223222010122674527 223222010122674527 223222010122674527 endpoint_10_56_window_0 endpoint_10_56_window_2
private theorem endpoint_10_56_window_4 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 4 2 223222010122674527 = some 223222010122674527 := by decide +kernel
private theorem endpoint_10_56_prefix_6 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 6 223222010122674527 = some 223222010122674527 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 4 2 223222010122674527 223222010122674527 223222010122674527 endpoint_10_56_prefix_4 endpoint_10_56_window_4
private theorem endpoint_10_56_window_6 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 6 2 223222010122674527 = some 223222010122674527 := by decide +kernel
private theorem endpoint_10_56_prefix_8 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 8 223222010122674527 = some 223222010122674527 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 6 2 223222010122674527 223222010122674527 223222010122674527 endpoint_10_56_prefix_6 endpoint_10_56_window_6
private theorem endpoint_10_56_window_8 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 8 1 223222010122674527 = some 223222010122674527 := by decide +kernel
private theorem endpoint_10_56_prefix_9 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 9 223222010122674527 = some 223222010122674527 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 8 1 223222010122674527 223222010122674527 223222010122674527 endpoint_10_56_prefix_8 endpoint_10_56_window_8

def endpoint_10_56 : CertifiedEndpoint :=
  ⟨⟨10, 56, 3175⟩, 223222010122674527, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_10_56_flag endpoint_10_56_sources 9 223222010122674527 223222010122674527 rfl endpoint_10_56_base endpoint_10_56_prefix_9) (by decide)⟩
private def endpoint_10_57_flag : Flag := ⟨10, 57, 3138⟩
private def endpoint_10_57_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_57_base : receiptBase endpoint_10_57_flag endpoint_10_57_sources = some 226192367166552644 := by decide +kernel
private theorem endpoint_10_57_window_0 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 2 226192367166552644 = some 226192367166552644 := by decide +kernel
private theorem endpoint_10_57_window_2 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 2 2 226192367166552644 = some 226192367166552644 := by decide +kernel
private theorem endpoint_10_57_prefix_4 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 4 226192367166552644 = some 226192367166552644 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 2 2 226192367166552644 226192367166552644 226192367166552644 endpoint_10_57_window_0 endpoint_10_57_window_2
private theorem endpoint_10_57_window_4 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 4 2 226192367166552644 = some 226192367166552644 := by decide +kernel
private theorem endpoint_10_57_prefix_6 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 6 226192367166552644 = some 226192367166552644 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 4 2 226192367166552644 226192367166552644 226192367166552644 endpoint_10_57_prefix_4 endpoint_10_57_window_4
private theorem endpoint_10_57_window_6 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 6 2 226192367166552644 = some 226192367166552644 := by decide +kernel
private theorem endpoint_10_57_prefix_8 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 8 226192367166552644 = some 226192367166552644 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 6 2 226192367166552644 226192367166552644 226192367166552644 endpoint_10_57_prefix_6 endpoint_10_57_window_6
private theorem endpoint_10_57_window_8 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 8 1 226192367166552644 = some 226192367166552644 := by decide +kernel
private theorem endpoint_10_57_prefix_9 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 9 226192367166552644 = some 226192367166552644 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 8 1 226192367166552644 226192367166552644 226192367166552644 endpoint_10_57_prefix_8 endpoint_10_57_window_8

def endpoint_10_57 : CertifiedEndpoint :=
  ⟨⟨10, 57, 3138⟩, 226192367166552644, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_57_flag endpoint_10_57_sources 9 226192367166552644 226192367166552644 rfl endpoint_10_57_base endpoint_10_57_prefix_9) (by decide)⟩
private def endpoint_10_58_flag : Flag := ⟨10, 58, 3099⟩
private def endpoint_10_58_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_58_base : receiptBase endpoint_10_58_flag endpoint_10_58_sources = some 226818304758078468 := by decide +kernel
private theorem endpoint_10_58_window_0 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 2 226818304758078468 = some 226818304758078468 := by decide +kernel
private theorem endpoint_10_58_window_2 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 2 2 226818304758078468 = some 226818304758078468 := by decide +kernel
private theorem endpoint_10_58_prefix_4 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 4 226818304758078468 = some 226818304758078468 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 2 2 226818304758078468 226818304758078468 226818304758078468 endpoint_10_58_window_0 endpoint_10_58_window_2
private theorem endpoint_10_58_window_4 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 4 2 226818304758078468 = some 226818304758078468 := by decide +kernel
private theorem endpoint_10_58_prefix_6 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 6 226818304758078468 = some 226818304758078468 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 4 2 226818304758078468 226818304758078468 226818304758078468 endpoint_10_58_prefix_4 endpoint_10_58_window_4
private theorem endpoint_10_58_window_6 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 6 2 226818304758078468 = some 226818304758078468 := by decide +kernel
private theorem endpoint_10_58_prefix_8 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 8 226818304758078468 = some 226818304758078468 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 6 2 226818304758078468 226818304758078468 226818304758078468 endpoint_10_58_prefix_6 endpoint_10_58_window_6
private theorem endpoint_10_58_window_8 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 8 1 226818304758078468 = some 226818304758078468 := by decide +kernel
private theorem endpoint_10_58_prefix_9 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 9 226818304758078468 = some 226818304758078468 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 8 1 226818304758078468 226818304758078468 226818304758078468 endpoint_10_58_prefix_8 endpoint_10_58_window_8

def endpoint_10_58 : CertifiedEndpoint :=
  ⟨⟨10, 58, 3099⟩, 226818304758078468, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_58_flag endpoint_10_58_sources 9 226818304758078468 226818304758078468 rfl endpoint_10_58_base endpoint_10_58_prefix_9) (by decide)⟩
private def endpoint_10_59_flag : Flag := ⟨10, 59, 3058⟩
private def endpoint_10_59_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_59_base : receiptBase endpoint_10_59_flag endpoint_10_59_sources = some 227211567305353337 := by decide +kernel
private theorem endpoint_10_59_window_0 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 2 227211567305353337 = some 227211567305353337 := by decide +kernel
private theorem endpoint_10_59_window_2 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 2 2 227211567305353337 = some 227211567305353337 := by decide +kernel
private theorem endpoint_10_59_prefix_4 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 4 227211567305353337 = some 227211567305353337 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 2 2 227211567305353337 227211567305353337 227211567305353337 endpoint_10_59_window_0 endpoint_10_59_window_2
private theorem endpoint_10_59_window_4 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 4 2 227211567305353337 = some 227211567305353337 := by decide +kernel
private theorem endpoint_10_59_prefix_6 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 6 227211567305353337 = some 227211567305353337 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 4 2 227211567305353337 227211567305353337 227211567305353337 endpoint_10_59_prefix_4 endpoint_10_59_window_4
private theorem endpoint_10_59_window_6 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 6 2 227211567305353337 = some 227211567305353337 := by decide +kernel
private theorem endpoint_10_59_prefix_8 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 8 227211567305353337 = some 227211567305353337 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 6 2 227211567305353337 227211567305353337 227211567305353337 endpoint_10_59_prefix_6 endpoint_10_59_window_6
private theorem endpoint_10_59_window_8 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 8 1 227211567305353337 = some 227211567305353337 := by decide +kernel
private theorem endpoint_10_59_prefix_9 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 9 227211567305353337 = some 227211567305353337 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 8 1 227211567305353337 227211567305353337 227211567305353337 endpoint_10_59_prefix_8 endpoint_10_59_window_8

def endpoint_10_59 : CertifiedEndpoint :=
  ⟨⟨10, 59, 3058⟩, 227211567305353337, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_59_flag endpoint_10_59_sources 9 227211567305353337 227211567305353337 rfl endpoint_10_59_base endpoint_10_59_prefix_9) (by decide)⟩
private def endpoint_10_60_flag : Flag := ⟨10, 60, 3016⟩
private def endpoint_10_60_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_60_base : receiptBase endpoint_10_60_flag endpoint_10_60_sources = some 227440066563834709 := by decide +kernel
private theorem endpoint_10_60_window_0 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 2 227440066563834709 = some 227440066563834709 := by decide +kernel
private theorem endpoint_10_60_window_2 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 2 2 227440066563834709 = some 227440066563834709 := by decide +kernel
private theorem endpoint_10_60_prefix_4 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 4 227440066563834709 = some 227440066563834709 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 2 2 227440066563834709 227440066563834709 227440066563834709 endpoint_10_60_window_0 endpoint_10_60_window_2
private theorem endpoint_10_60_window_4 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 4 2 227440066563834709 = some 227440066563834709 := by decide +kernel
private theorem endpoint_10_60_prefix_6 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 6 227440066563834709 = some 227440066563834709 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 4 2 227440066563834709 227440066563834709 227440066563834709 endpoint_10_60_prefix_4 endpoint_10_60_window_4
private theorem endpoint_10_60_window_6 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 6 2 227440066563834709 = some 227440066563834709 := by decide +kernel
private theorem endpoint_10_60_prefix_8 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 8 227440066563834709 = some 227440066563834709 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 6 2 227440066563834709 227440066563834709 227440066563834709 endpoint_10_60_prefix_6 endpoint_10_60_window_6
private theorem endpoint_10_60_window_8 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 8 1 227440066563834709 = some 227440066563834709 := by decide +kernel
private theorem endpoint_10_60_prefix_9 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 9 227440066563834709 = some 227440066563834709 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 8 1 227440066563834709 227440066563834709 227440066563834709 endpoint_10_60_prefix_8 endpoint_10_60_window_8

def endpoint_10_60 : CertifiedEndpoint :=
  ⟨⟨10, 60, 3016⟩, 227440066563834709, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_60_flag endpoint_10_60_sources 9 227440066563834709 227440066563834709 rfl endpoint_10_60_base endpoint_10_60_prefix_9) (by decide)⟩
private def endpoint_10_61_flag : Flag := ⟨10, 61, 2972⟩
private def endpoint_10_61_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_61_base : receiptBase endpoint_10_61_flag endpoint_10_61_sources = some 227425008583308268 := by decide +kernel
private theorem endpoint_10_61_window_0 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 2 227425008583308268 = some 227425008583308268 := by decide +kernel
private theorem endpoint_10_61_window_2 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 2 2 227425008583308268 = some 227425008583308268 := by decide +kernel
private theorem endpoint_10_61_prefix_4 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 4 227425008583308268 = some 227425008583308268 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 2 2 227425008583308268 227425008583308268 227425008583308268 endpoint_10_61_window_0 endpoint_10_61_window_2
private theorem endpoint_10_61_window_4 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 4 2 227425008583308268 = some 227425008583308268 := by decide +kernel
private theorem endpoint_10_61_prefix_6 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 6 227425008583308268 = some 227425008583308268 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 4 2 227425008583308268 227425008583308268 227425008583308268 endpoint_10_61_prefix_4 endpoint_10_61_window_4
private theorem endpoint_10_61_window_6 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 6 2 227425008583308268 = some 227425008583308268 := by decide +kernel
private theorem endpoint_10_61_prefix_8 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 8 227425008583308268 = some 227425008583308268 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 6 2 227425008583308268 227425008583308268 227425008583308268 endpoint_10_61_prefix_6 endpoint_10_61_window_6
private theorem endpoint_10_61_window_8 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 8 1 227425008583308268 = some 227425008583308268 := by decide +kernel
private theorem endpoint_10_61_prefix_9 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 9 227425008583308268 = some 227425008583308268 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 8 1 227425008583308268 227425008583308268 227425008583308268 endpoint_10_61_prefix_8 endpoint_10_61_window_8

def endpoint_10_61 : CertifiedEndpoint :=
  ⟨⟨10, 61, 2972⟩, 227425008583308268, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_61_flag endpoint_10_61_sources 9 227425008583308268 227425008583308268 rfl endpoint_10_61_base endpoint_10_61_prefix_9) (by decide)⟩
private def endpoint_10_62_flag : Flag := ⟨10, 62, 2926⟩
private def endpoint_10_62_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_10_62_base : receiptBase endpoint_10_62_flag endpoint_10_62_sources = some 228316012349080696 := by decide +kernel
private theorem endpoint_10_62_window_0 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 2 228316012349080696 = some 228316012349080696 := by decide +kernel
private theorem endpoint_10_62_window_2 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 2 2 228316012349080696 = some 228316012349080696 := by decide +kernel
private theorem endpoint_10_62_prefix_4 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 4 228316012349080696 = some 228316012349080696 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 2 2 228316012349080696 228316012349080696 228316012349080696 endpoint_10_62_window_0 endpoint_10_62_window_2
private theorem endpoint_10_62_window_4 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 4 2 228316012349080696 = some 228316012349080696 := by decide +kernel
private theorem endpoint_10_62_prefix_6 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 6 228316012349080696 = some 228316012349080696 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 4 2 228316012349080696 228316012349080696 228316012349080696 endpoint_10_62_prefix_4 endpoint_10_62_window_4
private theorem endpoint_10_62_window_6 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 6 2 228316012349080696 = some 228316012349080696 := by decide +kernel
private theorem endpoint_10_62_prefix_8 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 8 228316012349080696 = some 228316012349080696 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 6 2 228316012349080696 228316012349080696 228316012349080696 endpoint_10_62_prefix_6 endpoint_10_62_window_6
private theorem endpoint_10_62_window_8 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 8 1 228316012349080696 = some 228316012349080696 := by decide +kernel
private theorem endpoint_10_62_prefix_9 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 9 228316012349080696 = some 228316012349080696 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 8 1 228316012349080696 228316012349080696 228316012349080696 endpoint_10_62_prefix_8 endpoint_10_62_window_8

def endpoint_10_62 : CertifiedEndpoint :=
  ⟨⟨10, 62, 2926⟩, 228316012349080696, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_10_62_flag endpoint_10_62_sources 9 228316012349080696 228316012349080696 rfl endpoint_10_62_base endpoint_10_62_prefix_9) (by decide)⟩
private def endpoint_10_63_flag : Flag := ⟨10, 63, 2878⟩
private def endpoint_10_63_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_10_63_base : receiptBase endpoint_10_63_flag endpoint_10_63_sources = some 227793638897230027 := by decide +kernel
private theorem endpoint_10_63_window_0 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 2 227793638897230027 = some 227793638897230027 := by decide +kernel
private theorem endpoint_10_63_window_2 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 2 2 227793638897230027 = some 227793638897230027 := by decide +kernel
private theorem endpoint_10_63_prefix_4 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 4 227793638897230027 = some 227793638897230027 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 2 2 227793638897230027 227793638897230027 227793638897230027 endpoint_10_63_window_0 endpoint_10_63_window_2
private theorem endpoint_10_63_window_4 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 4 2 227793638897230027 = some 227793638897230027 := by decide +kernel
private theorem endpoint_10_63_prefix_6 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 6 227793638897230027 = some 227793638897230027 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 4 2 227793638897230027 227793638897230027 227793638897230027 endpoint_10_63_prefix_4 endpoint_10_63_window_4
private theorem endpoint_10_63_window_6 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 6 2 227793638897230027 = some 227793638897230027 := by decide +kernel
private theorem endpoint_10_63_prefix_8 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 8 227793638897230027 = some 227793638897230027 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 6 2 227793638897230027 227793638897230027 227793638897230027 endpoint_10_63_prefix_6 endpoint_10_63_window_6
private theorem endpoint_10_63_window_8 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 8 1 227793638897230027 = some 227793638897230027 := by decide +kernel
private theorem endpoint_10_63_prefix_9 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 9 227793638897230027 = some 227793638897230027 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 8 1 227793638897230027 227793638897230027 227793638897230027 endpoint_10_63_prefix_8 endpoint_10_63_window_8

def endpoint_10_63 : CertifiedEndpoint :=
  ⟨⟨10, 63, 2878⟩, 227793638897230027, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_10_63_flag endpoint_10_63_sources 9 227793638897230027 227793638897230027 rfl endpoint_10_63_base endpoint_10_63_prefix_9) (by decide)⟩
private def endpoint_10_64_flag : Flag := ⟨10, 64, 2828⟩
private def endpoint_10_64_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_10_64_base : receiptBase endpoint_10_64_flag endpoint_10_64_sources = some 228214517209994608 := by decide +kernel
private theorem endpoint_10_64_window_0 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 2 228214517209994608 = some 228214517209994608 := by decide +kernel
private theorem endpoint_10_64_window_2 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 2 2 228214517209994608 = some 228214517209994608 := by decide +kernel
private theorem endpoint_10_64_prefix_4 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 4 228214517209994608 = some 228214517209994608 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 2 2 228214517209994608 228214517209994608 228214517209994608 endpoint_10_64_window_0 endpoint_10_64_window_2
private theorem endpoint_10_64_window_4 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 4 2 228214517209994608 = some 228214517209994608 := by decide +kernel
private theorem endpoint_10_64_prefix_6 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 6 228214517209994608 = some 228214517209994608 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 4 2 228214517209994608 228214517209994608 228214517209994608 endpoint_10_64_prefix_4 endpoint_10_64_window_4
private theorem endpoint_10_64_window_6 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 6 2 228214517209994608 = some 228214517209994608 := by decide +kernel
private theorem endpoint_10_64_prefix_8 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 8 228214517209994608 = some 228214517209994608 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 6 2 228214517209994608 228214517209994608 228214517209994608 endpoint_10_64_prefix_6 endpoint_10_64_window_6
private theorem endpoint_10_64_window_8 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 8 1 228214517209994608 = some 228214517209994608 := by decide +kernel
private theorem endpoint_10_64_prefix_9 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 9 228214517209994608 = some 228214517209994608 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 8 1 228214517209994608 228214517209994608 228214517209994608 endpoint_10_64_prefix_8 endpoint_10_64_window_8

def endpoint_10_64 : CertifiedEndpoint :=
  ⟨⟨10, 64, 2828⟩, 228214517209994608, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_10_64_flag endpoint_10_64_sources 9 228214517209994608 228214517209994608 rfl endpoint_10_64_base endpoint_10_64_prefix_9) (by decide)⟩
private def endpoint_10_65_flag : Flag := ⟨10, 65, 2775⟩
private def endpoint_10_65_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_10_65_base : receiptBase endpoint_10_65_flag endpoint_10_65_sources = some 227071418127595034 := by decide +kernel
private theorem endpoint_10_65_window_0 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 2 227071418127595034 = some 227071418127595034 := by decide +kernel
private theorem endpoint_10_65_window_2 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 2 2 227071418127595034 = some 227071418127595034 := by decide +kernel
private theorem endpoint_10_65_prefix_4 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 4 227071418127595034 = some 227071418127595034 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 2 2 227071418127595034 227071418127595034 227071418127595034 endpoint_10_65_window_0 endpoint_10_65_window_2
private theorem endpoint_10_65_window_4 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 4 2 227071418127595034 = some 227071418127595034 := by decide +kernel
private theorem endpoint_10_65_prefix_6 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 6 227071418127595034 = some 227071418127595034 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 4 2 227071418127595034 227071418127595034 227071418127595034 endpoint_10_65_prefix_4 endpoint_10_65_window_4
private theorem endpoint_10_65_window_6 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 6 2 227071418127595034 = some 227071418127595034 := by decide +kernel
private theorem endpoint_10_65_prefix_8 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 8 227071418127595034 = some 227071418127595034 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 6 2 227071418127595034 227071418127595034 227071418127595034 endpoint_10_65_prefix_6 endpoint_10_65_window_6
private theorem endpoint_10_65_window_8 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 8 1 227071418127595034 = some 227071418127595034 := by decide +kernel
private theorem endpoint_10_65_prefix_9 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 9 227071418127595034 = some 227071418127595034 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 8 1 227071418127595034 227071418127595034 227071418127595034 endpoint_10_65_prefix_8 endpoint_10_65_window_8

def endpoint_10_65 : CertifiedEndpoint :=
  ⟨⟨10, 65, 2775⟩, 227071418127595034, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_10_65_flag endpoint_10_65_sources 9 227071418127595034 227071418127595034 rfl endpoint_10_65_base endpoint_10_65_prefix_9) (by decide)⟩
private def endpoint_10_66_flag : Flag := ⟨10, 66, 2719⟩
private def endpoint_10_66_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_10_66_base : receiptBase endpoint_10_66_flag endpoint_10_66_sources = some 226809476938221126 := by decide +kernel
private theorem endpoint_10_66_window_0 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 2 226809476938221126 = some 226809476938221126 := by decide +kernel
private theorem endpoint_10_66_window_2 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 2 2 226809476938221126 = some 226809476938221126 := by decide +kernel
private theorem endpoint_10_66_prefix_4 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 4 226809476938221126 = some 226809476938221126 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 2 2 226809476938221126 226809476938221126 226809476938221126 endpoint_10_66_window_0 endpoint_10_66_window_2
private theorem endpoint_10_66_window_4 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 4 2 226809476938221126 = some 226809476938221126 := by decide +kernel
private theorem endpoint_10_66_prefix_6 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 6 226809476938221126 = some 226809476938221126 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 4 2 226809476938221126 226809476938221126 226809476938221126 endpoint_10_66_prefix_4 endpoint_10_66_window_4
private theorem endpoint_10_66_window_6 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 6 2 226809476938221126 = some 226809476938221126 := by decide +kernel
private theorem endpoint_10_66_prefix_8 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 8 226809476938221126 = some 226809476938221126 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 6 2 226809476938221126 226809476938221126 226809476938221126 endpoint_10_66_prefix_6 endpoint_10_66_window_6
private theorem endpoint_10_66_window_8 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 8 1 226809476938221126 = some 226809476938221126 := by decide +kernel
private theorem endpoint_10_66_prefix_9 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 9 226809476938221126 = some 226809476938221126 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 8 1 226809476938221126 226809476938221126 226809476938221126 endpoint_10_66_prefix_8 endpoint_10_66_window_8

def endpoint_10_66 : CertifiedEndpoint :=
  ⟨⟨10, 66, 2719⟩, 226809476938221126, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_10_66_flag endpoint_10_66_sources 9 226809476938221126 226809476938221126 rfl endpoint_10_66_base endpoint_10_66_prefix_9) (by decide)⟩
private def endpoint_10_67_flag : Flag := ⟨10, 67, 2661⟩
private def endpoint_10_67_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_10_67_base : receiptBase endpoint_10_67_flag endpoint_10_67_sources = some 226276942503114348 := by decide +kernel
private theorem endpoint_10_67_window_0 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 2 226276942503114348 = some 226276942503114348 := by decide +kernel
private theorem endpoint_10_67_window_2 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 2 2 226276942503114348 = some 226276942503114348 := by decide +kernel
private theorem endpoint_10_67_prefix_4 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 4 226276942503114348 = some 226276942503114348 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 2 2 226276942503114348 226276942503114348 226276942503114348 endpoint_10_67_window_0 endpoint_10_67_window_2
private theorem endpoint_10_67_window_4 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 4 2 226276942503114348 = some 226276942503114348 := by decide +kernel
private theorem endpoint_10_67_prefix_6 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 6 226276942503114348 = some 226276942503114348 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 4 2 226276942503114348 226276942503114348 226276942503114348 endpoint_10_67_prefix_4 endpoint_10_67_window_4
private theorem endpoint_10_67_window_6 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 6 2 226276942503114348 = some 226276942503114348 := by decide +kernel
private theorem endpoint_10_67_prefix_8 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 8 226276942503114348 = some 226276942503114348 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 6 2 226276942503114348 226276942503114348 226276942503114348 endpoint_10_67_prefix_6 endpoint_10_67_window_6
private theorem endpoint_10_67_window_8 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 8 1 226276942503114348 = some 226276942503114348 := by decide +kernel
private theorem endpoint_10_67_prefix_9 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 9 226276942503114348 = some 226276942503114348 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 8 1 226276942503114348 226276942503114348 226276942503114348 endpoint_10_67_prefix_8 endpoint_10_67_window_8

def endpoint_10_67 : CertifiedEndpoint :=
  ⟨⟨10, 67, 2661⟩, 226276942503114348, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_10_67_flag endpoint_10_67_sources 9 226276942503114348 226276942503114348 rfl endpoint_10_67_base endpoint_10_67_prefix_9) (by decide)⟩
private def endpoint_10_68_flag : Flag := ⟨10, 68, 2600⟩
private def endpoint_10_68_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_68_base : receiptBase endpoint_10_68_flag endpoint_10_68_sources = some 225229623366754603 := by decide +kernel
private theorem endpoint_10_68_window_0 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 2 225229623366754603 = some 225229623366754603 := by decide +kernel
private theorem endpoint_10_68_window_2 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 2 2 225229623366754603 = some 225229623366754603 := by decide +kernel
private theorem endpoint_10_68_prefix_4 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 4 225229623366754603 = some 225229623366754603 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 2 2 225229623366754603 225229623366754603 225229623366754603 endpoint_10_68_window_0 endpoint_10_68_window_2
private theorem endpoint_10_68_window_4 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 4 2 225229623366754603 = some 225229623366754603 := by decide +kernel
private theorem endpoint_10_68_prefix_6 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 6 225229623366754603 = some 225229623366754603 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 4 2 225229623366754603 225229623366754603 225229623366754603 endpoint_10_68_prefix_4 endpoint_10_68_window_4
private theorem endpoint_10_68_window_6 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 6 2 225229623366754603 = some 225229623366754603 := by decide +kernel
private theorem endpoint_10_68_prefix_8 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 8 225229623366754603 = some 225229623366754603 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 6 2 225229623366754603 225229623366754603 225229623366754603 endpoint_10_68_prefix_6 endpoint_10_68_window_6
private theorem endpoint_10_68_window_8 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 8 1 225229623366754603 = some 225229623366754603 := by decide +kernel
private theorem endpoint_10_68_prefix_9 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 9 225229623366754603 = some 225229623366754603 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 8 1 225229623366754603 225229623366754603 225229623366754603 endpoint_10_68_prefix_8 endpoint_10_68_window_8

def endpoint_10_68 : CertifiedEndpoint :=
  ⟨⟨10, 68, 2600⟩, 225229623366754603, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_68_flag endpoint_10_68_sources 9 225229623366754603 225229623366754603 rfl endpoint_10_68_base endpoint_10_68_prefix_9) (by decide)⟩
private def endpoint_10_69_flag : Flag := ⟨10, 69, 2537⟩
private def endpoint_10_69_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_69_base : receiptBase endpoint_10_69_flag endpoint_10_69_sources = some 222705126810654351 := by decide +kernel
private theorem endpoint_10_69_window_0 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 2 222705126810654351 = some 222705126810654351 := by decide +kernel
private theorem endpoint_10_69_window_2 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 2 2 222705126810654351 = some 222705126810654351 := by decide +kernel
private theorem endpoint_10_69_prefix_4 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 4 222705126810654351 = some 222705126810654351 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 2 2 222705126810654351 222705126810654351 222705126810654351 endpoint_10_69_window_0 endpoint_10_69_window_2
private theorem endpoint_10_69_window_4 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 4 2 222705126810654351 = some 222705126810654351 := by decide +kernel
private theorem endpoint_10_69_prefix_6 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 6 222705126810654351 = some 222705126810654351 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 4 2 222705126810654351 222705126810654351 222705126810654351 endpoint_10_69_prefix_4 endpoint_10_69_window_4
private theorem endpoint_10_69_window_6 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 6 2 222705126810654351 = some 222705126810654351 := by decide +kernel
private theorem endpoint_10_69_prefix_8 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 8 222705126810654351 = some 222705126810654351 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 6 2 222705126810654351 222705126810654351 222705126810654351 endpoint_10_69_prefix_6 endpoint_10_69_window_6
private theorem endpoint_10_69_window_8 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 8 1 222705126810654351 = some 222705126810654351 := by decide +kernel
private theorem endpoint_10_69_prefix_9 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 9 222705126810654351 = some 222705126810654351 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 8 1 222705126810654351 222705126810654351 222705126810654351 endpoint_10_69_prefix_8 endpoint_10_69_window_8

def endpoint_10_69 : CertifiedEndpoint :=
  ⟨⟨10, 69, 2537⟩, 222705126810654351, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_69_flag endpoint_10_69_sources 9 222705126810654351 222705126810654351 rfl endpoint_10_69_base endpoint_10_69_prefix_9) (by decide)⟩
private def endpoint_10_70_flag : Flag := ⟨10, 70, 2471⟩
private def endpoint_10_70_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_70_base : receiptBase endpoint_10_70_flag endpoint_10_70_sources = some 219772690522187555 := by decide +kernel
private theorem endpoint_10_70_window_0 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 2 219772690522187555 = some 219772690522187555 := by decide +kernel
private theorem endpoint_10_70_window_2 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 2 2 219772690522187555 = some 219772690522187555 := by decide +kernel
private theorem endpoint_10_70_prefix_4 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 4 219772690522187555 = some 219772690522187555 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 2 2 219772690522187555 219772690522187555 219772690522187555 endpoint_10_70_window_0 endpoint_10_70_window_2
private theorem endpoint_10_70_window_4 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 4 2 219772690522187555 = some 219772690522187555 := by decide +kernel
private theorem endpoint_10_70_prefix_6 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 6 219772690522187555 = some 219772690522187555 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 4 2 219772690522187555 219772690522187555 219772690522187555 endpoint_10_70_prefix_4 endpoint_10_70_window_4
private theorem endpoint_10_70_window_6 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 6 2 219772690522187555 = some 219772690522187555 := by decide +kernel
private theorem endpoint_10_70_prefix_8 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 8 219772690522187555 = some 219772690522187555 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 6 2 219772690522187555 219772690522187555 219772690522187555 endpoint_10_70_prefix_6 endpoint_10_70_window_6
private theorem endpoint_10_70_window_8 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 8 1 219772690522187555 = some 219772690522187555 := by decide +kernel
private theorem endpoint_10_70_prefix_9 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 9 219772690522187555 = some 219772690522187555 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 8 1 219772690522187555 219772690522187555 219772690522187555 endpoint_10_70_prefix_8 endpoint_10_70_window_8

def endpoint_10_70 : CertifiedEndpoint :=
  ⟨⟨10, 70, 2471⟩, 219772690522187555, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_70_flag endpoint_10_70_sources 9 219772690522187555 219772690522187555 rfl endpoint_10_70_base endpoint_10_70_prefix_9) (by decide)⟩

def endpointBlock05 : List CertifiedEndpoint := [
  endpoint_9_66, endpoint_9_67, endpoint_9_68, endpoint_9_69, endpoint_9_70, endpoint_9_71,
  endpoint_9_72, endpoint_9_73, endpoint_9_74, endpoint_9_75, endpoint_9_76, endpoint_9_77,
  endpoint_9_78, endpoint_9_79, endpoint_9_80, endpoint_9_81, endpoint_9_82, endpoint_9_83,
  endpoint_9_84, endpoint_9_85, endpoint_9_86, endpoint_9_87, endpoint_9_88, endpoint_9_89,
  endpoint_9_90, endpoint_9_91, endpoint_9_92, endpoint_9_93, endpoint_9_94, endpoint_9_95,
  endpoint_10_10, endpoint_10_11, endpoint_10_12, endpoint_10_13, endpoint_10_14, endpoint_10_15,
  endpoint_10_16, endpoint_10_17, endpoint_10_18, endpoint_10_19, endpoint_10_20, endpoint_10_21,
  endpoint_10_22, endpoint_10_23, endpoint_10_24, endpoint_10_25, endpoint_10_26, endpoint_10_27,
  endpoint_10_28, endpoint_10_29, endpoint_10_30, endpoint_10_31, endpoint_10_32, endpoint_10_33,
  endpoint_10_34, endpoint_10_35, endpoint_10_36, endpoint_10_37, endpoint_10_38, endpoint_10_39,
  endpoint_10_40, endpoint_10_41, endpoint_10_42, endpoint_10_43, endpoint_10_44, endpoint_10_45,
  endpoint_10_46, endpoint_10_47, endpoint_10_48, endpoint_10_49, endpoint_10_50, endpoint_10_51,
  endpoint_10_52, endpoint_10_53, endpoint_10_54, endpoint_10_55, endpoint_10_56, endpoint_10_57,
  endpoint_10_58, endpoint_10_59, endpoint_10_60, endpoint_10_61, endpoint_10_62, endpoint_10_63,
  endpoint_10_64, endpoint_10_65, endpoint_10_66, endpoint_10_67, endpoint_10_68, endpoint_10_69,
  endpoint_10_70
]

end ProximityPrize.SubmissionLower.Koala6844Receipts
