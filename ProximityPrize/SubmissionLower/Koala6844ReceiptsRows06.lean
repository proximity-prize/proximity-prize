import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


private def endpoint_10_71_flag : Flag := ⟨10, 71, 2402⟩
private def endpoint_10_71_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_71_base : receiptBase endpoint_10_71_flag endpoint_10_71_sources = some 216422115520609120 := by decide +kernel
private theorem endpoint_10_71_window_0 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 2 216422115520609120 = some 216422115520609120 := by decide +kernel
private theorem endpoint_10_71_window_2 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 2 2 216422115520609120 = some 216422115520609120 := by decide +kernel
private theorem endpoint_10_71_prefix_4 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 4 216422115520609120 = some 216422115520609120 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 2 2 216422115520609120 216422115520609120 216422115520609120 endpoint_10_71_window_0 endpoint_10_71_window_2
private theorem endpoint_10_71_window_4 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 4 2 216422115520609120 = some 216422115520609120 := by decide +kernel
private theorem endpoint_10_71_prefix_6 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 6 216422115520609120 = some 216422115520609120 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 4 2 216422115520609120 216422115520609120 216422115520609120 endpoint_10_71_prefix_4 endpoint_10_71_window_4
private theorem endpoint_10_71_window_6 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 6 2 216422115520609120 = some 216422115520609120 := by decide +kernel
private theorem endpoint_10_71_prefix_8 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 8 216422115520609120 = some 216422115520609120 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 6 2 216422115520609120 216422115520609120 216422115520609120 endpoint_10_71_prefix_6 endpoint_10_71_window_6
private theorem endpoint_10_71_window_8 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 8 1 216422115520609120 = some 216422115520609120 := by decide +kernel
private theorem endpoint_10_71_prefix_9 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 9 216422115520609120 = some 216422115520609120 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 8 1 216422115520609120 216422115520609120 216422115520609120 endpoint_10_71_prefix_8 endpoint_10_71_window_8

def endpoint_10_71 : CertifiedEndpoint :=
  ⟨⟨10, 71, 2402⟩, 216422115520609120, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_71_flag endpoint_10_71_sources 9 216422115520609120 216422115520609120 rfl endpoint_10_71_base endpoint_10_71_prefix_9) (by decide)⟩
private def endpoint_10_72_flag : Flag := ⟨10, 72, 2331⟩
private def endpoint_10_72_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_10_72_base : receiptBase endpoint_10_72_flag endpoint_10_72_sources = some 217390836170234411 := by decide +kernel
private theorem endpoint_10_72_window_0 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 2 217390836170234411 = some 217390836170234411 := by decide +kernel
private theorem endpoint_10_72_window_2 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 2 2 217390836170234411 = some 217390836170234411 := by decide +kernel
private theorem endpoint_10_72_prefix_4 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 4 217390836170234411 = some 217390836170234411 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 2 2 217390836170234411 217390836170234411 217390836170234411 endpoint_10_72_window_0 endpoint_10_72_window_2
private theorem endpoint_10_72_window_4 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 4 2 217390836170234411 = some 217390836170234411 := by decide +kernel
private theorem endpoint_10_72_prefix_6 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 6 217390836170234411 = some 217390836170234411 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 4 2 217390836170234411 217390836170234411 217390836170234411 endpoint_10_72_prefix_4 endpoint_10_72_window_4
private theorem endpoint_10_72_window_6 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 6 2 217390836170234411 = some 217390836170234411 := by decide +kernel
private theorem endpoint_10_72_prefix_8 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 8 217390836170234411 = some 217390836170234411 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 6 2 217390836170234411 217390836170234411 217390836170234411 endpoint_10_72_prefix_6 endpoint_10_72_window_6
private theorem endpoint_10_72_window_8 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 8 1 217390836170234411 = some 217390836170234411 := by decide +kernel
private theorem endpoint_10_72_prefix_9 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 9 217390836170234411 = some 217390836170234411 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 8 1 217390836170234411 217390836170234411 217390836170234411 endpoint_10_72_prefix_8 endpoint_10_72_window_8

def endpoint_10_72 : CertifiedEndpoint :=
  ⟨⟨10, 72, 2331⟩, 217390836170234411, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_10_72_flag endpoint_10_72_sources 9 217390836170234411 217390836170234411 rfl endpoint_10_72_base endpoint_10_72_prefix_9) (by decide)⟩
private def endpoint_10_73_flag : Flag := ⟨10, 73, 2257⟩
private def endpoint_10_73_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_10_73_base : receiptBase endpoint_10_73_flag endpoint_10_73_sources = some 213228527067040670 := by decide +kernel
private theorem endpoint_10_73_window_0 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 2 213228527067040670 = some 213228527067040670 := by decide +kernel
private theorem endpoint_10_73_window_2 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 2 2 213228527067040670 = some 213228527067040670 := by decide +kernel
private theorem endpoint_10_73_prefix_4 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 4 213228527067040670 = some 213228527067040670 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 2 2 213228527067040670 213228527067040670 213228527067040670 endpoint_10_73_window_0 endpoint_10_73_window_2
private theorem endpoint_10_73_window_4 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 4 2 213228527067040670 = some 213228527067040670 := by decide +kernel
private theorem endpoint_10_73_prefix_6 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 6 213228527067040670 = some 213228527067040670 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 4 2 213228527067040670 213228527067040670 213228527067040670 endpoint_10_73_prefix_4 endpoint_10_73_window_4
private theorem endpoint_10_73_window_6 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 6 2 213228527067040670 = some 213228527067040670 := by decide +kernel
private theorem endpoint_10_73_prefix_8 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 8 213228527067040670 = some 213228527067040670 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 6 2 213228527067040670 213228527067040670 213228527067040670 endpoint_10_73_prefix_6 endpoint_10_73_window_6
private theorem endpoint_10_73_window_8 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 8 1 213228527067040670 = some 213228527067040670 := by decide +kernel
private theorem endpoint_10_73_prefix_9 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 9 213228527067040670 = some 213228527067040670 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 8 1 213228527067040670 213228527067040670 213228527067040670 endpoint_10_73_prefix_8 endpoint_10_73_window_8

def endpoint_10_73 : CertifiedEndpoint :=
  ⟨⟨10, 73, 2257⟩, 213228527067040670, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_10_73_flag endpoint_10_73_sources 9 213228527067040670 213228527067040670 rfl endpoint_10_73_base endpoint_10_73_prefix_9) (by decide)⟩
private def endpoint_10_74_flag : Flag := ⟨10, 74, 2181⟩
private def endpoint_10_74_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_10_74_base : receiptBase endpoint_10_74_flag endpoint_10_74_sources = some 208709861764168773 := by decide +kernel
private theorem endpoint_10_74_window_0 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 2 208709861764168773 = some 208709861764168773 := by decide +kernel
private theorem endpoint_10_74_window_2 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 2 2 208709861764168773 = some 208709861764168773 := by decide +kernel
private theorem endpoint_10_74_prefix_4 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 4 208709861764168773 = some 208709861764168773 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 2 2 208709861764168773 208709861764168773 208709861764168773 endpoint_10_74_window_0 endpoint_10_74_window_2
private theorem endpoint_10_74_window_4 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 4 2 208709861764168773 = some 208709861764168773 := by decide +kernel
private theorem endpoint_10_74_prefix_6 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 6 208709861764168773 = some 208709861764168773 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 4 2 208709861764168773 208709861764168773 208709861764168773 endpoint_10_74_prefix_4 endpoint_10_74_window_4
private theorem endpoint_10_74_window_6 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 6 2 208709861764168773 = some 208709861764168773 := by decide +kernel
private theorem endpoint_10_74_prefix_8 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 8 208709861764168773 = some 208709861764168773 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 6 2 208709861764168773 208709861764168773 208709861764168773 endpoint_10_74_prefix_6 endpoint_10_74_window_6
private theorem endpoint_10_74_window_8 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 8 1 208709861764168773 = some 208709861764168773 := by decide +kernel
private theorem endpoint_10_74_prefix_9 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 9 208709861764168773 = some 208709861764168773 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 8 1 208709861764168773 208709861764168773 208709861764168773 endpoint_10_74_prefix_8 endpoint_10_74_window_8

def endpoint_10_74 : CertifiedEndpoint :=
  ⟨⟨10, 74, 2181⟩, 208709861764168773, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_10_74_flag endpoint_10_74_sources 9 208709861764168773 208709861764168773 rfl endpoint_10_74_base endpoint_10_74_prefix_9) (by decide)⟩
private def endpoint_10_75_flag : Flag := ⟨10, 75, 2102⟩
private def endpoint_10_75_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_10_75_base : receiptBase endpoint_10_75_flag endpoint_10_75_sources = some 205270179209196778 := by decide +kernel
private theorem endpoint_10_75_window_0 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 2 205270179209196778 = some 205270179209196778 := by decide +kernel
private theorem endpoint_10_75_window_2 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 2 2 205270179209196778 = some 205270179209196778 := by decide +kernel
private theorem endpoint_10_75_prefix_4 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 4 205270179209196778 = some 205270179209196778 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 2 2 205270179209196778 205270179209196778 205270179209196778 endpoint_10_75_window_0 endpoint_10_75_window_2
private theorem endpoint_10_75_window_4 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 4 2 205270179209196778 = some 205270179209196778 := by decide +kernel
private theorem endpoint_10_75_prefix_6 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 6 205270179209196778 = some 205270179209196778 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 4 2 205270179209196778 205270179209196778 205270179209196778 endpoint_10_75_prefix_4 endpoint_10_75_window_4
private theorem endpoint_10_75_window_6 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 6 2 205270179209196778 = some 205270179209196778 := by decide +kernel
private theorem endpoint_10_75_prefix_8 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 8 205270179209196778 = some 205270179209196778 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 6 2 205270179209196778 205270179209196778 205270179209196778 endpoint_10_75_prefix_6 endpoint_10_75_window_6
private theorem endpoint_10_75_window_8 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 8 1 205270179209196778 = some 205270179209196778 := by decide +kernel
private theorem endpoint_10_75_prefix_9 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 9 205270179209196778 = some 205270179209196778 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 8 1 205270179209196778 205270179209196778 205270179209196778 endpoint_10_75_prefix_8 endpoint_10_75_window_8

def endpoint_10_75 : CertifiedEndpoint :=
  ⟨⟨10, 75, 2102⟩, 205270179209196778, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_10_75_flag endpoint_10_75_sources 9 205270179209196778 205270179209196778 rfl endpoint_10_75_base endpoint_10_75_prefix_9) (by decide)⟩
private def endpoint_10_76_flag : Flag := ⟨10, 76, 2020⟩
private def endpoint_10_76_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_10_76_base : receiptBase endpoint_10_76_flag endpoint_10_76_sources = some 199698091432593893 := by decide +kernel
private theorem endpoint_10_76_window_0 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 2 199698091432593893 = some 199698091432593893 := by decide +kernel
private theorem endpoint_10_76_window_2 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 2 2 199698091432593893 = some 199698091432593893 := by decide +kernel
private theorem endpoint_10_76_prefix_4 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 4 199698091432593893 = some 199698091432593893 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 2 2 199698091432593893 199698091432593893 199698091432593893 endpoint_10_76_window_0 endpoint_10_76_window_2
private theorem endpoint_10_76_window_4 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 4 2 199698091432593893 = some 199698091432593893 := by decide +kernel
private theorem endpoint_10_76_prefix_6 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 6 199698091432593893 = some 199698091432593893 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 4 2 199698091432593893 199698091432593893 199698091432593893 endpoint_10_76_prefix_4 endpoint_10_76_window_4
private theorem endpoint_10_76_window_6 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 6 2 199698091432593893 = some 199698091432593893 := by decide +kernel
private theorem endpoint_10_76_prefix_8 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 8 199698091432593893 = some 199698091432593893 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 6 2 199698091432593893 199698091432593893 199698091432593893 endpoint_10_76_prefix_6 endpoint_10_76_window_6
private theorem endpoint_10_76_window_8 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 8 1 199698091432593893 = some 199698091432593893 := by decide +kernel
private theorem endpoint_10_76_prefix_9 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 9 199698091432593893 = some 199698091432593893 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 8 1 199698091432593893 199698091432593893 199698091432593893 endpoint_10_76_prefix_8 endpoint_10_76_window_8

def endpoint_10_76 : CertifiedEndpoint :=
  ⟨⟨10, 76, 2020⟩, 199698091432593893, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_10_76_flag endpoint_10_76_sources 9 199698091432593893 199698091432593893 rfl endpoint_10_76_base endpoint_10_76_prefix_9) (by decide)⟩
private def endpoint_10_77_flag : Flag := ⟨10, 77, 1936⟩
private def endpoint_10_77_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_10_77_base : receiptBase endpoint_10_77_flag endpoint_10_77_sources = some 195463840059435779 := by decide +kernel
private theorem endpoint_10_77_window_0 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 2 195463840059435779 = some 195463840059435779 := by decide +kernel
private theorem endpoint_10_77_window_2 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 2 2 195463840059435779 = some 195463840059435779 := by decide +kernel
private theorem endpoint_10_77_prefix_4 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 4 195463840059435779 = some 195463840059435779 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 2 2 195463840059435779 195463840059435779 195463840059435779 endpoint_10_77_window_0 endpoint_10_77_window_2
private theorem endpoint_10_77_window_4 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 4 2 195463840059435779 = some 195463840059435779 := by decide +kernel
private theorem endpoint_10_77_prefix_6 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 6 195463840059435779 = some 195463840059435779 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 4 2 195463840059435779 195463840059435779 195463840059435779 endpoint_10_77_prefix_4 endpoint_10_77_window_4
private theorem endpoint_10_77_window_6 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 6 2 195463840059435779 = some 195463840059435779 := by decide +kernel
private theorem endpoint_10_77_prefix_8 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 8 195463840059435779 = some 195463840059435779 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 6 2 195463840059435779 195463840059435779 195463840059435779 endpoint_10_77_prefix_6 endpoint_10_77_window_6
private theorem endpoint_10_77_window_8 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 8 1 195463840059435779 = some 195463840059435779 := by decide +kernel
private theorem endpoint_10_77_prefix_9 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 9 195463840059435779 = some 195463840059435779 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 8 1 195463840059435779 195463840059435779 195463840059435779 endpoint_10_77_prefix_8 endpoint_10_77_window_8

def endpoint_10_77 : CertifiedEndpoint :=
  ⟨⟨10, 77, 1936⟩, 195463840059435779, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_10_77_flag endpoint_10_77_sources 9 195463840059435779 195463840059435779 rfl endpoint_10_77_base endpoint_10_77_prefix_9) (by decide)⟩
private def endpoint_10_78_flag : Flag := ⟨10, 78, 1848⟩
private def endpoint_10_78_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_10_78_base : receiptBase endpoint_10_78_flag endpoint_10_78_sources = some 190588738561059210 := by decide +kernel
private theorem endpoint_10_78_window_0 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 2 190588738561059210 = some 190588738561059210 := by decide +kernel
private theorem endpoint_10_78_window_2 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 2 2 190588738561059210 = some 190588738561059210 := by decide +kernel
private theorem endpoint_10_78_prefix_4 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 4 190588738561059210 = some 190588738561059210 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 2 2 190588738561059210 190588738561059210 190588738561059210 endpoint_10_78_window_0 endpoint_10_78_window_2
private theorem endpoint_10_78_window_4 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 4 2 190588738561059210 = some 190588738561059210 := by decide +kernel
private theorem endpoint_10_78_prefix_6 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 6 190588738561059210 = some 190588738561059210 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 4 2 190588738561059210 190588738561059210 190588738561059210 endpoint_10_78_prefix_4 endpoint_10_78_window_4
private theorem endpoint_10_78_window_6 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 6 2 190588738561059210 = some 190588738561059210 := by decide +kernel
private theorem endpoint_10_78_prefix_8 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 8 190588738561059210 = some 190588738561059210 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 6 2 190588738561059210 190588738561059210 190588738561059210 endpoint_10_78_prefix_6 endpoint_10_78_window_6
private theorem endpoint_10_78_window_8 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 8 1 190588738561059210 = some 190588738561059210 := by decide +kernel
private theorem endpoint_10_78_prefix_9 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 9 190588738561059210 = some 190588738561059210 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 8 1 190588738561059210 190588738561059210 190588738561059210 endpoint_10_78_prefix_8 endpoint_10_78_window_8

def endpoint_10_78 : CertifiedEndpoint :=
  ⟨⟨10, 78, 1848⟩, 190588738561059210, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_10_78_flag endpoint_10_78_sources 9 190588738561059210 190588738561059210 rfl endpoint_10_78_base endpoint_10_78_prefix_9) (by decide)⟩
private def endpoint_10_79_flag : Flag := ⟨10, 79, 1759⟩
private def endpoint_10_79_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_10_79_base : receiptBase endpoint_10_79_flag endpoint_10_79_sources = some 183560269240554881 := by decide +kernel
private theorem endpoint_10_79_window_0 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 2 183560269240554881 = some 183560269240554881 := by decide +kernel
private theorem endpoint_10_79_window_2 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 2 2 183560269240554881 = some 183560269240554881 := by decide +kernel
private theorem endpoint_10_79_prefix_4 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 4 183560269240554881 = some 183560269240554881 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 2 2 183560269240554881 183560269240554881 183560269240554881 endpoint_10_79_window_0 endpoint_10_79_window_2
private theorem endpoint_10_79_window_4 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 4 2 183560269240554881 = some 183560269240554881 := by decide +kernel
private theorem endpoint_10_79_prefix_6 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 6 183560269240554881 = some 183560269240554881 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 4 2 183560269240554881 183560269240554881 183560269240554881 endpoint_10_79_prefix_4 endpoint_10_79_window_4
private theorem endpoint_10_79_window_6 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 6 2 183560269240554881 = some 183560269240554881 := by decide +kernel
private theorem endpoint_10_79_prefix_8 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 8 183560269240554881 = some 183560269240554881 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 6 2 183560269240554881 183560269240554881 183560269240554881 endpoint_10_79_prefix_6 endpoint_10_79_window_6
private theorem endpoint_10_79_window_8 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 8 1 183560269240554881 = some 183560269240554881 := by decide +kernel
private theorem endpoint_10_79_prefix_9 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 9 183560269240554881 = some 183560269240554881 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 8 1 183560269240554881 183560269240554881 183560269240554881 endpoint_10_79_prefix_8 endpoint_10_79_window_8

def endpoint_10_79 : CertifiedEndpoint :=
  ⟨⟨10, 79, 1759⟩, 183560269240554881, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_10_79_flag endpoint_10_79_sources 9 183560269240554881 183560269240554881 rfl endpoint_10_79_base endpoint_10_79_prefix_9) (by decide)⟩
private def endpoint_10_80_flag : Flag := ⟨10, 80, 1666⟩
private def endpoint_10_80_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_10_80_base : receiptBase endpoint_10_80_flag endpoint_10_80_sources = some 175901986078527800 := by decide +kernel
private theorem endpoint_10_80_window_0 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 2 175901986078527800 = some 175901986078527800 := by decide +kernel
private theorem endpoint_10_80_window_2 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 2 2 175901986078527800 = some 175901986078527800 := by decide +kernel
private theorem endpoint_10_80_prefix_4 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 4 175901986078527800 = some 175901986078527800 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 2 2 175901986078527800 175901986078527800 175901986078527800 endpoint_10_80_window_0 endpoint_10_80_window_2
private theorem endpoint_10_80_window_4 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 4 2 175901986078527800 = some 175901986078527800 := by decide +kernel
private theorem endpoint_10_80_prefix_6 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 6 175901986078527800 = some 175901986078527800 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 4 2 175901986078527800 175901986078527800 175901986078527800 endpoint_10_80_prefix_4 endpoint_10_80_window_4
private theorem endpoint_10_80_window_6 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 6 2 175901986078527800 = some 175901986078527800 := by decide +kernel
private theorem endpoint_10_80_prefix_8 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 8 175901986078527800 = some 175901986078527800 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 6 2 175901986078527800 175901986078527800 175901986078527800 endpoint_10_80_prefix_6 endpoint_10_80_window_6
private theorem endpoint_10_80_window_8 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 8 1 175901986078527800 = some 175901986078527800 := by decide +kernel
private theorem endpoint_10_80_prefix_9 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 9 175901986078527800 = some 175901986078527800 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 8 1 175901986078527800 175901986078527800 175901986078527800 endpoint_10_80_prefix_8 endpoint_10_80_window_8

def endpoint_10_80 : CertifiedEndpoint :=
  ⟨⟨10, 80, 1666⟩, 175901986078527800, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_10_80_flag endpoint_10_80_sources 9 175901986078527800 175901986078527800 rfl endpoint_10_80_base endpoint_10_80_prefix_9) (by decide)⟩
private def endpoint_10_81_flag : Flag := ⟨10, 81, 1571⟩
private def endpoint_10_81_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_81_base : receiptBase endpoint_10_81_flag endpoint_10_81_sources = some 171061230324678774 := by decide +kernel
private theorem endpoint_10_81_window_0 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 2 171061230324678774 = some 171061230324678774 := by decide +kernel
private theorem endpoint_10_81_window_2 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 2 2 171061230324678774 = some 171061230324678774 := by decide +kernel
private theorem endpoint_10_81_prefix_4 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 4 171061230324678774 = some 171061230324678774 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 2 2 171061230324678774 171061230324678774 171061230324678774 endpoint_10_81_window_0 endpoint_10_81_window_2
private theorem endpoint_10_81_window_4 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 4 2 171061230324678774 = some 171061230324678774 := by decide +kernel
private theorem endpoint_10_81_prefix_6 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 6 171061230324678774 = some 171061230324678774 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 4 2 171061230324678774 171061230324678774 171061230324678774 endpoint_10_81_prefix_4 endpoint_10_81_window_4
private theorem endpoint_10_81_window_6 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 6 2 171061230324678774 = some 171061230324678774 := by decide +kernel
private theorem endpoint_10_81_prefix_8 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 8 171061230324678774 = some 171061230324678774 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 6 2 171061230324678774 171061230324678774 171061230324678774 endpoint_10_81_prefix_6 endpoint_10_81_window_6
private theorem endpoint_10_81_window_8 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 8 1 171061230324678774 = some 171061230324678774 := by decide +kernel
private theorem endpoint_10_81_prefix_9 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 9 171061230324678774 = some 171061230324678774 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 8 1 171061230324678774 171061230324678774 171061230324678774 endpoint_10_81_prefix_8 endpoint_10_81_window_8

def endpoint_10_81 : CertifiedEndpoint :=
  ⟨⟨10, 81, 1571⟩, 171061230324678774, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_81_flag endpoint_10_81_sources 9 171061230324678774 171061230324678774 rfl endpoint_10_81_base endpoint_10_81_prefix_9) (by decide)⟩
private def endpoint_10_82_flag : Flag := ⟨10, 82, 1473⟩
private def endpoint_10_82_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_82_base : receiptBase endpoint_10_82_flag endpoint_10_82_sources = some 162200186810425099 := by decide +kernel
private theorem endpoint_10_82_window_0 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 2 162200186810425099 = some 162200186810425099 := by decide +kernel
private theorem endpoint_10_82_window_2 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 2 2 162200186810425099 = some 162200186810425099 := by decide +kernel
private theorem endpoint_10_82_prefix_4 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 4 162200186810425099 = some 162200186810425099 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 2 2 162200186810425099 162200186810425099 162200186810425099 endpoint_10_82_window_0 endpoint_10_82_window_2
private theorem endpoint_10_82_window_4 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 4 2 162200186810425099 = some 162200186810425099 := by decide +kernel
private theorem endpoint_10_82_prefix_6 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 6 162200186810425099 = some 162200186810425099 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 4 2 162200186810425099 162200186810425099 162200186810425099 endpoint_10_82_prefix_4 endpoint_10_82_window_4
private theorem endpoint_10_82_window_6 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 6 2 162200186810425099 = some 162200186810425099 := by decide +kernel
private theorem endpoint_10_82_prefix_8 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 8 162200186810425099 = some 162200186810425099 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 6 2 162200186810425099 162200186810425099 162200186810425099 endpoint_10_82_prefix_6 endpoint_10_82_window_6
private theorem endpoint_10_82_window_8 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 8 1 162200186810425099 = some 162200186810425099 := by decide +kernel
private theorem endpoint_10_82_prefix_9 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 9 162200186810425099 = some 162200186810425099 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 8 1 162200186810425099 162200186810425099 162200186810425099 endpoint_10_82_prefix_8 endpoint_10_82_window_8

def endpoint_10_82 : CertifiedEndpoint :=
  ⟨⟨10, 82, 1473⟩, 162200186810425099, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_82_flag endpoint_10_82_sources 9 162200186810425099 162200186810425099 rfl endpoint_10_82_base endpoint_10_82_prefix_9) (by decide)⟩
def endpoint_10_83 : CertifiedEndpoint :=
  ⟨⟨10, 83, 1372⟩, 252825560663514597, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_84 : CertifiedEndpoint :=
  ⟨⟨10, 84, 1269⟩, 236125918779311239, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_85 : CertifiedEndpoint :=
  ⟨⟨10, 85, 1163⟩, 218331754202311508, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_86 : CertifiedEndpoint :=
  ⟨⟨10, 86, 1054⟩, 199420955885258094, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_87 : CertifiedEndpoint :=
  ⟨⟨10, 87, 943⟩, 179571649215576948, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_88 : CertifiedEndpoint :=
  ⟨⟨10, 88, 829⟩, 158566400277384679, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_89 : CertifiedEndpoint :=
  ⟨⟨10, 89, 712⟩, 136383098023423977, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_90 : CertifiedEndpoint :=
  ⟨⟨10, 90, 592⟩, 112999631406437532, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_91 : CertifiedEndpoint :=
  ⟨⟨10, 91, 470⟩, 88603952945965655, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_92 : CertifiedEndpoint :=
  ⟨⟨10, 92, 345⟩, 62968801594010595, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_93 : CertifiedEndpoint :=
  ⟨⟨10, 93, 217⟩, 36072066303315042, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_11 : CertifiedEndpoint :=
  ⟨⟨11, 11, 4209⟩, 72420054222541494, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_12 : CertifiedEndpoint :=
  ⟨⟨11, 12, 4190⟩, 75788235513551962, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_13 : CertifiedEndpoint :=
  ⟨⟨11, 13, 4171⟩, 79122794946367988, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_14 : CertifiedEndpoint :=
  ⟨⟨11, 14, 4152⟩, 89995510265450388, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_15 : CertifiedEndpoint :=
  ⟨⟨11, 15, 4132⟩, 100737921570685123, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_16 : CertifiedEndpoint :=
  ⟨⟨11, 16, 4112⟩, 111369038894248336, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_17 : CertifiedEndpoint :=
  ⟨⟨11, 17, 4093⟩, 121918730217747538, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_18 : CertifiedEndpoint :=
  ⟨⟨11, 18, 4072⟩, 132297391596360196, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_19 : CertifiedEndpoint :=
  ⟨⟨11, 19, 4052⟩, 142594626974908843, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_20 : CertifiedEndpoint :=
  ⟨⟨11, 20, 4032⟩, 152780568371785968, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_21 : CertifiedEndpoint :=
  ⟨⟨11, 21, 4011⟩, 162814489855952692, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_22 : CertifiedEndpoint :=
  ⟨⟨11, 22, 3990⟩, 172731688383732210, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_23 : CertifiedEndpoint :=
  ⟨⟨11, 23, 3969⟩, 182532163955124522, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_24 : CertifiedEndpoint :=
  ⟨⟨11, 24, 3948⟩, 192215916570129628, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_25 : CertifiedEndpoint :=
  ⟨⟨11, 25, 3926⟩, 201731362348277281, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_26 : CertifiedEndpoint :=
  ⟨⟨11, 26, 3904⟩, 211124656195322044, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_27 : CertifiedEndpoint :=
  ⟨⟨11, 27, 3882⟩, 220395798111263917, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_28 : CertifiedEndpoint :=
  ⟨⟨11, 28, 3860⟩, 229544788096102900, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_29 : CertifiedEndpoint :=
  ⟨⟨11, 29, 3837⟩, 238509184319937378, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_30 : CertifiedEndpoint :=
  ⟨⟨11, 30, 3814⟩, 247345999637953282, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_11_31_flag : Flag := ⟨11, 31, 3791⟩
private def endpoint_11_31_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_31_base : receiptBase endpoint_11_31_flag endpoint_11_31_sources = some 170461377317128589 := by decide +kernel
private theorem endpoint_11_31_window_0 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 2 170461377317128589 = some 170461377317128589 := by decide +kernel
private theorem endpoint_11_31_window_2 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 2 2 170461377317128589 = some 170461377317128589 := by decide +kernel
private theorem endpoint_11_31_prefix_4 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 4 170461377317128589 = some 170461377317128589 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 2 2 170461377317128589 170461377317128589 170461377317128589 endpoint_11_31_window_0 endpoint_11_31_window_2
private theorem endpoint_11_31_window_4 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 4 2 170461377317128589 = some 170461377317128589 := by decide +kernel
private theorem endpoint_11_31_prefix_6 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 6 170461377317128589 = some 170461377317128589 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 4 2 170461377317128589 170461377317128589 170461377317128589 endpoint_11_31_prefix_4 endpoint_11_31_window_4
private theorem endpoint_11_31_window_6 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 6 2 170461377317128589 = some 170461377317128589 := by decide +kernel
private theorem endpoint_11_31_prefix_8 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 8 170461377317128589 = some 170461377317128589 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 6 2 170461377317128589 170461377317128589 170461377317128589 endpoint_11_31_prefix_6 endpoint_11_31_window_6
private theorem endpoint_11_31_window_8 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 8 2 170461377317128589 = some 170461377317128589 := by decide +kernel
private theorem endpoint_11_31_prefix_10 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 10 170461377317128589 = some 170461377317128589 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 8 2 170461377317128589 170461377317128589 170461377317128589 endpoint_11_31_prefix_8 endpoint_11_31_window_8

def endpoint_11_31 : CertifiedEndpoint :=
  ⟨⟨11, 31, 3791⟩, 170461377317128589, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_31_flag endpoint_11_31_sources 10 170461377317128589 170461377317128589 rfl endpoint_11_31_base endpoint_11_31_prefix_10) (by decide)⟩
private def endpoint_11_32_flag : Flag := ⟨11, 32, 3767⟩
private def endpoint_11_32_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_32_base : receiptBase endpoint_11_32_flag endpoint_11_32_sources = some 173826706987284526 := by decide +kernel
private theorem endpoint_11_32_window_0 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 2 173826706987284526 = some 173826706987284526 := by decide +kernel
private theorem endpoint_11_32_window_2 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 2 2 173826706987284526 = some 173826706987284526 := by decide +kernel
private theorem endpoint_11_32_prefix_4 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 4 173826706987284526 = some 173826706987284526 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 2 2 173826706987284526 173826706987284526 173826706987284526 endpoint_11_32_window_0 endpoint_11_32_window_2
private theorem endpoint_11_32_window_4 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 4 2 173826706987284526 = some 173826706987284526 := by decide +kernel
private theorem endpoint_11_32_prefix_6 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 6 173826706987284526 = some 173826706987284526 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 4 2 173826706987284526 173826706987284526 173826706987284526 endpoint_11_32_prefix_4 endpoint_11_32_window_4
private theorem endpoint_11_32_window_6 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 6 2 173826706987284526 = some 173826706987284526 := by decide +kernel
private theorem endpoint_11_32_prefix_8 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 8 173826706987284526 = some 173826706987284526 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 6 2 173826706987284526 173826706987284526 173826706987284526 endpoint_11_32_prefix_6 endpoint_11_32_window_6
private theorem endpoint_11_32_window_8 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 8 2 173826706987284526 = some 173826706987284526 := by decide +kernel
private theorem endpoint_11_32_prefix_10 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 10 173826706987284526 = some 173826706987284526 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 8 2 173826706987284526 173826706987284526 173826706987284526 endpoint_11_32_prefix_8 endpoint_11_32_window_8

def endpoint_11_32 : CertifiedEndpoint :=
  ⟨⟨11, 32, 3767⟩, 173826706987284526, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_32_flag endpoint_11_32_sources 10 173826706987284526 173826706987284526 rfl endpoint_11_32_base endpoint_11_32_prefix_10) (by decide)⟩
private def endpoint_11_33_flag : Flag := ⟨11, 33, 3743⟩
private def endpoint_11_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_33_base : receiptBase endpoint_11_33_flag endpoint_11_33_sources = some 177135562429572516 := by decide +kernel
private theorem endpoint_11_33_window_0 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 2 177135562429572516 = some 177135562429572516 := by decide +kernel
private theorem endpoint_11_33_window_2 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 2 2 177135562429572516 = some 177135562429572516 := by decide +kernel
private theorem endpoint_11_33_prefix_4 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 4 177135562429572516 = some 177135562429572516 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 2 2 177135562429572516 177135562429572516 177135562429572516 endpoint_11_33_window_0 endpoint_11_33_window_2
private theorem endpoint_11_33_window_4 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 4 2 177135562429572516 = some 177135562429572516 := by decide +kernel
private theorem endpoint_11_33_prefix_6 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 6 177135562429572516 = some 177135562429572516 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 4 2 177135562429572516 177135562429572516 177135562429572516 endpoint_11_33_prefix_4 endpoint_11_33_window_4
private theorem endpoint_11_33_window_6 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 6 2 177135562429572516 = some 177135562429572516 := by decide +kernel
private theorem endpoint_11_33_prefix_8 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 8 177135562429572516 = some 177135562429572516 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 6 2 177135562429572516 177135562429572516 177135562429572516 endpoint_11_33_prefix_6 endpoint_11_33_window_6
private theorem endpoint_11_33_window_8 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 8 2 177135562429572516 = some 177135562429572516 := by decide +kernel
private theorem endpoint_11_33_prefix_10 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 10 177135562429572516 = some 177135562429572516 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 8 2 177135562429572516 177135562429572516 177135562429572516 endpoint_11_33_prefix_8 endpoint_11_33_window_8

def endpoint_11_33 : CertifiedEndpoint :=
  ⟨⟨11, 33, 3743⟩, 177135562429572516, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_33_flag endpoint_11_33_sources 10 177135562429572516 177135562429572516 rfl endpoint_11_33_base endpoint_11_33_prefix_10) (by decide)⟩
private def endpoint_11_34_flag : Flag := ⟨11, 34, 3719⟩
private def endpoint_11_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_34_base : receiptBase endpoint_11_34_flag endpoint_11_34_sources = some 180387943643992559 := by decide +kernel
private theorem endpoint_11_34_window_0 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 2 180387943643992559 = some 180387943643992559 := by decide +kernel
private theorem endpoint_11_34_window_2 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 2 2 180387943643992559 = some 180387943643992559 := by decide +kernel
private theorem endpoint_11_34_prefix_4 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 4 180387943643992559 = some 180387943643992559 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 2 2 180387943643992559 180387943643992559 180387943643992559 endpoint_11_34_window_0 endpoint_11_34_window_2
private theorem endpoint_11_34_window_4 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 4 2 180387943643992559 = some 180387943643992559 := by decide +kernel
private theorem endpoint_11_34_prefix_6 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 6 180387943643992559 = some 180387943643992559 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 4 2 180387943643992559 180387943643992559 180387943643992559 endpoint_11_34_prefix_4 endpoint_11_34_window_4
private theorem endpoint_11_34_window_6 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 6 2 180387943643992559 = some 180387943643992559 := by decide +kernel
private theorem endpoint_11_34_prefix_8 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 8 180387943643992559 = some 180387943643992559 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 6 2 180387943643992559 180387943643992559 180387943643992559 endpoint_11_34_prefix_6 endpoint_11_34_window_6
private theorem endpoint_11_34_window_8 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 8 2 180387943643992559 = some 180387943643992559 := by decide +kernel
private theorem endpoint_11_34_prefix_10 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 10 180387943643992559 = some 180387943643992559 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 8 2 180387943643992559 180387943643992559 180387943643992559 endpoint_11_34_prefix_8 endpoint_11_34_window_8

def endpoint_11_34 : CertifiedEndpoint :=
  ⟨⟨11, 34, 3719⟩, 180387943643992559, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_34_flag endpoint_11_34_sources 10 180387943643992559 180387943643992559 rfl endpoint_11_34_base endpoint_11_34_prefix_10) (by decide)⟩
private def endpoint_11_35_flag : Flag := ⟨11, 35, 3695⟩
private def endpoint_11_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_35_base : receiptBase endpoint_11_35_flag endpoint_11_35_sources = some 183583850630544654 := by decide +kernel
private theorem endpoint_11_35_window_0 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 2 183583850630544654 = some 183583850630544654 := by decide +kernel
private theorem endpoint_11_35_window_2 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 2 2 183583850630544654 = some 183583850630544654 := by decide +kernel
private theorem endpoint_11_35_prefix_4 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 4 183583850630544654 = some 183583850630544654 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 2 2 183583850630544654 183583850630544654 183583850630544654 endpoint_11_35_window_0 endpoint_11_35_window_2
private theorem endpoint_11_35_window_4 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 4 2 183583850630544654 = some 183583850630544654 := by decide +kernel
private theorem endpoint_11_35_prefix_6 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 6 183583850630544654 = some 183583850630544654 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 4 2 183583850630544654 183583850630544654 183583850630544654 endpoint_11_35_prefix_4 endpoint_11_35_window_4
private theorem endpoint_11_35_window_6 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 6 2 183583850630544654 = some 183583850630544654 := by decide +kernel
private theorem endpoint_11_35_prefix_8 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 8 183583850630544654 = some 183583850630544654 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 6 2 183583850630544654 183583850630544654 183583850630544654 endpoint_11_35_prefix_6 endpoint_11_35_window_6
private theorem endpoint_11_35_window_8 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 8 2 183583850630544654 = some 183583850630544654 := by decide +kernel
private theorem endpoint_11_35_prefix_10 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 10 183583850630544654 = some 183583850630544654 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 8 2 183583850630544654 183583850630544654 183583850630544654 endpoint_11_35_prefix_8 endpoint_11_35_window_8

def endpoint_11_35 : CertifiedEndpoint :=
  ⟨⟨11, 35, 3695⟩, 183583850630544654, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_35_flag endpoint_11_35_sources 10 183583850630544654 183583850630544654 rfl endpoint_11_35_base endpoint_11_35_prefix_10) (by decide)⟩
private def endpoint_11_36_flag : Flag := ⟨11, 36, 3670⟩
private def endpoint_11_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_36_base : receiptBase endpoint_11_36_flag endpoint_11_36_sources = some 186673205480180692 := by decide +kernel
private theorem endpoint_11_36_window_0 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 2 186673205480180692 = some 186673205480180692 := by decide +kernel
private theorem endpoint_11_36_window_2 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 2 2 186673205480180692 = some 186673205480180692 := by decide +kernel
private theorem endpoint_11_36_prefix_4 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 4 186673205480180692 = some 186673205480180692 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 2 2 186673205480180692 186673205480180692 186673205480180692 endpoint_11_36_window_0 endpoint_11_36_window_2
private theorem endpoint_11_36_window_4 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 4 2 186673205480180692 = some 186673205480180692 := by decide +kernel
private theorem endpoint_11_36_prefix_6 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 6 186673205480180692 = some 186673205480180692 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 4 2 186673205480180692 186673205480180692 186673205480180692 endpoint_11_36_prefix_4 endpoint_11_36_window_4
private theorem endpoint_11_36_window_6 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 6 2 186673205480180692 = some 186673205480180692 := by decide +kernel
private theorem endpoint_11_36_prefix_8 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 8 186673205480180692 = some 186673205480180692 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 6 2 186673205480180692 186673205480180692 186673205480180692 endpoint_11_36_prefix_6 endpoint_11_36_window_6
private theorem endpoint_11_36_window_8 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 8 2 186673205480180692 = some 186673205480180692 := by decide +kernel
private theorem endpoint_11_36_prefix_10 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 10 186673205480180692 = some 186673205480180692 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 8 2 186673205480180692 186673205480180692 186673205480180692 endpoint_11_36_prefix_8 endpoint_11_36_window_8

def endpoint_11_36 : CertifiedEndpoint :=
  ⟨⟨11, 36, 3670⟩, 186673205480180692, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_36_flag endpoint_11_36_sources 10 186673205480180692 186673205480180692 rfl endpoint_11_36_base endpoint_11_36_prefix_10) (by decide)⟩
private def endpoint_11_37_flag : Flag := ⟨11, 37, 3644⟩
private def endpoint_11_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_37_base : receiptBase endpoint_11_37_flag endpoint_11_37_sources = some 189652550862598860 := by decide +kernel
private theorem endpoint_11_37_window_0 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 2 189652550862598860 = some 189652550862598860 := by decide +kernel
private theorem endpoint_11_37_window_2 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 2 2 189652550862598860 = some 189652550862598860 := by decide +kernel
private theorem endpoint_11_37_prefix_4 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 4 189652550862598860 = some 189652550862598860 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 2 2 189652550862598860 189652550862598860 189652550862598860 endpoint_11_37_window_0 endpoint_11_37_window_2
private theorem endpoint_11_37_window_4 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 4 2 189652550862598860 = some 189652550862598860 := by decide +kernel
private theorem endpoint_11_37_prefix_6 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 6 189652550862598860 = some 189652550862598860 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 4 2 189652550862598860 189652550862598860 189652550862598860 endpoint_11_37_prefix_4 endpoint_11_37_window_4
private theorem endpoint_11_37_window_6 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 6 2 189652550862598860 = some 189652550862598860 := by decide +kernel
private theorem endpoint_11_37_prefix_8 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 8 189652550862598860 = some 189652550862598860 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 6 2 189652550862598860 189652550862598860 189652550862598860 endpoint_11_37_prefix_6 endpoint_11_37_window_6
private theorem endpoint_11_37_window_8 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 8 2 189652550862598860 = some 189652550862598860 := by decide +kernel
private theorem endpoint_11_37_prefix_10 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 10 189652550862598860 = some 189652550862598860 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 8 2 189652550862598860 189652550862598860 189652550862598860 endpoint_11_37_prefix_8 endpoint_11_37_window_8

def endpoint_11_37 : CertifiedEndpoint :=
  ⟨⟨11, 37, 3644⟩, 189652550862598860, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_37_flag endpoint_11_37_sources 10 189652550862598860 189652550862598860 rfl endpoint_11_37_base endpoint_11_37_prefix_10) (by decide)⟩
private def endpoint_11_38_flag : Flag := ⟨11, 38, 3619⟩
private def endpoint_11_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_38_base : receiptBase endpoint_11_38_flag endpoint_11_38_sources = some 192623195039329317 := by decide +kernel
private theorem endpoint_11_38_window_0 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 2 192623195039329317 = some 192623195039329317 := by decide +kernel
private theorem endpoint_11_38_window_2 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 2 2 192623195039329317 = some 192623195039329317 := by decide +kernel
private theorem endpoint_11_38_prefix_4 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 4 192623195039329317 = some 192623195039329317 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 2 2 192623195039329317 192623195039329317 192623195039329317 endpoint_11_38_window_0 endpoint_11_38_window_2
private theorem endpoint_11_38_window_4 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 4 2 192623195039329317 = some 192623195039329317 := by decide +kernel
private theorem endpoint_11_38_prefix_6 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 6 192623195039329317 = some 192623195039329317 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 4 2 192623195039329317 192623195039329317 192623195039329317 endpoint_11_38_prefix_4 endpoint_11_38_window_4
private theorem endpoint_11_38_window_6 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 6 2 192623195039329317 = some 192623195039329317 := by decide +kernel
private theorem endpoint_11_38_prefix_8 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 8 192623195039329317 = some 192623195039329317 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 6 2 192623195039329317 192623195039329317 192623195039329317 endpoint_11_38_prefix_6 endpoint_11_38_window_6
private theorem endpoint_11_38_window_8 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 8 2 192623195039329317 = some 192623195039329317 := by decide +kernel
private theorem endpoint_11_38_prefix_10 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 10 192623195039329317 = some 192623195039329317 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 8 2 192623195039329317 192623195039329317 192623195039329317 endpoint_11_38_prefix_8 endpoint_11_38_window_8

def endpoint_11_38 : CertifiedEndpoint :=
  ⟨⟨11, 38, 3619⟩, 192623195039329317, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_38_flag endpoint_11_38_sources 10 192623195039329317 192623195039329317 rfl endpoint_11_38_base endpoint_11_38_prefix_10) (by decide)⟩
private def endpoint_11_39_flag : Flag := ⟨11, 39, 3593⟩
private def endpoint_11_39_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_39_base : receiptBase endpoint_11_39_flag endpoint_11_39_sources = some 195481524861974029 := by decide +kernel
private theorem endpoint_11_39_window_0 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 2 195481524861974029 = some 195481524861974029 := by decide +kernel
private theorem endpoint_11_39_window_2 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 2 2 195481524861974029 = some 195481524861974029 := by decide +kernel
private theorem endpoint_11_39_prefix_4 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 4 195481524861974029 = some 195481524861974029 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 2 2 195481524861974029 195481524861974029 195481524861974029 endpoint_11_39_window_0 endpoint_11_39_window_2
private theorem endpoint_11_39_window_4 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 4 2 195481524861974029 = some 195481524861974029 := by decide +kernel
private theorem endpoint_11_39_prefix_6 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 6 195481524861974029 = some 195481524861974029 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 4 2 195481524861974029 195481524861974029 195481524861974029 endpoint_11_39_prefix_4 endpoint_11_39_window_4
private theorem endpoint_11_39_window_6 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 6 2 195481524861974029 = some 195481524861974029 := by decide +kernel
private theorem endpoint_11_39_prefix_8 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 8 195481524861974029 = some 195481524861974029 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 6 2 195481524861974029 195481524861974029 195481524861974029 endpoint_11_39_prefix_6 endpoint_11_39_window_6
private theorem endpoint_11_39_window_8 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 8 2 195481524861974029 = some 195481524861974029 := by decide +kernel
private theorem endpoint_11_39_prefix_10 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 10 195481524861974029 = some 195481524861974029 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 8 2 195481524861974029 195481524861974029 195481524861974029 endpoint_11_39_prefix_8 endpoint_11_39_window_8

def endpoint_11_39 : CertifiedEndpoint :=
  ⟨⟨11, 39, 3593⟩, 195481524861974029, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_39_flag endpoint_11_39_sources 10 195481524861974029 195481524861974029 rfl endpoint_11_39_base endpoint_11_39_prefix_10) (by decide)⟩
private def endpoint_11_40_flag : Flag := ⟨11, 40, 3566⟩
private def endpoint_11_40_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_40_base : receiptBase endpoint_11_40_flag endpoint_11_40_sources = some 198224083000231185 := by decide +kernel
private theorem endpoint_11_40_window_0 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 2 198224083000231185 = some 198224083000231185 := by decide +kernel
private theorem endpoint_11_40_window_2 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 2 2 198224083000231185 = some 198224083000231185 := by decide +kernel
private theorem endpoint_11_40_prefix_4 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 4 198224083000231185 = some 198224083000231185 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 2 2 198224083000231185 198224083000231185 198224083000231185 endpoint_11_40_window_0 endpoint_11_40_window_2
private theorem endpoint_11_40_window_4 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 4 2 198224083000231185 = some 198224083000231185 := by decide +kernel
private theorem endpoint_11_40_prefix_6 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 6 198224083000231185 = some 198224083000231185 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 4 2 198224083000231185 198224083000231185 198224083000231185 endpoint_11_40_prefix_4 endpoint_11_40_window_4
private theorem endpoint_11_40_window_6 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 6 2 198224083000231185 = some 198224083000231185 := by decide +kernel
private theorem endpoint_11_40_prefix_8 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 8 198224083000231185 = some 198224083000231185 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 6 2 198224083000231185 198224083000231185 198224083000231185 endpoint_11_40_prefix_6 endpoint_11_40_window_6
private theorem endpoint_11_40_window_8 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 8 2 198224083000231185 = some 198224083000231185 := by decide +kernel
private theorem endpoint_11_40_prefix_10 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 10 198224083000231185 = some 198224083000231185 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 8 2 198224083000231185 198224083000231185 198224083000231185 endpoint_11_40_prefix_8 endpoint_11_40_window_8

def endpoint_11_40 : CertifiedEndpoint :=
  ⟨⟨11, 40, 3566⟩, 198224083000231185, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_40_flag endpoint_11_40_sources 10 198224083000231185 198224083000231185 rfl endpoint_11_40_base endpoint_11_40_prefix_10) (by decide)⟩
private def endpoint_11_41_flag : Flag := ⟨11, 41, 3539⟩
private def endpoint_11_41_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_41_base : receiptBase endpoint_11_41_flag endpoint_11_41_sources = some 200903252250016769 := by decide +kernel
private theorem endpoint_11_41_window_0 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 2 200903252250016769 = some 200903252250016769 := by decide +kernel
private theorem endpoint_11_41_window_2 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 2 2 200903252250016769 = some 200903252250016769 := by decide +kernel
private theorem endpoint_11_41_prefix_4 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 4 200903252250016769 = some 200903252250016769 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 2 2 200903252250016769 200903252250016769 200903252250016769 endpoint_11_41_window_0 endpoint_11_41_window_2
private theorem endpoint_11_41_window_4 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 4 2 200903252250016769 = some 200903252250016769 := by decide +kernel
private theorem endpoint_11_41_prefix_6 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 6 200903252250016769 = some 200903252250016769 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 4 2 200903252250016769 200903252250016769 200903252250016769 endpoint_11_41_prefix_4 endpoint_11_41_window_4
private theorem endpoint_11_41_window_6 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 6 2 200903252250016769 = some 200903252250016769 := by decide +kernel
private theorem endpoint_11_41_prefix_8 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 8 200903252250016769 = some 200903252250016769 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 6 2 200903252250016769 200903252250016769 200903252250016769 endpoint_11_41_prefix_6 endpoint_11_41_window_6
private theorem endpoint_11_41_window_8 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 8 2 200903252250016769 = some 200903252250016769 := by decide +kernel
private theorem endpoint_11_41_prefix_10 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 10 200903252250016769 = some 200903252250016769 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 8 2 200903252250016769 200903252250016769 200903252250016769 endpoint_11_41_prefix_8 endpoint_11_41_window_8

def endpoint_11_41 : CertifiedEndpoint :=
  ⟨⟨11, 41, 3539⟩, 200903252250016769, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_41_flag endpoint_11_41_sources 10 200903252250016769 200903252250016769 rfl endpoint_11_41_base endpoint_11_41_prefix_10) (by decide)⟩
private def endpoint_11_42_flag : Flag := ⟨11, 42, 3512⟩
private def endpoint_11_42_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_42_base : receiptBase endpoint_11_42_flag endpoint_11_42_sources = some 203519032611330783 := by decide +kernel
private theorem endpoint_11_42_window_0 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 2 203519032611330783 = some 203519032611330783 := by decide +kernel
private theorem endpoint_11_42_window_2 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 2 2 203519032611330783 = some 203519032611330783 := by decide +kernel
private theorem endpoint_11_42_prefix_4 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 4 203519032611330783 = some 203519032611330783 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 2 2 203519032611330783 203519032611330783 203519032611330783 endpoint_11_42_window_0 endpoint_11_42_window_2
private theorem endpoint_11_42_window_4 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 4 2 203519032611330783 = some 203519032611330783 := by decide +kernel
private theorem endpoint_11_42_prefix_6 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 6 203519032611330783 = some 203519032611330783 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 4 2 203519032611330783 203519032611330783 203519032611330783 endpoint_11_42_prefix_4 endpoint_11_42_window_4
private theorem endpoint_11_42_window_6 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 6 2 203519032611330783 = some 203519032611330783 := by decide +kernel
private theorem endpoint_11_42_prefix_8 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 8 203519032611330783 = some 203519032611330783 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 6 2 203519032611330783 203519032611330783 203519032611330783 endpoint_11_42_prefix_6 endpoint_11_42_window_6
private theorem endpoint_11_42_window_8 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 8 2 203519032611330783 = some 203519032611330783 := by decide +kernel
private theorem endpoint_11_42_prefix_10 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 10 203519032611330783 = some 203519032611330783 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 8 2 203519032611330783 203519032611330783 203519032611330783 endpoint_11_42_prefix_8 endpoint_11_42_window_8

def endpoint_11_42 : CertifiedEndpoint :=
  ⟨⟨11, 42, 3512⟩, 203519032611330783, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_42_flag endpoint_11_42_sources 10 203519032611330783 203519032611330783 rfl endpoint_11_42_base endpoint_11_42_prefix_10) (by decide)⟩
private def endpoint_11_43_flag : Flag := ⟨11, 43, 3484⟩
private def endpoint_11_43_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_43_base : receiptBase endpoint_11_43_flag endpoint_11_43_sources = some 206013279071087553 := by decide +kernel
private theorem endpoint_11_43_window_0 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 2 206013279071087553 = some 207282640381288459 := by decide +kernel
private theorem endpoint_11_43_window_2 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 2 2 207282640381288459 = some 207282640381288459 := by decide +kernel
private theorem endpoint_11_43_prefix_4 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 4 206013279071087553 = some 207282640381288459 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 2 2 206013279071087553 207282640381288459 207282640381288459 endpoint_11_43_window_0 endpoint_11_43_window_2
private theorem endpoint_11_43_window_4 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 4 2 207282640381288459 = some 207282640381288459 := by decide +kernel
private theorem endpoint_11_43_prefix_6 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 6 206013279071087553 = some 207282640381288459 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 4 2 206013279071087553 207282640381288459 207282640381288459 endpoint_11_43_prefix_4 endpoint_11_43_window_4
private theorem endpoint_11_43_window_6 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 6 2 207282640381288459 = some 207282640381288459 := by decide +kernel
private theorem endpoint_11_43_prefix_8 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 8 206013279071087553 = some 207282640381288459 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 6 2 206013279071087553 207282640381288459 207282640381288459 endpoint_11_43_prefix_6 endpoint_11_43_window_6
private theorem endpoint_11_43_window_8 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 8 2 207282640381288459 = some 207282640381288459 := by decide +kernel
private theorem endpoint_11_43_prefix_10 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 10 206013279071087553 = some 207282640381288459 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 8 2 206013279071087553 207282640381288459 207282640381288459 endpoint_11_43_prefix_8 endpoint_11_43_window_8

def endpoint_11_43 : CertifiedEndpoint :=
  ⟨⟨11, 43, 3484⟩, 207282640381288459, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_43_flag endpoint_11_43_sources 10 206013279071087553 207282640381288459 rfl endpoint_11_43_base endpoint_11_43_prefix_10) (by decide)⟩
private def endpoint_11_44_flag : Flag := ⟨11, 44, 3455⟩
private def endpoint_11_44_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_44_base : receiptBase endpoint_11_44_flag endpoint_11_44_sources = some 208382534298985267 := by decide +kernel
private theorem endpoint_11_44_window_0 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 2 208382534298985267 = some 212043146941820580 := by decide +kernel
private theorem endpoint_11_44_window_2 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 2 2 212043146941820580 = some 212043146941820580 := by decide +kernel
private theorem endpoint_11_44_prefix_4 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 4 208382534298985267 = some 212043146941820580 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 2 2 208382534298985267 212043146941820580 212043146941820580 endpoint_11_44_window_0 endpoint_11_44_window_2
private theorem endpoint_11_44_window_4 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 4 2 212043146941820580 = some 212043146941820580 := by decide +kernel
private theorem endpoint_11_44_prefix_6 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 6 208382534298985267 = some 212043146941820580 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 4 2 208382534298985267 212043146941820580 212043146941820580 endpoint_11_44_prefix_4 endpoint_11_44_window_4
private theorem endpoint_11_44_window_6 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 6 2 212043146941820580 = some 212043146941820580 := by decide +kernel
private theorem endpoint_11_44_prefix_8 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 8 208382534298985267 = some 212043146941820580 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 6 2 208382534298985267 212043146941820580 212043146941820580 endpoint_11_44_prefix_6 endpoint_11_44_window_6
private theorem endpoint_11_44_window_8 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 8 2 212043146941820580 = some 212043146941820580 := by decide +kernel
private theorem endpoint_11_44_prefix_10 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 10 208382534298985267 = some 212043146941820580 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 8 2 208382534298985267 212043146941820580 212043146941820580 endpoint_11_44_prefix_8 endpoint_11_44_window_8

def endpoint_11_44 : CertifiedEndpoint :=
  ⟨⟨11, 44, 3455⟩, 212043146941820580, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_44_flag endpoint_11_44_sources 10 208382534298985267 212043146941820580 rfl endpoint_11_44_base endpoint_11_44_prefix_10) (by decide)⟩
private def endpoint_11_45_flag : Flag := ⟨11, 45, 3426⟩
private def endpoint_11_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_45_base : receiptBase endpoint_11_45_flag endpoint_11_45_sources = some 211204666443172743 := by decide +kernel
private theorem endpoint_11_45_window_0 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 2 211204666443172743 = some 211204666443172743 := by decide +kernel
private theorem endpoint_11_45_window_2 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 2 2 211204666443172743 = some 211204666443172743 := by decide +kernel
private theorem endpoint_11_45_prefix_4 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 4 211204666443172743 = some 211204666443172743 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 2 2 211204666443172743 211204666443172743 211204666443172743 endpoint_11_45_window_0 endpoint_11_45_window_2
private theorem endpoint_11_45_window_4 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 4 2 211204666443172743 = some 211204666443172743 := by decide +kernel
private theorem endpoint_11_45_prefix_6 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 6 211204666443172743 = some 211204666443172743 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 4 2 211204666443172743 211204666443172743 211204666443172743 endpoint_11_45_prefix_4 endpoint_11_45_window_4
private theorem endpoint_11_45_window_6 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 6 2 211204666443172743 = some 211204666443172743 := by decide +kernel
private theorem endpoint_11_45_prefix_8 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 8 211204666443172743 = some 211204666443172743 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 6 2 211204666443172743 211204666443172743 211204666443172743 endpoint_11_45_prefix_6 endpoint_11_45_window_6
private theorem endpoint_11_45_window_8 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 8 2 211204666443172743 = some 211204666443172743 := by decide +kernel
private theorem endpoint_11_45_prefix_10 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 10 211204666443172743 = some 211204666443172743 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 8 2 211204666443172743 211204666443172743 211204666443172743 endpoint_11_45_prefix_8 endpoint_11_45_window_8

def endpoint_11_45 : CertifiedEndpoint :=
  ⟨⟨11, 45, 3426⟩, 211204666443172743, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_45_flag endpoint_11_45_sources 10 211204666443172743 211204666443172743 rfl endpoint_11_45_base endpoint_11_45_prefix_10) (by decide)⟩
private def endpoint_11_46_flag : Flag := ⟨11, 46, 3396⟩
private def endpoint_11_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_46_base : receiptBase endpoint_11_46_flag endpoint_11_46_sources = some 213345616082217026 := by decide +kernel
private theorem endpoint_11_46_window_0 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 2 213345616082217026 = some 213345616082217026 := by decide +kernel
private theorem endpoint_11_46_window_2 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 2 2 213345616082217026 = some 213345616082217026 := by decide +kernel
private theorem endpoint_11_46_prefix_4 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 4 213345616082217026 = some 213345616082217026 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 2 2 213345616082217026 213345616082217026 213345616082217026 endpoint_11_46_window_0 endpoint_11_46_window_2
private theorem endpoint_11_46_window_4 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 4 2 213345616082217026 = some 213345616082217026 := by decide +kernel
private theorem endpoint_11_46_prefix_6 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 6 213345616082217026 = some 213345616082217026 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 4 2 213345616082217026 213345616082217026 213345616082217026 endpoint_11_46_prefix_4 endpoint_11_46_window_4
private theorem endpoint_11_46_window_6 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 6 2 213345616082217026 = some 213345616082217026 := by decide +kernel
private theorem endpoint_11_46_prefix_8 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 8 213345616082217026 = some 213345616082217026 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 6 2 213345616082217026 213345616082217026 213345616082217026 endpoint_11_46_prefix_6 endpoint_11_46_window_6
private theorem endpoint_11_46_window_8 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 8 2 213345616082217026 = some 213345616082217026 := by decide +kernel
private theorem endpoint_11_46_prefix_10 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 10 213345616082217026 = some 213345616082217026 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 8 2 213345616082217026 213345616082217026 213345616082217026 endpoint_11_46_prefix_8 endpoint_11_46_window_8

def endpoint_11_46 : CertifiedEndpoint :=
  ⟨⟨11, 46, 3396⟩, 213345616082217026, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_46_flag endpoint_11_46_sources 10 213345616082217026 213345616082217026 rfl endpoint_11_46_base endpoint_11_46_prefix_10) (by decide)⟩
private def endpoint_11_47_flag : Flag := ⟨11, 47, 3366⟩
private def endpoint_11_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_47_base : receiptBase endpoint_11_47_flag endpoint_11_47_sources = some 215416541101368320 := by decide +kernel
private theorem endpoint_11_47_window_0 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 2 215416541101368320 = some 215817863931329211 := by decide +kernel
private theorem endpoint_11_47_window_2 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 2 2 215817863931329211 = some 215817863931329211 := by decide +kernel
private theorem endpoint_11_47_prefix_4 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 4 215416541101368320 = some 215817863931329211 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 2 2 215416541101368320 215817863931329211 215817863931329211 endpoint_11_47_window_0 endpoint_11_47_window_2
private theorem endpoint_11_47_window_4 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 4 2 215817863931329211 = some 215817863931329211 := by decide +kernel
private theorem endpoint_11_47_prefix_6 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 6 215416541101368320 = some 215817863931329211 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 4 2 215416541101368320 215817863931329211 215817863931329211 endpoint_11_47_prefix_4 endpoint_11_47_window_4
private theorem endpoint_11_47_window_6 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 6 2 215817863931329211 = some 215817863931329211 := by decide +kernel
private theorem endpoint_11_47_prefix_8 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 8 215416541101368320 = some 215817863931329211 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 6 2 215416541101368320 215817863931329211 215817863931329211 endpoint_11_47_prefix_6 endpoint_11_47_window_6
private theorem endpoint_11_47_window_8 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 8 2 215817863931329211 = some 215817863931329211 := by decide +kernel
private theorem endpoint_11_47_prefix_10 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 10 215416541101368320 = some 215817863931329211 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 8 2 215416541101368320 215817863931329211 215817863931329211 endpoint_11_47_prefix_8 endpoint_11_47_window_8

def endpoint_11_47 : CertifiedEndpoint :=
  ⟨⟨11, 47, 3366⟩, 215817863931329211, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_47_flag endpoint_11_47_sources 10 215416541101368320 215817863931329211 rfl endpoint_11_47_base endpoint_11_47_prefix_10) (by decide)⟩
private def endpoint_11_48_flag : Flag := ⟨11, 48, 3335⟩
private def endpoint_11_48_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_48_base : receiptBase endpoint_11_48_flag endpoint_11_48_sources = some 217353291396268656 := by decide +kernel
private theorem endpoint_11_48_window_0 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 2 217353291396268656 = some 220066964397104180 := by decide +kernel
private theorem endpoint_11_48_window_2 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 2 2 220066964397104180 = some 220066964397104180 := by decide +kernel
private theorem endpoint_11_48_prefix_4 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 4 217353291396268656 = some 220066964397104180 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 2 2 217353291396268656 220066964397104180 220066964397104180 endpoint_11_48_window_0 endpoint_11_48_window_2
private theorem endpoint_11_48_window_4 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 4 2 220066964397104180 = some 220066964397104180 := by decide +kernel
private theorem endpoint_11_48_prefix_6 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 6 217353291396268656 = some 220066964397104180 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 4 2 217353291396268656 220066964397104180 220066964397104180 endpoint_11_48_prefix_4 endpoint_11_48_window_4
private theorem endpoint_11_48_window_6 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 6 2 220066964397104180 = some 220066964397104180 := by decide +kernel
private theorem endpoint_11_48_prefix_8 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 8 217353291396268656 = some 220066964397104180 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 6 2 217353291396268656 220066964397104180 220066964397104180 endpoint_11_48_prefix_6 endpoint_11_48_window_6
private theorem endpoint_11_48_window_8 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 8 2 220066964397104180 = some 220066964397104180 := by decide +kernel
private theorem endpoint_11_48_prefix_10 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 10 217353291396268656 = some 220066964397104180 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 8 2 217353291396268656 220066964397104180 220066964397104180 endpoint_11_48_prefix_8 endpoint_11_48_window_8

def endpoint_11_48 : CertifiedEndpoint :=
  ⟨⟨11, 48, 3335⟩, 220066964397104180, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_48_flag endpoint_11_48_sources 10 217353291396268656 220066964397104180 rfl endpoint_11_48_base endpoint_11_48_prefix_10) (by decide)⟩
private def endpoint_11_49_flag : Flag := ⟨11, 49, 3304⟩
private def endpoint_11_49_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_49_base : receiptBase endpoint_11_49_flag endpoint_11_49_sources = some 219217721182099185 := by decide +kernel
private theorem endpoint_11_49_window_0 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 2 219217721182099185 = some 224264077253320309 := by decide +kernel
private theorem endpoint_11_49_window_2 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 2 2 224264077253320309 = some 224264077253320309 := by decide +kernel
private theorem endpoint_11_49_prefix_4 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 4 219217721182099185 = some 224264077253320309 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 2 2 219217721182099185 224264077253320309 224264077253320309 endpoint_11_49_window_0 endpoint_11_49_window_2
private theorem endpoint_11_49_window_4 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 4 2 224264077253320309 = some 224264077253320309 := by decide +kernel
private theorem endpoint_11_49_prefix_6 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 6 219217721182099185 = some 224264077253320309 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 4 2 219217721182099185 224264077253320309 224264077253320309 endpoint_11_49_prefix_4 endpoint_11_49_window_4
private theorem endpoint_11_49_window_6 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 6 2 224264077253320309 = some 224264077253320309 := by decide +kernel
private theorem endpoint_11_49_prefix_8 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 8 219217721182099185 = some 224264077253320309 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 6 2 219217721182099185 224264077253320309 224264077253320309 endpoint_11_49_prefix_6 endpoint_11_49_window_6
private theorem endpoint_11_49_window_8 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 8 2 224264077253320309 = some 224264077253320309 := by decide +kernel
private theorem endpoint_11_49_prefix_10 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 10 219217721182099185 = some 224264077253320309 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 8 2 219217721182099185 224264077253320309 224264077253320309 endpoint_11_49_prefix_8 endpoint_11_49_window_8

def endpoint_11_49 : CertifiedEndpoint :=
  ⟨⟨11, 49, 3304⟩, 224264077253320309, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_49_flag endpoint_11_49_sources 10 219217721182099185 224264077253320309 rfl endpoint_11_49_base endpoint_11_49_prefix_10) (by decide)⟩
private def endpoint_11_50_flag : Flag := ⟨11, 50, 3271⟩
private def endpoint_11_50_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_50_base : receiptBase endpoint_11_50_flag endpoint_11_50_sources = some 220876938471790327 := by decide +kernel
private theorem endpoint_11_50_window_0 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 2 220876938471790327 = some 228340051735533306 := by decide +kernel
private theorem endpoint_11_50_window_2 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 2 2 228340051735533306 = some 228340051735533306 := by decide +kernel
private theorem endpoint_11_50_prefix_4 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 4 220876938471790327 = some 228340051735533306 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 2 2 220876938471790327 228340051735533306 228340051735533306 endpoint_11_50_window_0 endpoint_11_50_window_2
private theorem endpoint_11_50_window_4 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 4 2 228340051735533306 = some 228340051735533306 := by decide +kernel
private theorem endpoint_11_50_prefix_6 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 6 220876938471790327 = some 228340051735533306 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 4 2 220876938471790327 228340051735533306 228340051735533306 endpoint_11_50_prefix_4 endpoint_11_50_window_4
private theorem endpoint_11_50_window_6 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 6 2 228340051735533306 = some 228340051735533306 := by decide +kernel
private theorem endpoint_11_50_prefix_8 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 8 220876938471790327 = some 228340051735533306 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 6 2 220876938471790327 228340051735533306 228340051735533306 endpoint_11_50_prefix_6 endpoint_11_50_window_6
private theorem endpoint_11_50_window_8 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 8 2 228340051735533306 = some 228340051735533306 := by decide +kernel
private theorem endpoint_11_50_prefix_10 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 10 220876938471790327 = some 228340051735533306 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 8 2 220876938471790327 228340051735533306 228340051735533306 endpoint_11_50_prefix_8 endpoint_11_50_window_8

def endpoint_11_50 : CertifiedEndpoint :=
  ⟨⟨11, 50, 3271⟩, 228340051735533306, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_50_flag endpoint_11_50_sources 10 220876938471790327 228340051735533306 rfl endpoint_11_50_base endpoint_11_50_prefix_10) (by decide)⟩
private def endpoint_11_51_flag : Flag := ⟨11, 51, 3238⟩
private def endpoint_11_51_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_11_51_base : receiptBase endpoint_11_51_flag endpoint_11_51_sources = some 223032913033353013 := by decide +kernel
private theorem endpoint_11_51_window_0 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 2 223032913033353013 = some 224634036858612579 := by decide +kernel
private theorem endpoint_11_51_window_2 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 2 2 224634036858612579 = some 224634036858612579 := by decide +kernel
private theorem endpoint_11_51_prefix_4 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 4 223032913033353013 = some 224634036858612579 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 2 2 223032913033353013 224634036858612579 224634036858612579 endpoint_11_51_window_0 endpoint_11_51_window_2
private theorem endpoint_11_51_window_4 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 4 2 224634036858612579 = some 224634036858612579 := by decide +kernel
private theorem endpoint_11_51_prefix_6 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 6 223032913033353013 = some 224634036858612579 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 4 2 223032913033353013 224634036858612579 224634036858612579 endpoint_11_51_prefix_4 endpoint_11_51_window_4
private theorem endpoint_11_51_window_6 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 6 2 224634036858612579 = some 224634036858612579 := by decide +kernel
private theorem endpoint_11_51_prefix_8 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 8 223032913033353013 = some 224634036858612579 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 6 2 223032913033353013 224634036858612579 224634036858612579 endpoint_11_51_prefix_6 endpoint_11_51_window_6
private theorem endpoint_11_51_window_8 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 8 2 224634036858612579 = some 224634036858612579 := by decide +kernel
private theorem endpoint_11_51_prefix_10 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 10 223032913033353013 = some 224634036858612579 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 8 2 223032913033353013 224634036858612579 224634036858612579 endpoint_11_51_prefix_8 endpoint_11_51_window_8

def endpoint_11_51 : CertifiedEndpoint :=
  ⟨⟨11, 51, 3238⟩, 224634036858612579, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_11_51_flag endpoint_11_51_sources 10 223032913033353013 224634036858612579 rfl endpoint_11_51_base endpoint_11_51_prefix_10) (by decide)⟩
private def endpoint_11_52_flag : Flag := ⟨11, 52, 3204⟩
private def endpoint_11_52_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_11_52_base : receiptBase endpoint_11_52_flag endpoint_11_52_sources = some 224477447705578305 := by decide +kernel
private theorem endpoint_11_52_window_0 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 2 224477447705578305 = some 228391050428606640 := by decide +kernel
private theorem endpoint_11_52_window_2 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 2 2 228391050428606640 = some 228391050428606640 := by decide +kernel
private theorem endpoint_11_52_prefix_4 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 4 224477447705578305 = some 228391050428606640 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 2 2 224477447705578305 228391050428606640 228391050428606640 endpoint_11_52_window_0 endpoint_11_52_window_2
private theorem endpoint_11_52_window_4 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 4 2 228391050428606640 = some 228391050428606640 := by decide +kernel
private theorem endpoint_11_52_prefix_6 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 6 224477447705578305 = some 228391050428606640 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 4 2 224477447705578305 228391050428606640 228391050428606640 endpoint_11_52_prefix_4 endpoint_11_52_window_4
private theorem endpoint_11_52_window_6 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 6 2 228391050428606640 = some 228391050428606640 := by decide +kernel
private theorem endpoint_11_52_prefix_8 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 8 224477447705578305 = some 228391050428606640 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 6 2 224477447705578305 228391050428606640 228391050428606640 endpoint_11_52_prefix_6 endpoint_11_52_window_6
private theorem endpoint_11_52_window_8 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 8 2 228391050428606640 = some 228391050428606640 := by decide +kernel
private theorem endpoint_11_52_prefix_10 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 10 224477447705578305 = some 228391050428606640 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 8 2 224477447705578305 228391050428606640 228391050428606640 endpoint_11_52_prefix_8 endpoint_11_52_window_8

def endpoint_11_52 : CertifiedEndpoint :=
  ⟨⟨11, 52, 3204⟩, 228391050428606640, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_11_52_flag endpoint_11_52_sources 10 224477447705578305 228391050428606640 rfl endpoint_11_52_base endpoint_11_52_prefix_10) (by decide)⟩
private def endpoint_11_53_flag : Flag := ⟨11, 53, 3169⟩
private def endpoint_11_53_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_11_53_base : receiptBase endpoint_11_53_flag endpoint_11_53_sources = some 225772380333838138 := by decide +kernel
private theorem endpoint_11_53_window_0 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 2 225772380333838138 = some 232054311048129840 := by decide +kernel
private theorem endpoint_11_53_window_2 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 2 2 232054311048129840 = some 232054311048129840 := by decide +kernel
private theorem endpoint_11_53_prefix_4 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 4 225772380333838138 = some 232054311048129840 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 2 2 225772380333838138 232054311048129840 232054311048129840 endpoint_11_53_window_0 endpoint_11_53_window_2
private theorem endpoint_11_53_window_4 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 4 2 232054311048129840 = some 232054311048129840 := by decide +kernel
private theorem endpoint_11_53_prefix_6 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 6 225772380333838138 = some 232054311048129840 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 4 2 225772380333838138 232054311048129840 232054311048129840 endpoint_11_53_prefix_4 endpoint_11_53_window_4
private theorem endpoint_11_53_window_6 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 6 2 232054311048129840 = some 232054311048129840 := by decide +kernel
private theorem endpoint_11_53_prefix_8 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 8 225772380333838138 = some 232054311048129840 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 6 2 225772380333838138 232054311048129840 232054311048129840 endpoint_11_53_prefix_6 endpoint_11_53_window_6
private theorem endpoint_11_53_window_8 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 8 2 232054311048129840 = some 232054311048129840 := by decide +kernel
private theorem endpoint_11_53_prefix_10 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 10 225772380333838138 = some 232054311048129840 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 8 2 225772380333838138 232054311048129840 232054311048129840 endpoint_11_53_prefix_8 endpoint_11_53_window_8

def endpoint_11_53 : CertifiedEndpoint :=
  ⟨⟨11, 53, 3169⟩, 232054311048129840, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_11_53_flag endpoint_11_53_sources 10 225772380333838138 232054311048129840 rfl endpoint_11_53_base endpoint_11_53_prefix_10) (by decide)⟩
private def endpoint_11_54_flag : Flag := ⟨11, 54, 3133⟩
private def endpoint_11_54_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_54_base : receiptBase endpoint_11_54_flag endpoint_11_54_sources = some 229353931708003150 := by decide +kernel
private theorem endpoint_11_54_window_0 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 2 229353931708003150 = some 229353931708003150 := by decide +kernel
private theorem endpoint_11_54_window_2 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 2 2 229353931708003150 = some 229353931708003150 := by decide +kernel
private theorem endpoint_11_54_prefix_4 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 4 229353931708003150 = some 229353931708003150 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 2 2 229353931708003150 229353931708003150 229353931708003150 endpoint_11_54_window_0 endpoint_11_54_window_2
private theorem endpoint_11_54_window_4 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 4 2 229353931708003150 = some 229353931708003150 := by decide +kernel
private theorem endpoint_11_54_prefix_6 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 6 229353931708003150 = some 229353931708003150 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 4 2 229353931708003150 229353931708003150 229353931708003150 endpoint_11_54_prefix_4 endpoint_11_54_window_4
private theorem endpoint_11_54_window_6 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 6 2 229353931708003150 = some 229353931708003150 := by decide +kernel
private theorem endpoint_11_54_prefix_8 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 8 229353931708003150 = some 229353931708003150 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 6 2 229353931708003150 229353931708003150 229353931708003150 endpoint_11_54_prefix_6 endpoint_11_54_window_6
private theorem endpoint_11_54_window_8 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 8 2 229353931708003150 = some 229353931708003150 := by decide +kernel
private theorem endpoint_11_54_prefix_10 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 10 229353931708003150 = some 229353931708003150 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 8 2 229353931708003150 229353931708003150 229353931708003150 endpoint_11_54_prefix_8 endpoint_11_54_window_8

def endpoint_11_54 : CertifiedEndpoint :=
  ⟨⟨11, 54, 3133⟩, 229353931708003150, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_54_flag endpoint_11_54_sources 10 229353931708003150 229353931708003150 rfl endpoint_11_54_base endpoint_11_54_prefix_10) (by decide)⟩
private def endpoint_11_55_flag : Flag := ⟨11, 55, 3096⟩
private def endpoint_11_55_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_55_base : receiptBase endpoint_11_55_flag endpoint_11_55_sources = some 230301449282326391 := by decide +kernel
private theorem endpoint_11_55_window_0 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 2 230301449282326391 = some 230301449282326391 := by decide +kernel
private theorem endpoint_11_55_window_2 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 2 2 230301449282326391 = some 230301449282326391 := by decide +kernel
private theorem endpoint_11_55_prefix_4 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 4 230301449282326391 = some 230301449282326391 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 2 2 230301449282326391 230301449282326391 230301449282326391 endpoint_11_55_window_0 endpoint_11_55_window_2
private theorem endpoint_11_55_window_4 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 4 2 230301449282326391 = some 230301449282326391 := by decide +kernel
private theorem endpoint_11_55_prefix_6 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 6 230301449282326391 = some 230301449282326391 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 4 2 230301449282326391 230301449282326391 230301449282326391 endpoint_11_55_prefix_4 endpoint_11_55_window_4
private theorem endpoint_11_55_window_6 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 6 2 230301449282326391 = some 230301449282326391 := by decide +kernel
private theorem endpoint_11_55_prefix_8 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 8 230301449282326391 = some 230301449282326391 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 6 2 230301449282326391 230301449282326391 230301449282326391 endpoint_11_55_prefix_6 endpoint_11_55_window_6
private theorem endpoint_11_55_window_8 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 8 2 230301449282326391 = some 230301449282326391 := by decide +kernel
private theorem endpoint_11_55_prefix_10 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 10 230301449282326391 = some 230301449282326391 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 8 2 230301449282326391 230301449282326391 230301449282326391 endpoint_11_55_prefix_8 endpoint_11_55_window_8

def endpoint_11_55 : CertifiedEndpoint :=
  ⟨⟨11, 55, 3096⟩, 230301449282326391, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_55_flag endpoint_11_55_sources 10 230301449282326391 230301449282326391 rfl endpoint_11_55_base endpoint_11_55_prefix_10) (by decide)⟩
private def endpoint_11_56_flag : Flag := ⟨11, 56, 3058⟩
private def endpoint_11_56_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_56_base : receiptBase endpoint_11_56_flag endpoint_11_56_sources = some 231087644260691369 := by decide +kernel
private theorem endpoint_11_56_window_0 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 2 231087644260691369 = some 231721466735119044 := by decide +kernel
private theorem endpoint_11_56_window_2 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 2 2 231721466735119044 = some 231721466735119044 := by decide +kernel
private theorem endpoint_11_56_prefix_4 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 4 231087644260691369 = some 231721466735119044 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 2 2 231087644260691369 231721466735119044 231721466735119044 endpoint_11_56_window_0 endpoint_11_56_window_2
private theorem endpoint_11_56_window_4 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 4 2 231721466735119044 = some 231721466735119044 := by decide +kernel
private theorem endpoint_11_56_prefix_6 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 6 231087644260691369 = some 231721466735119044 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 4 2 231087644260691369 231721466735119044 231721466735119044 endpoint_11_56_prefix_4 endpoint_11_56_window_4
private theorem endpoint_11_56_window_6 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 6 2 231721466735119044 = some 231721466735119044 := by decide +kernel
private theorem endpoint_11_56_prefix_8 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 8 231087644260691369 = some 231721466735119044 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 6 2 231087644260691369 231721466735119044 231721466735119044 endpoint_11_56_prefix_6 endpoint_11_56_window_6
private theorem endpoint_11_56_window_8 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 8 2 231721466735119044 = some 231721466735119044 := by decide +kernel
private theorem endpoint_11_56_prefix_10 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 10 231087644260691369 = some 231721466735119044 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 8 2 231087644260691369 231721466735119044 231721466735119044 endpoint_11_56_prefix_8 endpoint_11_56_window_8

def endpoint_11_56 : CertifiedEndpoint :=
  ⟨⟨11, 56, 3058⟩, 231721466735119044, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_56_flag endpoint_11_56_sources 10 231087644260691369 231721466735119044 rfl endpoint_11_56_base endpoint_11_56_prefix_10) (by decide)⟩
private def endpoint_11_57_flag : Flag := ⟨11, 57, 3019⟩
private def endpoint_11_57_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_57_base : receiptBase endpoint_11_57_flag endpoint_11_57_sources = some 231709045823095091 := by decide +kernel
private theorem endpoint_11_57_window_0 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 2 231709045823095091 = some 234770222188929600 := by decide +kernel
private theorem endpoint_11_57_window_2 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 2 2 234770222188929600 = some 234770222188929600 := by decide +kernel
private theorem endpoint_11_57_prefix_4 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 4 231709045823095091 = some 234770222188929600 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 2 2 231709045823095091 234770222188929600 234770222188929600 endpoint_11_57_window_0 endpoint_11_57_window_2
private theorem endpoint_11_57_window_4 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 4 2 234770222188929600 = some 234770222188929600 := by decide +kernel
private theorem endpoint_11_57_prefix_6 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 6 231709045823095091 = some 234770222188929600 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 4 2 231709045823095091 234770222188929600 234770222188929600 endpoint_11_57_prefix_4 endpoint_11_57_window_4
private theorem endpoint_11_57_window_6 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 6 2 234770222188929600 = some 234770222188929600 := by decide +kernel
private theorem endpoint_11_57_prefix_8 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 8 231709045823095091 = some 234770222188929600 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 6 2 231709045823095091 234770222188929600 234770222188929600 endpoint_11_57_prefix_6 endpoint_11_57_window_6
private theorem endpoint_11_57_window_8 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 8 2 234770222188929600 = some 234770222188929600 := by decide +kernel
private theorem endpoint_11_57_prefix_10 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 10 231709045823095091 = some 234770222188929600 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 8 2 231709045823095091 234770222188929600 234770222188929600 endpoint_11_57_prefix_8 endpoint_11_57_window_8

def endpoint_11_57 : CertifiedEndpoint :=
  ⟨⟨11, 57, 3019⟩, 234770222188929600, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_57_flag endpoint_11_57_sources 10 231709045823095091 234770222188929600 rfl endpoint_11_57_base endpoint_11_57_prefix_10) (by decide)⟩
private def endpoint_11_58_flag : Flag := ⟨11, 58, 2978⟩
private def endpoint_11_58_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_58_base : receiptBase endpoint_11_58_flag endpoint_11_58_sources = some 232085317173649142 := by decide +kernel
private theorem endpoint_11_58_window_0 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 2 232085317173649142 = some 237672274971173024 := by decide +kernel
private theorem endpoint_11_58_window_2 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 2 2 237672274971173024 = some 237672274971173024 := by decide +kernel
private theorem endpoint_11_58_prefix_4 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 4 232085317173649142 = some 237672274971173024 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 2 2 232085317173649142 237672274971173024 237672274971173024 endpoint_11_58_window_0 endpoint_11_58_window_2
private theorem endpoint_11_58_window_4 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 4 2 237672274971173024 = some 237672274971173024 := by decide +kernel
private theorem endpoint_11_58_prefix_6 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 6 232085317173649142 = some 237672274971173024 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 4 2 232085317173649142 237672274971173024 237672274971173024 endpoint_11_58_prefix_4 endpoint_11_58_window_4
private theorem endpoint_11_58_window_6 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 6 2 237672274971173024 = some 237672274971173024 := by decide +kernel
private theorem endpoint_11_58_prefix_8 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 8 232085317173649142 = some 237672274971173024 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 6 2 232085317173649142 237672274971173024 237672274971173024 endpoint_11_58_prefix_6 endpoint_11_58_window_6
private theorem endpoint_11_58_window_8 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 8 2 237672274971173024 = some 237672274971173024 := by decide +kernel
private theorem endpoint_11_58_prefix_10 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 10 232085317173649142 = some 237672274971173024 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 8 2 232085317173649142 237672274971173024 237672274971173024 endpoint_11_58_prefix_8 endpoint_11_58_window_8

def endpoint_11_58 : CertifiedEndpoint :=
  ⟨⟨11, 58, 2978⟩, 237672274971173024, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_58_flag endpoint_11_58_sources 10 232085317173649142 237672274971173024 rfl endpoint_11_58_base endpoint_11_58_prefix_10) (by decide)⟩
private def endpoint_11_59_flag : Flag := ⟨11, 59, 2935⟩
private def endpoint_11_59_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_59_base : receiptBase endpoint_11_59_flag endpoint_11_59_sources = some 232209516672347533 := by decide +kernel
private theorem endpoint_11_59_window_0 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 2 232209516672347533 = some 240422831776056066 := by decide +kernel
private theorem endpoint_11_59_window_2 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 2 2 240422831776056066 = some 240422831776056066 := by decide +kernel
private theorem endpoint_11_59_prefix_4 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 4 232209516672347533 = some 240422831776056066 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 2 2 232209516672347533 240422831776056066 240422831776056066 endpoint_11_59_window_0 endpoint_11_59_window_2
private theorem endpoint_11_59_window_4 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 4 2 240422831776056066 = some 240422831776056066 := by decide +kernel
private theorem endpoint_11_59_prefix_6 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 6 232209516672347533 = some 240422831776056066 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 4 2 232209516672347533 240422831776056066 240422831776056066 endpoint_11_59_prefix_4 endpoint_11_59_window_4
private theorem endpoint_11_59_window_6 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 6 2 240422831776056066 = some 240422831776056066 := by decide +kernel
private theorem endpoint_11_59_prefix_8 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 8 232209516672347533 = some 240422831776056066 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 6 2 232209516672347533 240422831776056066 240422831776056066 endpoint_11_59_prefix_6 endpoint_11_59_window_6
private theorem endpoint_11_59_window_8 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 8 2 240422831776056066 = some 240422831776056066 := by decide +kernel
private theorem endpoint_11_59_prefix_10 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 10 232209516672347533 = some 240422831776056066 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 8 2 232209516672347533 240422831776056066 240422831776056066 endpoint_11_59_prefix_8 endpoint_11_59_window_8

def endpoint_11_59 : CertifiedEndpoint :=
  ⟨⟨11, 59, 2935⟩, 240422831776056066, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_59_flag endpoint_11_59_sources 10 232209516672347533 240422831776056066 rfl endpoint_11_59_base endpoint_11_59_prefix_10) (by decide)⟩
private def endpoint_11_60_flag : Flag := ⟨11, 60, 2891⟩
private def endpoint_11_60_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_11_60_base : receiptBase endpoint_11_60_flag endpoint_11_60_sources = some 233210233004717714 := by decide +kernel
private theorem endpoint_11_60_window_0 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 2 233210233004717714 = some 235833062049007886 := by decide +kernel
private theorem endpoint_11_60_window_2 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 2 2 235833062049007886 = some 235833062049007886 := by decide +kernel
private theorem endpoint_11_60_prefix_4 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 4 233210233004717714 = some 235833062049007886 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 2 2 233210233004717714 235833062049007886 235833062049007886 endpoint_11_60_window_0 endpoint_11_60_window_2
private theorem endpoint_11_60_window_4 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 4 2 235833062049007886 = some 235833062049007886 := by decide +kernel
private theorem endpoint_11_60_prefix_6 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 6 233210233004717714 = some 235833062049007886 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 4 2 233210233004717714 235833062049007886 235833062049007886 endpoint_11_60_prefix_4 endpoint_11_60_window_4
private theorem endpoint_11_60_window_6 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 6 2 235833062049007886 = some 235833062049007886 := by decide +kernel
private theorem endpoint_11_60_prefix_8 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 8 233210233004717714 = some 235833062049007886 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 6 2 233210233004717714 235833062049007886 235833062049007886 endpoint_11_60_prefix_6 endpoint_11_60_window_6
private theorem endpoint_11_60_window_8 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 8 2 235833062049007886 = some 235833062049007886 := by decide +kernel
private theorem endpoint_11_60_prefix_10 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 10 233210233004717714 = some 235833062049007886 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 8 2 233210233004717714 235833062049007886 235833062049007886 endpoint_11_60_prefix_8 endpoint_11_60_window_8

def endpoint_11_60 : CertifiedEndpoint :=
  ⟨⟨11, 60, 2891⟩, 235833062049007886, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_11_60_flag endpoint_11_60_sources 10 233210233004717714 235833062049007886 rfl endpoint_11_60_base endpoint_11_60_prefix_10) (by decide)⟩
private def endpoint_11_61_flag : Flag := ⟨11, 61, 2845⟩
private def endpoint_11_61_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_11_61_base : receiptBase endpoint_11_61_flag endpoint_11_61_sources = some 232891872590895820 := by decide +kernel
private theorem endpoint_11_61_window_0 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 2 232891872590895820 = some 238176119178492145 := by decide +kernel
private theorem endpoint_11_61_window_2 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 2 2 238176119178492145 = some 238176119178492145 := by decide +kernel
private theorem endpoint_11_61_prefix_4 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 4 232891872590895820 = some 238176119178492145 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 2 2 232891872590895820 238176119178492145 238176119178492145 endpoint_11_61_window_0 endpoint_11_61_window_2
private theorem endpoint_11_61_window_4 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 4 2 238176119178492145 = some 238176119178492145 := by decide +kernel
private theorem endpoint_11_61_prefix_6 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 6 232891872590895820 = some 238176119178492145 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 4 2 232891872590895820 238176119178492145 238176119178492145 endpoint_11_61_prefix_4 endpoint_11_61_window_4
private theorem endpoint_11_61_window_6 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 6 2 238176119178492145 = some 238176119178492145 := by decide +kernel
private theorem endpoint_11_61_prefix_8 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 8 232891872590895820 = some 238176119178492145 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 6 2 232891872590895820 238176119178492145 238176119178492145 endpoint_11_61_prefix_6 endpoint_11_61_window_6
private theorem endpoint_11_61_window_8 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 8 2 238176119178492145 = some 238176119178492145 := by decide +kernel
private theorem endpoint_11_61_prefix_10 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 10 232891872590895820 = some 238176119178492145 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 8 2 232891872590895820 238176119178492145 238176119178492145 endpoint_11_61_prefix_8 endpoint_11_61_window_8

def endpoint_11_61 : CertifiedEndpoint :=
  ⟨⟨11, 61, 2845⟩, 238176119178492145, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_11_61_flag endpoint_11_61_sources 10 232891872590895820 238176119178492145 rfl endpoint_11_61_base endpoint_11_61_prefix_10) (by decide)⟩
private def endpoint_11_62_flag : Flag := ⟨11, 62, 2797⟩
private def endpoint_11_62_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_11_62_base : receiptBase endpoint_11_62_flag endpoint_11_62_sources = some 233414863638055457 := by decide +kernel
private theorem endpoint_11_62_window_0 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 2 233414863638055457 = some 234987978404602734 := by decide +kernel
private theorem endpoint_11_62_window_2 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 2 2 234987978404602734 = some 234987978404602734 := by decide +kernel
private theorem endpoint_11_62_prefix_4 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 4 233414863638055457 = some 234987978404602734 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 2 2 233414863638055457 234987978404602734 234987978404602734 endpoint_11_62_window_0 endpoint_11_62_window_2
private theorem endpoint_11_62_window_4 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 4 2 234987978404602734 = some 234987978404602734 := by decide +kernel
private theorem endpoint_11_62_prefix_6 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 6 233414863638055457 = some 234987978404602734 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 4 2 233414863638055457 234987978404602734 234987978404602734 endpoint_11_62_prefix_4 endpoint_11_62_window_4
private theorem endpoint_11_62_window_6 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 6 2 234987978404602734 = some 234987978404602734 := by decide +kernel
private theorem endpoint_11_62_prefix_8 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 8 233414863638055457 = some 234987978404602734 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 6 2 233414863638055457 234987978404602734 234987978404602734 endpoint_11_62_prefix_6 endpoint_11_62_window_6
private theorem endpoint_11_62_window_8 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 8 2 234987978404602734 = some 234987978404602734 := by decide +kernel
private theorem endpoint_11_62_prefix_10 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 10 233414863638055457 = some 234987978404602734 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 8 2 233414863638055457 234987978404602734 234987978404602734 endpoint_11_62_prefix_8 endpoint_11_62_window_8

def endpoint_11_62 : CertifiedEndpoint :=
  ⟨⟨11, 62, 2797⟩, 234987978404602734, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_11_62_flag endpoint_11_62_sources 10 233414863638055457 234987978404602734 rfl endpoint_11_62_base endpoint_11_62_prefix_10) (by decide)⟩
private def endpoint_11_63_flag : Flag := ⟨11, 63, 2746⟩
private def endpoint_11_63_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_11_63_base : receiptBase endpoint_11_63_flag endpoint_11_63_sources = some 232459766937181708 := by decide +kernel
private theorem endpoint_11_63_window_0 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 2 232459766937181708 = some 236856566971577988 := by decide +kernel
private theorem endpoint_11_63_window_2 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 2 2 236856566971577988 = some 236856566971577988 := by decide +kernel
private theorem endpoint_11_63_prefix_4 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 4 232459766937181708 = some 236856566971577988 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 2 2 232459766937181708 236856566971577988 236856566971577988 endpoint_11_63_window_0 endpoint_11_63_window_2
private theorem endpoint_11_63_window_4 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 4 2 236856566971577988 = some 236856566971577988 := by decide +kernel
private theorem endpoint_11_63_prefix_6 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 6 232459766937181708 = some 236856566971577988 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 4 2 232459766937181708 236856566971577988 236856566971577988 endpoint_11_63_prefix_4 endpoint_11_63_window_4
private theorem endpoint_11_63_window_6 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 6 2 236856566971577988 = some 236856566971577988 := by decide +kernel
private theorem endpoint_11_63_prefix_8 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 8 232459766937181708 = some 236856566971577988 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 6 2 232459766937181708 236856566971577988 236856566971577988 endpoint_11_63_prefix_6 endpoint_11_63_window_6
private theorem endpoint_11_63_window_8 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 8 2 236856566971577988 = some 236856566971577988 := by decide +kernel
private theorem endpoint_11_63_prefix_10 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 10 232459766937181708 = some 236856566971577988 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 8 2 232459766937181708 236856566971577988 236856566971577988 endpoint_11_63_prefix_8 endpoint_11_63_window_8

def endpoint_11_63 : CertifiedEndpoint :=
  ⟨⟨11, 63, 2746⟩, 236856566971577988, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_11_63_flag endpoint_11_63_sources 10 232459766937181708 236856566971577988 rfl endpoint_11_63_base endpoint_11_63_prefix_10) (by decide)⟩
private def endpoint_11_64_flag : Flag := ⟨11, 64, 2693⟩
private def endpoint_11_64_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_11_64_base : receiptBase endpoint_11_64_flag endpoint_11_64_sources = some 232371200717185313 := by decide +kernel
private theorem endpoint_11_64_window_0 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 2 232371200717185313 = some 234811586046618836 := by decide +kernel
private theorem endpoint_11_64_window_2 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 2 2 234811586046618836 = some 234811586046618836 := by decide +kernel
private theorem endpoint_11_64_prefix_4 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 4 232371200717185313 = some 234811586046618836 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 2 2 232371200717185313 234811586046618836 234811586046618836 endpoint_11_64_window_0 endpoint_11_64_window_2
private theorem endpoint_11_64_window_4 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 4 2 234811586046618836 = some 234811586046618836 := by decide +kernel
private theorem endpoint_11_64_prefix_6 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 6 232371200717185313 = some 234811586046618836 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 4 2 232371200717185313 234811586046618836 234811586046618836 endpoint_11_64_prefix_4 endpoint_11_64_window_4
private theorem endpoint_11_64_window_6 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 6 2 234811586046618836 = some 234811586046618836 := by decide +kernel
private theorem endpoint_11_64_prefix_8 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 8 232371200717185313 = some 234811586046618836 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 6 2 232371200717185313 234811586046618836 234811586046618836 endpoint_11_64_prefix_6 endpoint_11_64_window_6
private theorem endpoint_11_64_window_8 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 8 2 234811586046618836 = some 234811586046618836 := by decide +kernel
private theorem endpoint_11_64_prefix_10 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 10 232371200717185313 = some 234811586046618836 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 8 2 232371200717185313 234811586046618836 234811586046618836 endpoint_11_64_prefix_8 endpoint_11_64_window_8

def endpoint_11_64 : CertifiedEndpoint :=
  ⟨⟨11, 64, 2693⟩, 234811586046618836, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_11_64_flag endpoint_11_64_sources 10 232371200717185313 234811586046618836 rfl endpoint_11_64_base endpoint_11_64_prefix_10) (by decide)⟩
private def endpoint_11_65_flag : Flag := ⟨11, 65, 2637⟩
private def endpoint_11_65_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_11_65_base : receiptBase endpoint_11_65_flag endpoint_11_65_sources = some 231925438513490118 := by decide +kernel
private theorem endpoint_11_65_window_0 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 2 231925438513490118 = some 233775569703068895 := by decide +kernel
private theorem endpoint_11_65_window_2 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 2 2 233775569703068895 = some 233775569703068895 := by decide +kernel
private theorem endpoint_11_65_prefix_4 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 4 231925438513490118 = some 233775569703068895 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 2 2 231925438513490118 233775569703068895 233775569703068895 endpoint_11_65_window_0 endpoint_11_65_window_2
private theorem endpoint_11_65_window_4 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 4 2 233775569703068895 = some 233775569703068895 := by decide +kernel
private theorem endpoint_11_65_prefix_6 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 6 231925438513490118 = some 233775569703068895 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 4 2 231925438513490118 233775569703068895 233775569703068895 endpoint_11_65_prefix_4 endpoint_11_65_window_4
private theorem endpoint_11_65_window_6 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 6 2 233775569703068895 = some 233775569703068895 := by decide +kernel
private theorem endpoint_11_65_prefix_8 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 8 231925438513490118 = some 233775569703068895 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 6 2 231925438513490118 233775569703068895 233775569703068895 endpoint_11_65_prefix_6 endpoint_11_65_window_6
private theorem endpoint_11_65_window_8 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 8 2 233775569703068895 = some 233775569703068895 := by decide +kernel
private theorem endpoint_11_65_prefix_10 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 10 231925438513490118 = some 233775569703068895 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 8 2 231925438513490118 233775569703068895 233775569703068895 endpoint_11_65_prefix_8 endpoint_11_65_window_8

def endpoint_11_65 : CertifiedEndpoint :=
  ⟨⟨11, 65, 2637⟩, 233775569703068895, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_11_65_flag endpoint_11_65_sources 10 231925438513490118 233775569703068895 rfl endpoint_11_65_base endpoint_11_65_prefix_10) (by decide)⟩
private def endpoint_11_66_flag : Flag := ⟨11, 66, 2579⟩
private def endpoint_11_66_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_66_base : receiptBase endpoint_11_66_flag endpoint_11_66_sources = some 231041451096426070 := by decide +kernel
private theorem endpoint_11_66_window_0 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 2 231041451096426070 = some 231041451096426070 := by decide +kernel
private theorem endpoint_11_66_window_2 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 2 2 231041451096426070 = some 231041451096426070 := by decide +kernel
private theorem endpoint_11_66_prefix_4 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 4 231041451096426070 = some 231041451096426070 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 2 2 231041451096426070 231041451096426070 231041451096426070 endpoint_11_66_window_0 endpoint_11_66_window_2
private theorem endpoint_11_66_window_4 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 4 2 231041451096426070 = some 231041451096426070 := by decide +kernel
private theorem endpoint_11_66_prefix_6 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 6 231041451096426070 = some 231041451096426070 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 4 2 231041451096426070 231041451096426070 231041451096426070 endpoint_11_66_prefix_4 endpoint_11_66_window_4
private theorem endpoint_11_66_window_6 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 6 2 231041451096426070 = some 231041451096426070 := by decide +kernel
private theorem endpoint_11_66_prefix_8 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 8 231041451096426070 = some 231041451096426070 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 6 2 231041451096426070 231041451096426070 231041451096426070 endpoint_11_66_prefix_6 endpoint_11_66_window_6
private theorem endpoint_11_66_window_8 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 8 2 231041451096426070 = some 231041451096426070 := by decide +kernel
private theorem endpoint_11_66_prefix_10 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 10 231041451096426070 = some 231041451096426070 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 8 2 231041451096426070 231041451096426070 231041451096426070 endpoint_11_66_prefix_8 endpoint_11_66_window_8

def endpoint_11_66 : CertifiedEndpoint :=
  ⟨⟨11, 66, 2579⟩, 231041451096426070, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_66_flag endpoint_11_66_sources 10 231041451096426070 231041451096426070 rfl endpoint_11_66_base endpoint_11_66_prefix_10) (by decide)⟩
private def endpoint_11_67_flag : Flag := ⟨11, 67, 2519⟩
private def endpoint_11_67_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_67_base : receiptBase endpoint_11_67_flag endpoint_11_67_sources = some 228762482249096196 := by decide +kernel
private theorem endpoint_11_67_window_0 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 2 228762482249096196 = some 228974488969321658 := by decide +kernel
private theorem endpoint_11_67_window_2 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 2 2 228974488969321658 = some 228974488969321658 := by decide +kernel
private theorem endpoint_11_67_prefix_4 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 4 228762482249096196 = some 228974488969321658 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 2 2 228762482249096196 228974488969321658 228974488969321658 endpoint_11_67_window_0 endpoint_11_67_window_2
private theorem endpoint_11_67_window_4 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 4 2 228974488969321658 = some 228974488969321658 := by decide +kernel
private theorem endpoint_11_67_prefix_6 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 6 228762482249096196 = some 228974488969321658 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 4 2 228762482249096196 228974488969321658 228974488969321658 endpoint_11_67_prefix_4 endpoint_11_67_window_4
private theorem endpoint_11_67_window_6 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 6 2 228974488969321658 = some 228974488969321658 := by decide +kernel
private theorem endpoint_11_67_prefix_8 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 8 228762482249096196 = some 228974488969321658 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 6 2 228762482249096196 228974488969321658 228974488969321658 endpoint_11_67_prefix_6 endpoint_11_67_window_6
private theorem endpoint_11_67_window_8 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 8 2 228974488969321658 = some 228974488969321658 := by decide +kernel
private theorem endpoint_11_67_prefix_10 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 10 228762482249096196 = some 228974488969321658 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 8 2 228762482249096196 228974488969321658 228974488969321658 endpoint_11_67_prefix_8 endpoint_11_67_window_8

def endpoint_11_67 : CertifiedEndpoint :=
  ⟨⟨11, 67, 2519⟩, 228974488969321658, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_67_flag endpoint_11_67_sources 10 228762482249096196 228974488969321658 rfl endpoint_11_67_base endpoint_11_67_prefix_10) (by decide)⟩
private def endpoint_11_68_flag : Flag := ⟨11, 68, 2456⟩
private def endpoint_11_68_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_68_base : receiptBase endpoint_11_68_flag endpoint_11_68_sources = some 226065126489873709 := by decide +kernel
private theorem endpoint_11_68_window_0 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 2 226065126489873709 = some 229597024163578740 := by decide +kernel
private theorem endpoint_11_68_window_2 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 2 2 229597024163578740 = some 229597024163578740 := by decide +kernel
private theorem endpoint_11_68_prefix_4 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 4 226065126489873709 = some 229597024163578740 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 2 2 226065126489873709 229597024163578740 229597024163578740 endpoint_11_68_window_0 endpoint_11_68_window_2
private theorem endpoint_11_68_window_4 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 4 2 229597024163578740 = some 229597024163578740 := by decide +kernel
private theorem endpoint_11_68_prefix_6 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 6 226065126489873709 = some 229597024163578740 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 4 2 226065126489873709 229597024163578740 229597024163578740 endpoint_11_68_prefix_4 endpoint_11_68_window_4
private theorem endpoint_11_68_window_6 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 6 2 229597024163578740 = some 229597024163578740 := by decide +kernel
private theorem endpoint_11_68_prefix_8 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 8 226065126489873709 = some 229597024163578740 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 6 2 226065126489873709 229597024163578740 229597024163578740 endpoint_11_68_prefix_6 endpoint_11_68_window_6
private theorem endpoint_11_68_window_8 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 8 2 229597024163578740 = some 229597024163578740 := by decide +kernel
private theorem endpoint_11_68_prefix_10 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 10 226065126489873709 = some 229597024163578740 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 8 2 226065126489873709 229597024163578740 229597024163578740 endpoint_11_68_prefix_8 endpoint_11_68_window_8

def endpoint_11_68 : CertifiedEndpoint :=
  ⟨⟨11, 68, 2456⟩, 229597024163578740, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_68_flag endpoint_11_68_sources 10 226065126489873709 229597024163578740 rfl endpoint_11_68_base endpoint_11_68_prefix_10) (by decide)⟩
private def endpoint_11_69_flag : Flag := ⟨11, 69, 2390⟩
private def endpoint_11_69_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_69_base : receiptBase endpoint_11_69_flag endpoint_11_69_sources = some 222938566353285706 := by decide +kernel
private theorem endpoint_11_69_window_0 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 2 222938566353285706 = some 229967180601446669 := by decide +kernel
private theorem endpoint_11_69_window_2 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 2 2 229967180601446669 = some 229967180601446669 := by decide +kernel
private theorem endpoint_11_69_prefix_4 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 4 222938566353285706 = some 229967180601446669 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 2 2 222938566353285706 229967180601446669 229967180601446669 endpoint_11_69_window_0 endpoint_11_69_window_2
private theorem endpoint_11_69_window_4 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 4 2 229967180601446669 = some 229967180601446669 := by decide +kernel
private theorem endpoint_11_69_prefix_6 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 6 222938566353285706 = some 229967180601446669 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 4 2 222938566353285706 229967180601446669 229967180601446669 endpoint_11_69_prefix_4 endpoint_11_69_window_4
private theorem endpoint_11_69_window_6 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 6 2 229967180601446669 = some 229967180601446669 := by decide +kernel
private theorem endpoint_11_69_prefix_8 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 8 222938566353285706 = some 229967180601446669 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 6 2 222938566353285706 229967180601446669 229967180601446669 endpoint_11_69_prefix_6 endpoint_11_69_window_6
private theorem endpoint_11_69_window_8 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 8 2 229967180601446669 = some 229967180601446669 := by decide +kernel
private theorem endpoint_11_69_prefix_10 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 10 222938566353285706 = some 229967180601446669 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 8 2 222938566353285706 229967180601446669 229967180601446669 endpoint_11_69_prefix_8 endpoint_11_69_window_8

def endpoint_11_69 : CertifiedEndpoint :=
  ⟨⟨11, 69, 2390⟩, 229967180601446669, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_69_flag endpoint_11_69_sources 10 222938566353285706 229967180601446669 rfl endpoint_11_69_base endpoint_11_69_prefix_10) (by decide)⟩
private def endpoint_11_70_flag : Flag := ⟨11, 70, 2322⟩
private def endpoint_11_70_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_11_70_base : receiptBase endpoint_11_70_flag endpoint_11_70_sources = some 224436749583382801 := by decide +kernel
private theorem endpoint_11_70_window_0 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 2 224436749583382801 = some 224436749583382801 := by decide +kernel
private theorem endpoint_11_70_window_2 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 2 2 224436749583382801 = some 224436749583382801 := by decide +kernel
private theorem endpoint_11_70_prefix_4 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 4 224436749583382801 = some 224436749583382801 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 2 2 224436749583382801 224436749583382801 224436749583382801 endpoint_11_70_window_0 endpoint_11_70_window_2
private theorem endpoint_11_70_window_4 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 4 2 224436749583382801 = some 224436749583382801 := by decide +kernel
private theorem endpoint_11_70_prefix_6 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 6 224436749583382801 = some 224436749583382801 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 4 2 224436749583382801 224436749583382801 224436749583382801 endpoint_11_70_prefix_4 endpoint_11_70_window_4
private theorem endpoint_11_70_window_6 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 6 2 224436749583382801 = some 224436749583382801 := by decide +kernel
private theorem endpoint_11_70_prefix_8 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 8 224436749583382801 = some 224436749583382801 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 6 2 224436749583382801 224436749583382801 224436749583382801 endpoint_11_70_prefix_6 endpoint_11_70_window_6
private theorem endpoint_11_70_window_8 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 8 2 224436749583382801 = some 224436749583382801 := by decide +kernel
private theorem endpoint_11_70_prefix_10 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 10 224436749583382801 = some 224436749583382801 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 8 2 224436749583382801 224436749583382801 224436749583382801 endpoint_11_70_prefix_8 endpoint_11_70_window_8

def endpoint_11_70 : CertifiedEndpoint :=
  ⟨⟨11, 70, 2322⟩, 224436749583382801, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_11_70_flag endpoint_11_70_sources 10 224436749583382801 224436749583382801 rfl endpoint_11_70_base endpoint_11_70_prefix_10) (by decide)⟩
private def endpoint_11_71_flag : Flag := ⟨11, 71, 2251⟩
private def endpoint_11_71_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_11_71_base : receiptBase endpoint_11_71_flag endpoint_11_71_sources = some 220478113884612438 := by decide +kernel
private theorem endpoint_11_71_window_0 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 2 220478113884612438 = some 220478113884612438 := by decide +kernel
private theorem endpoint_11_71_window_2 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 2 2 220478113884612438 = some 220478113884612438 := by decide +kernel
private theorem endpoint_11_71_prefix_4 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 4 220478113884612438 = some 220478113884612438 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 2 2 220478113884612438 220478113884612438 220478113884612438 endpoint_11_71_window_0 endpoint_11_71_window_2
private theorem endpoint_11_71_window_4 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 4 2 220478113884612438 = some 220478113884612438 := by decide +kernel
private theorem endpoint_11_71_prefix_6 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 6 220478113884612438 = some 220478113884612438 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 4 2 220478113884612438 220478113884612438 220478113884612438 endpoint_11_71_prefix_4 endpoint_11_71_window_4
private theorem endpoint_11_71_window_6 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 6 2 220478113884612438 = some 220478113884612438 := by decide +kernel
private theorem endpoint_11_71_prefix_8 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 8 220478113884612438 = some 220478113884612438 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 6 2 220478113884612438 220478113884612438 220478113884612438 endpoint_11_71_prefix_6 endpoint_11_71_window_6
private theorem endpoint_11_71_window_8 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 8 2 220478113884612438 = some 220478113884612438 := by decide +kernel
private theorem endpoint_11_71_prefix_10 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 10 220478113884612438 = some 220478113884612438 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 8 2 220478113884612438 220478113884612438 220478113884612438 endpoint_11_71_prefix_8 endpoint_11_71_window_8

def endpoint_11_71 : CertifiedEndpoint :=
  ⟨⟨11, 71, 2251⟩, 220478113884612438, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_11_71_flag endpoint_11_71_sources 10 220478113884612438 220478113884612438 rfl endpoint_11_71_base endpoint_11_71_prefix_10) (by decide)⟩
private def endpoint_11_72_flag : Flag := ⟨11, 72, 2178⟩
private def endpoint_11_72_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_11_72_base : receiptBase endpoint_11_72_flag endpoint_11_72_sources = some 216153425705341166 := by decide +kernel
private theorem endpoint_11_72_window_0 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 2 216153425705341166 = some 217370415316788154 := by decide +kernel
private theorem endpoint_11_72_window_2 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 2 2 217370415316788154 = some 217370415316788154 := by decide +kernel
private theorem endpoint_11_72_prefix_4 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 4 216153425705341166 = some 217370415316788154 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 2 2 216153425705341166 217370415316788154 217370415316788154 endpoint_11_72_window_0 endpoint_11_72_window_2
private theorem endpoint_11_72_window_4 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 4 2 217370415316788154 = some 217370415316788154 := by decide +kernel
private theorem endpoint_11_72_prefix_6 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 6 216153425705341166 = some 217370415316788154 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 4 2 216153425705341166 217370415316788154 217370415316788154 endpoint_11_72_prefix_4 endpoint_11_72_window_4
private theorem endpoint_11_72_window_6 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 6 2 217370415316788154 = some 217370415316788154 := by decide +kernel
private theorem endpoint_11_72_prefix_8 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 8 216153425705341166 = some 217370415316788154 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 6 2 216153425705341166 217370415316788154 217370415316788154 endpoint_11_72_prefix_6 endpoint_11_72_window_6
private theorem endpoint_11_72_window_8 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 8 2 217370415316788154 = some 217370415316788154 := by decide +kernel
private theorem endpoint_11_72_prefix_10 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 10 216153425705341166 = some 217370415316788154 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 8 2 216153425705341166 217370415316788154 217370415316788154 endpoint_11_72_prefix_8 endpoint_11_72_window_8

def endpoint_11_72 : CertifiedEndpoint :=
  ⟨⟨11, 72, 2178⟩, 217370415316788154, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_11_72_flag endpoint_11_72_sources 10 216153425705341166 217370415316788154 rfl endpoint_11_72_base endpoint_11_72_prefix_10) (by decide)⟩
private def endpoint_11_73_flag : Flag := ⟨11, 73, 2102⟩
private def endpoint_11_73_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_11_73_base : receiptBase endpoint_11_73_flag endpoint_11_73_sources = some 212805744272791850 := by decide +kernel
private theorem endpoint_11_73_window_0 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 2 212805744272791850 = some 212805744272791850 := by decide +kernel
private theorem endpoint_11_73_window_2 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 2 2 212805744272791850 = some 212805744272791850 := by decide +kernel
private theorem endpoint_11_73_prefix_4 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 4 212805744272791850 = some 212805744272791850 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 2 2 212805744272791850 212805744272791850 212805744272791850 endpoint_11_73_window_0 endpoint_11_73_window_2
private theorem endpoint_11_73_window_4 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 4 2 212805744272791850 = some 212805744272791850 := by decide +kernel
private theorem endpoint_11_73_prefix_6 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 6 212805744272791850 = some 212805744272791850 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 4 2 212805744272791850 212805744272791850 212805744272791850 endpoint_11_73_prefix_4 endpoint_11_73_window_4
private theorem endpoint_11_73_window_6 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 6 2 212805744272791850 = some 212805744272791850 := by decide +kernel
private theorem endpoint_11_73_prefix_8 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 8 212805744272791850 = some 212805744272791850 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 6 2 212805744272791850 212805744272791850 212805744272791850 endpoint_11_73_prefix_6 endpoint_11_73_window_6
private theorem endpoint_11_73_window_8 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 8 2 212805744272791850 = some 212805744272791850 := by decide +kernel
private theorem endpoint_11_73_prefix_10 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 10 212805744272791850 = some 212805744272791850 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 8 2 212805744272791850 212805744272791850 212805744272791850 endpoint_11_73_prefix_8 endpoint_11_73_window_8

def endpoint_11_73 : CertifiedEndpoint :=
  ⟨⟨11, 73, 2102⟩, 212805744272791850, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_11_73_flag endpoint_11_73_sources 10 212805744272791850 212805744272791850 rfl endpoint_11_73_base endpoint_11_73_prefix_10) (by decide)⟩

def endpointBlock06 : List CertifiedEndpoint := [
  endpoint_10_71, endpoint_10_72, endpoint_10_73, endpoint_10_74, endpoint_10_75, endpoint_10_76,
  endpoint_10_77, endpoint_10_78, endpoint_10_79, endpoint_10_80, endpoint_10_81, endpoint_10_82,
  endpoint_10_83, endpoint_10_84, endpoint_10_85, endpoint_10_86, endpoint_10_87, endpoint_10_88,
  endpoint_10_89, endpoint_10_90, endpoint_10_91, endpoint_10_92, endpoint_10_93, endpoint_11_11,
  endpoint_11_12, endpoint_11_13, endpoint_11_14, endpoint_11_15, endpoint_11_16, endpoint_11_17,
  endpoint_11_18, endpoint_11_19, endpoint_11_20, endpoint_11_21, endpoint_11_22, endpoint_11_23,
  endpoint_11_24, endpoint_11_25, endpoint_11_26, endpoint_11_27, endpoint_11_28, endpoint_11_29,
  endpoint_11_30, endpoint_11_31, endpoint_11_32, endpoint_11_33, endpoint_11_34, endpoint_11_35,
  endpoint_11_36, endpoint_11_37, endpoint_11_38, endpoint_11_39, endpoint_11_40, endpoint_11_41,
  endpoint_11_42, endpoint_11_43, endpoint_11_44, endpoint_11_45, endpoint_11_46, endpoint_11_47,
  endpoint_11_48, endpoint_11_49, endpoint_11_50, endpoint_11_51, endpoint_11_52, endpoint_11_53,
  endpoint_11_54, endpoint_11_55, endpoint_11_56, endpoint_11_57, endpoint_11_58, endpoint_11_59,
  endpoint_11_60, endpoint_11_61, endpoint_11_62, endpoint_11_63, endpoint_11_64, endpoint_11_65,
  endpoint_11_66, endpoint_11_67, endpoint_11_68, endpoint_11_69, endpoint_11_70, endpoint_11_71,
  endpoint_11_72, endpoint_11_73
]

end ProximityPrize.SubmissionLower.Koala6844Receipts
