import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_11_67_flag : Flag := ⟨11, 67, 2627⟩
private def endpoint_11_67_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_67_base : receiptBase endpoint_11_67_flag endpoint_11_67_sources = some 238482285127056588 := by decide +kernel
private theorem endpoint_11_67_w0 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 2 238482285127056588 = some 238482285127056588 := by decide +kernel
private theorem endpoint_11_67_w2 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 2 2 238482285127056588 = some 238482285127056588 := by decide +kernel
private theorem endpoint_11_67_p4 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 4 238482285127056588 = some 238482285127056588 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 2 2 238482285127056588 238482285127056588 238482285127056588 endpoint_11_67_w0 endpoint_11_67_w2
private theorem endpoint_11_67_w4 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 4 2 238482285127056588 = some 238482285127056588 := by decide +kernel
private theorem endpoint_11_67_p6 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 6 238482285127056588 = some 238482285127056588 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 4 2 238482285127056588 238482285127056588 238482285127056588 endpoint_11_67_p4 endpoint_11_67_w4
private theorem endpoint_11_67_w6 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 6 2 238482285127056588 = some 238482285127056588 := by decide +kernel
private theorem endpoint_11_67_p8 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 8 238482285127056588 = some 238482285127056588 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 6 2 238482285127056588 238482285127056588 238482285127056588 endpoint_11_67_p6 endpoint_11_67_w6
private theorem endpoint_11_67_w8 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 8 2 238482285127056588 = some 238482285127056588 := by decide +kernel
private theorem endpoint_11_67_p10 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 10 238482285127056588 = some 238482285127056588 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 8 2 238482285127056588 238482285127056588 238482285127056588 endpoint_11_67_p8 endpoint_11_67_w8
def endpoint_11_67 : CertifiedEndpoint :=
  ⟨⟨11, 67, 2627⟩, 238482285127056588, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_67_flag endpoint_11_67_sources 10 238482285127056588 238482285127056588 rfl endpoint_11_67_base endpoint_11_67_p10) (by decide)⟩
private def endpoint_11_68_flag : Flag := ⟨11, 68, 2566⟩
private def endpoint_11_68_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_68_base : receiptBase endpoint_11_68_flag endpoint_11_68_sources = some 236097089988083563 := by decide +kernel
private theorem endpoint_11_68_w0 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 2 236097089988083563 = some 236097089988083563 := by decide +kernel
private theorem endpoint_11_68_w2 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 2 2 236097089988083563 = some 236097089988083563 := by decide +kernel
private theorem endpoint_11_68_p4 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 4 236097089988083563 = some 236097089988083563 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 2 2 236097089988083563 236097089988083563 236097089988083563 endpoint_11_68_w0 endpoint_11_68_w2
private theorem endpoint_11_68_w4 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 4 2 236097089988083563 = some 236097089988083563 := by decide +kernel
private theorem endpoint_11_68_p6 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 6 236097089988083563 = some 236097089988083563 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 4 2 236097089988083563 236097089988083563 236097089988083563 endpoint_11_68_p4 endpoint_11_68_w4
private theorem endpoint_11_68_w6 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 6 2 236097089988083563 = some 236097089988083563 := by decide +kernel
private theorem endpoint_11_68_p8 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 8 236097089988083563 = some 236097089988083563 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 6 2 236097089988083563 236097089988083563 236097089988083563 endpoint_11_68_p6 endpoint_11_68_w6
private theorem endpoint_11_68_w8 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 8 2 236097089988083563 = some 236097089988083563 := by decide +kernel
private theorem endpoint_11_68_p10 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 10 236097089988083563 = some 236097089988083563 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 8 2 236097089988083563 236097089988083563 236097089988083563 endpoint_11_68_p8 endpoint_11_68_w8
def endpoint_11_68 : CertifiedEndpoint :=
  ⟨⟨11, 68, 2566⟩, 236097089988083563, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_68_flag endpoint_11_68_sources 10 236097089988083563 236097089988083563 rfl endpoint_11_68_base endpoint_11_68_p10) (by decide)⟩
private def endpoint_11_69_flag : Flag := ⟨11, 69, 2503⟩
private def endpoint_11_69_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_69_base : receiptBase endpoint_11_69_flag endpoint_11_69_sources = some 233379684207313085 := by decide +kernel
private theorem endpoint_11_69_w0 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 2 233379684207313085 = some 236005956945095556 := by decide +kernel
private theorem endpoint_11_69_w2 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 2 2 236005956945095556 = some 236005956945095556 := by decide +kernel
private theorem endpoint_11_69_p4 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 4 233379684207313085 = some 236005956945095556 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 2 2 233379684207313085 236005956945095556 236005956945095556 endpoint_11_69_w0 endpoint_11_69_w2
private theorem endpoint_11_69_w4 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 4 2 236005956945095556 = some 236005956945095556 := by decide +kernel
private theorem endpoint_11_69_p6 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 6 233379684207313085 = some 236005956945095556 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 4 2 233379684207313085 236005956945095556 236005956945095556 endpoint_11_69_p4 endpoint_11_69_w4
private theorem endpoint_11_69_w6 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 6 2 236005956945095556 = some 236005956945095556 := by decide +kernel
private theorem endpoint_11_69_p8 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 8 233379684207313085 = some 236005956945095556 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 6 2 233379684207313085 236005956945095556 236005956945095556 endpoint_11_69_p6 endpoint_11_69_w6
private theorem endpoint_11_69_w8 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 8 2 236005956945095556 = some 236005956945095556 := by decide +kernel
private theorem endpoint_11_69_p10 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 10 233379684207313085 = some 236005956945095556 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 8 2 233379684207313085 236005956945095556 236005956945095556 endpoint_11_69_p8 endpoint_11_69_w8
def endpoint_11_69 : CertifiedEndpoint :=
  ⟨⟨11, 69, 2503⟩, 236005956945095556, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_69_flag endpoint_11_69_sources 10 233379684207313085 236005956945095556 rfl endpoint_11_69_base endpoint_11_69_p10) (by decide)⟩
private def endpoint_11_70_flag : Flag := ⟨11, 70, 2438⟩
private def endpoint_11_70_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_11_70_base : receiptBase endpoint_11_70_flag endpoint_11_70_sources = some 235443615022284582 := by decide +kernel
private theorem endpoint_11_70_w0 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 2 235443615022284582 = some 235443615022284582 := by decide +kernel
private theorem endpoint_11_70_w2 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 2 2 235443615022284582 = some 235443615022284582 := by decide +kernel
private theorem endpoint_11_70_p4 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 4 235443615022284582 = some 235443615022284582 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 2 2 235443615022284582 235443615022284582 235443615022284582 endpoint_11_70_w0 endpoint_11_70_w2
private theorem endpoint_11_70_w4 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 4 2 235443615022284582 = some 235443615022284582 := by decide +kernel
private theorem endpoint_11_70_p6 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 6 235443615022284582 = some 235443615022284582 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 4 2 235443615022284582 235443615022284582 235443615022284582 endpoint_11_70_p4 endpoint_11_70_w4
private theorem endpoint_11_70_w6 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 6 2 235443615022284582 = some 235443615022284582 := by decide +kernel
private theorem endpoint_11_70_p8 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 8 235443615022284582 = some 235443615022284582 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 6 2 235443615022284582 235443615022284582 235443615022284582 endpoint_11_70_p6 endpoint_11_70_w6
private theorem endpoint_11_70_w8 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 8 2 235443615022284582 = some 235443615022284582 := by decide +kernel
private theorem endpoint_11_70_p10 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 10 235443615022284582 = some 235443615022284582 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 8 2 235443615022284582 235443615022284582 235443615022284582 endpoint_11_70_p8 endpoint_11_70_w8
def endpoint_11_70 : CertifiedEndpoint :=
  ⟨⟨11, 70, 2438⟩, 235443615022284582, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_11_70_flag endpoint_11_70_sources 10 235443615022284582 235443615022284582 rfl endpoint_11_70_base endpoint_11_70_p10) (by decide)⟩
private def endpoint_11_71_flag : Flag := ⟨11, 71, 2370⟩
private def endpoint_11_71_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_11_71_base : receiptBase endpoint_11_71_flag endpoint_11_71_sources = some 231912514745537389 := by decide +kernel
private theorem endpoint_11_71_w0 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 2 231912514745537389 = some 231912514745537389 := by decide +kernel
private theorem endpoint_11_71_w2 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 2 2 231912514745537389 = some 231912514745537389 := by decide +kernel
private theorem endpoint_11_71_p4 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 4 231912514745537389 = some 231912514745537389 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 2 2 231912514745537389 231912514745537389 231912514745537389 endpoint_11_71_w0 endpoint_11_71_w2
private theorem endpoint_11_71_w4 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 4 2 231912514745537389 = some 231912514745537389 := by decide +kernel
private theorem endpoint_11_71_p6 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 6 231912514745537389 = some 231912514745537389 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 4 2 231912514745537389 231912514745537389 231912514745537389 endpoint_11_71_p4 endpoint_11_71_w4
private theorem endpoint_11_71_w6 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 6 2 231912514745537389 = some 231912514745537389 := by decide +kernel
private theorem endpoint_11_71_p8 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 8 231912514745537389 = some 231912514745537389 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 6 2 231912514745537389 231912514745537389 231912514745537389 endpoint_11_71_p6 endpoint_11_71_w6
private theorem endpoint_11_71_w8 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 8 2 231912514745537389 = some 231912514745537389 := by decide +kernel
private theorem endpoint_11_71_p10 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 10 231912514745537389 = some 231912514745537389 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 8 2 231912514745537389 231912514745537389 231912514745537389 endpoint_11_71_p8 endpoint_11_71_w8
def endpoint_11_71 : CertifiedEndpoint :=
  ⟨⟨11, 71, 2370⟩, 231912514745537389, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_11_71_flag endpoint_11_71_sources 10 231912514745537389 231912514745537389 rfl endpoint_11_71_base endpoint_11_71_p10) (by decide)⟩
private def endpoint_11_72_flag : Flag := ⟨11, 72, 2299⟩
private def endpoint_11_72_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_11_72_base : receiptBase endpoint_11_72_flag endpoint_11_72_sources = some 227925655795834289 := by decide +kernel
private theorem endpoint_11_72_w0 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 2 227925655795834289 = some 227925655795834289 := by decide +kernel
private theorem endpoint_11_72_w2 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 2 2 227925655795834289 = some 227925655795834289 := by decide +kernel
private theorem endpoint_11_72_p4 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 4 227925655795834289 = some 227925655795834289 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 2 2 227925655795834289 227925655795834289 227925655795834289 endpoint_11_72_w0 endpoint_11_72_w2
private theorem endpoint_11_72_w4 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 4 2 227925655795834289 = some 227925655795834289 := by decide +kernel
private theorem endpoint_11_72_p6 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 6 227925655795834289 = some 227925655795834289 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 4 2 227925655795834289 227925655795834289 227925655795834289 endpoint_11_72_p4 endpoint_11_72_w4
private theorem endpoint_11_72_w6 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 6 2 227925655795834289 = some 227925655795834289 := by decide +kernel
private theorem endpoint_11_72_p8 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 8 227925655795834289 = some 227925655795834289 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 6 2 227925655795834289 227925655795834289 227925655795834289 endpoint_11_72_p6 endpoint_11_72_w6
private theorem endpoint_11_72_w8 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 8 2 227925655795834289 = some 227925655795834289 := by decide +kernel
private theorem endpoint_11_72_p10 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 10 227925655795834289 = some 227925655795834289 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 8 2 227925655795834289 227925655795834289 227925655795834289 endpoint_11_72_p8 endpoint_11_72_w8
def endpoint_11_72 : CertifiedEndpoint :=
  ⟨⟨11, 72, 2299⟩, 227925655795834289, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_11_72_flag endpoint_11_72_sources 10 227925655795834289 227925655795834289 rfl endpoint_11_72_base endpoint_11_72_p10) (by decide)⟩
private def endpoint_11_73_flag : Flag := ⟨11, 73, 2226⟩
private def endpoint_11_73_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_11_73_base : receiptBase endpoint_11_73_flag endpoint_11_73_sources = some 225203203620915458 := by decide +kernel
private theorem endpoint_11_73_w0 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 2 225203203620915458 = some 225203203620915458 := by decide +kernel
private theorem endpoint_11_73_w2 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 2 2 225203203620915458 = some 225203203620915458 := by decide +kernel
private theorem endpoint_11_73_p4 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 4 225203203620915458 = some 225203203620915458 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 2 2 225203203620915458 225203203620915458 225203203620915458 endpoint_11_73_w0 endpoint_11_73_w2
private theorem endpoint_11_73_w4 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 4 2 225203203620915458 = some 225203203620915458 := by decide +kernel
private theorem endpoint_11_73_p6 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 6 225203203620915458 = some 225203203620915458 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 4 2 225203203620915458 225203203620915458 225203203620915458 endpoint_11_73_p4 endpoint_11_73_w4
private theorem endpoint_11_73_w6 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 6 2 225203203620915458 = some 225203203620915458 := by decide +kernel
private theorem endpoint_11_73_p8 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 8 225203203620915458 = some 225203203620915458 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 6 2 225203203620915458 225203203620915458 225203203620915458 endpoint_11_73_p6 endpoint_11_73_w6
private theorem endpoint_11_73_w8 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 8 2 225203203620915458 = some 225203203620915458 := by decide +kernel
private theorem endpoint_11_73_p10 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 10 225203203620915458 = some 225203203620915458 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 8 2 225203203620915458 225203203620915458 225203203620915458 endpoint_11_73_p8 endpoint_11_73_w8
def endpoint_11_73 : CertifiedEndpoint :=
  ⟨⟨11, 73, 2226⟩, 225203203620915458, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_11_73_flag endpoint_11_73_sources 10 225203203620915458 225203203620915458 rfl endpoint_11_73_base endpoint_11_73_p10) (by decide)⟩
private def endpoint_11_74_flag : Flag := ⟨11, 74, 2150⟩
private def endpoint_11_74_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_11_74_base : receiptBase endpoint_11_74_flag endpoint_11_74_sources = some 220252972383033778 := by decide +kernel
private theorem endpoint_11_74_w0 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 2 220252972383033778 = some 220252972383033778 := by decide +kernel
private theorem endpoint_11_74_w2 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 2 2 220252972383033778 = some 220252972383033778 := by decide +kernel
private theorem endpoint_11_74_p4 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 4 220252972383033778 = some 220252972383033778 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 2 2 220252972383033778 220252972383033778 220252972383033778 endpoint_11_74_w0 endpoint_11_74_w2
private theorem endpoint_11_74_w4 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 4 2 220252972383033778 = some 220252972383033778 := by decide +kernel
private theorem endpoint_11_74_p6 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 6 220252972383033778 = some 220252972383033778 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 4 2 220252972383033778 220252972383033778 220252972383033778 endpoint_11_74_p4 endpoint_11_74_w4
private theorem endpoint_11_74_w6 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 6 2 220252972383033778 = some 220252972383033778 := by decide +kernel
private theorem endpoint_11_74_p8 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 8 220252972383033778 = some 220252972383033778 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 6 2 220252972383033778 220252972383033778 220252972383033778 endpoint_11_74_p6 endpoint_11_74_w6
private theorem endpoint_11_74_w8 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 8 2 220252972383033778 = some 220252972383033778 := by decide +kernel
private theorem endpoint_11_74_p10 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 10 220252972383033778 = some 220252972383033778 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 8 2 220252972383033778 220252972383033778 220252972383033778 endpoint_11_74_p8 endpoint_11_74_w8
def endpoint_11_74 : CertifiedEndpoint :=
  ⟨⟨11, 74, 2150⟩, 220252972383033778, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_11_74_flag endpoint_11_74_sources 10 220252972383033778 220252972383033778 rfl endpoint_11_74_base endpoint_11_74_p10) (by decide)⟩
private def endpoint_11_75_flag : Flag := ⟨11, 75, 2072⟩
private def endpoint_11_75_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_11_75_base : receiptBase endpoint_11_75_flag endpoint_11_75_sources = some 216671043936186174 := by decide +kernel
private theorem endpoint_11_75_w0 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 2 216671043936186174 = some 216671043936186174 := by decide +kernel
private theorem endpoint_11_75_w2 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 2 2 216671043936186174 = some 216671043936186174 := by decide +kernel
private theorem endpoint_11_75_p4 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 4 216671043936186174 = some 216671043936186174 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 2 2 216671043936186174 216671043936186174 216671043936186174 endpoint_11_75_w0 endpoint_11_75_w2
private theorem endpoint_11_75_w4 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 4 2 216671043936186174 = some 216671043936186174 := by decide +kernel
private theorem endpoint_11_75_p6 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 6 216671043936186174 = some 216671043936186174 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 4 2 216671043936186174 216671043936186174 216671043936186174 endpoint_11_75_p4 endpoint_11_75_w4
private theorem endpoint_11_75_w6 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 6 2 216671043936186174 = some 216671043936186174 := by decide +kernel
private theorem endpoint_11_75_p8 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 8 216671043936186174 = some 216671043936186174 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 6 2 216671043936186174 216671043936186174 216671043936186174 endpoint_11_75_p6 endpoint_11_75_w6
private theorem endpoint_11_75_w8 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 8 2 216671043936186174 = some 216671043936186174 := by decide +kernel
private theorem endpoint_11_75_p10 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 10 216671043936186174 = some 216671043936186174 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 8 2 216671043936186174 216671043936186174 216671043936186174 endpoint_11_75_p8 endpoint_11_75_w8
def endpoint_11_75 : CertifiedEndpoint :=
  ⟨⟨11, 75, 2072⟩, 216671043936186174, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_11_75_flag endpoint_11_75_sources 10 216671043936186174 216671043936186174 rfl endpoint_11_75_base endpoint_11_75_p10) (by decide)⟩
private def endpoint_11_76_flag : Flag := ⟨11, 76, 1991⟩
private def endpoint_11_76_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_11_76_base : receiptBase endpoint_11_76_flag endpoint_11_76_sources = some 210772590103219473 := by decide +kernel
private theorem endpoint_11_76_w0 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 2 210772590103219473 = some 210772590103219473 := by decide +kernel
private theorem endpoint_11_76_w2 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 2 2 210772590103219473 = some 210772590103219473 := by decide +kernel
private theorem endpoint_11_76_p4 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 4 210772590103219473 = some 210772590103219473 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 2 2 210772590103219473 210772590103219473 210772590103219473 endpoint_11_76_w0 endpoint_11_76_w2
private theorem endpoint_11_76_w4 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 4 2 210772590103219473 = some 210772590103219473 := by decide +kernel
private theorem endpoint_11_76_p6 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 6 210772590103219473 = some 210772590103219473 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 4 2 210772590103219473 210772590103219473 210772590103219473 endpoint_11_76_p4 endpoint_11_76_w4
private theorem endpoint_11_76_w6 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 6 2 210772590103219473 = some 210772590103219473 := by decide +kernel
private theorem endpoint_11_76_p8 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 8 210772590103219473 = some 210772590103219473 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 6 2 210772590103219473 210772590103219473 210772590103219473 endpoint_11_76_p6 endpoint_11_76_w6
private theorem endpoint_11_76_w8 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 8 2 210772590103219473 = some 210772590103219473 := by decide +kernel
private theorem endpoint_11_76_p10 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 10 210772590103219473 = some 210772590103219473 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 8 2 210772590103219473 210772590103219473 210772590103219473 endpoint_11_76_p8 endpoint_11_76_w8
def endpoint_11_76 : CertifiedEndpoint :=
  ⟨⟨11, 76, 1991⟩, 210772590103219473, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_11_76_flag endpoint_11_76_sources 10 210772590103219473 210772590103219473 rfl endpoint_11_76_base endpoint_11_76_p10) (by decide)⟩
private def endpoint_11_77_flag : Flag := ⟨11, 77, 1908⟩
private def endpoint_11_77_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_11_77_base : receiptBase endpoint_11_77_flag endpoint_11_77_sources = some 206219360574532474 := by decide +kernel
private theorem endpoint_11_77_w0 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 2 206219360574532474 = some 206219360574532474 := by decide +kernel
private theorem endpoint_11_77_w2 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 2 2 206219360574532474 = some 206219360574532474 := by decide +kernel
private theorem endpoint_11_77_p4 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 4 206219360574532474 = some 206219360574532474 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 2 2 206219360574532474 206219360574532474 206219360574532474 endpoint_11_77_w0 endpoint_11_77_w2
private theorem endpoint_11_77_w4 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 4 2 206219360574532474 = some 206219360574532474 := by decide +kernel
private theorem endpoint_11_77_p6 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 6 206219360574532474 = some 206219360574532474 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 4 2 206219360574532474 206219360574532474 206219360574532474 endpoint_11_77_p4 endpoint_11_77_w4
private theorem endpoint_11_77_w6 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 6 2 206219360574532474 = some 206219360574532474 := by decide +kernel
private theorem endpoint_11_77_p8 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 8 206219360574532474 = some 206219360574532474 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 6 2 206219360574532474 206219360574532474 206219360574532474 endpoint_11_77_p6 endpoint_11_77_w6
private theorem endpoint_11_77_w8 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 8 2 206219360574532474 = some 206219360574532474 := by decide +kernel
private theorem endpoint_11_77_p10 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 10 206219360574532474 = some 206219360574532474 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 8 2 206219360574532474 206219360574532474 206219360574532474 endpoint_11_77_p8 endpoint_11_77_w8
def endpoint_11_77 : CertifiedEndpoint :=
  ⟨⟨11, 77, 1908⟩, 206219360574532474, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_11_77_flag endpoint_11_77_sources 10 206219360574532474 206219360574532474 rfl endpoint_11_77_base endpoint_11_77_p10) (by decide)⟩
private def endpoint_11_78_flag : Flag := ⟨11, 78, 1822⟩
private def endpoint_11_78_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_11_78_base : receiptBase endpoint_11_78_flag endpoint_11_78_sources = some 199287104181582300 := by decide +kernel
private theorem endpoint_11_78_w0 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 2 199287104181582300 = some 199287104181582300 := by decide +kernel
private theorem endpoint_11_78_w2 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 2 2 199287104181582300 = some 199287104181582300 := by decide +kernel
private theorem endpoint_11_78_p4 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 4 199287104181582300 = some 199287104181582300 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 2 2 199287104181582300 199287104181582300 199287104181582300 endpoint_11_78_w0 endpoint_11_78_w2
private theorem endpoint_11_78_w4 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 4 2 199287104181582300 = some 199287104181582300 := by decide +kernel
private theorem endpoint_11_78_p6 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 6 199287104181582300 = some 199287104181582300 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 4 2 199287104181582300 199287104181582300 199287104181582300 endpoint_11_78_p4 endpoint_11_78_w4
private theorem endpoint_11_78_w6 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 6 2 199287104181582300 = some 199287104181582300 := by decide +kernel
private theorem endpoint_11_78_p8 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 8 199287104181582300 = some 199287104181582300 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 6 2 199287104181582300 199287104181582300 199287104181582300 endpoint_11_78_p6 endpoint_11_78_w6
private theorem endpoint_11_78_w8 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 8 2 199287104181582300 = some 199287104181582300 := by decide +kernel
private theorem endpoint_11_78_p10 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 10 199287104181582300 = some 199287104181582300 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 8 2 199287104181582300 199287104181582300 199287104181582300 endpoint_11_78_p8 endpoint_11_78_w8
def endpoint_11_78 : CertifiedEndpoint :=
  ⟨⟨11, 78, 1822⟩, 199287104181582300, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_11_78_flag endpoint_11_78_sources 10 199287104181582300 199287104181582300 rfl endpoint_11_78_base endpoint_11_78_p10) (by decide)⟩
private def endpoint_11_79_flag : Flag := ⟨11, 79, 1733⟩
private def endpoint_11_79_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_11_79_base : receiptBase endpoint_11_79_flag endpoint_11_79_sources = some 191809917260609937 := by decide +kernel
private theorem endpoint_11_79_w0 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 2 191809917260609937 = some 191809917260609937 := by decide +kernel
private theorem endpoint_11_79_w2 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 2 2 191809917260609937 = some 191809917260609937 := by decide +kernel
private theorem endpoint_11_79_p4 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 4 191809917260609937 = some 191809917260609937 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 2 2 191809917260609937 191809917260609937 191809917260609937 endpoint_11_79_w0 endpoint_11_79_w2
private theorem endpoint_11_79_w4 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 4 2 191809917260609937 = some 191809917260609937 := by decide +kernel
private theorem endpoint_11_79_p6 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 6 191809917260609937 = some 191809917260609937 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 4 2 191809917260609937 191809917260609937 191809917260609937 endpoint_11_79_p4 endpoint_11_79_w4
private theorem endpoint_11_79_w6 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 6 2 191809917260609937 = some 191809917260609937 := by decide +kernel
private theorem endpoint_11_79_p8 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 8 191809917260609937 = some 191809917260609937 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 6 2 191809917260609937 191809917260609937 191809917260609937 endpoint_11_79_p6 endpoint_11_79_w6
private theorem endpoint_11_79_w8 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 8 2 191809917260609937 = some 191809917260609937 := by decide +kernel
private theorem endpoint_11_79_p10 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 10 191809917260609937 = some 191809917260609937 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 8 2 191809917260609937 191809917260609937 191809917260609937 endpoint_11_79_p8 endpoint_11_79_w8
def endpoint_11_79 : CertifiedEndpoint :=
  ⟨⟨11, 79, 1733⟩, 191809917260609937, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_11_79_flag endpoint_11_79_sources 10 191809917260609937 191809917260609937 rfl endpoint_11_79_base endpoint_11_79_p10) (by decide)⟩
private def endpoint_11_80_flag : Flag := ⟨11, 80, 1641⟩
private def endpoint_11_80_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_11_80_base : receiptBase endpoint_11_80_flag endpoint_11_80_sources = some 187121138629054890 := by decide +kernel
private theorem endpoint_11_80_w0 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 2 187121138629054890 = some 187121138629054890 := by decide +kernel
private theorem endpoint_11_80_w2 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 2 2 187121138629054890 = some 187121138629054890 := by decide +kernel
private theorem endpoint_11_80_p4 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 4 187121138629054890 = some 187121138629054890 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 2 2 187121138629054890 187121138629054890 187121138629054890 endpoint_11_80_w0 endpoint_11_80_w2
private theorem endpoint_11_80_w4 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 4 2 187121138629054890 = some 187121138629054890 := by decide +kernel
private theorem endpoint_11_80_p6 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 6 187121138629054890 = some 187121138629054890 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 4 2 187121138629054890 187121138629054890 187121138629054890 endpoint_11_80_p4 endpoint_11_80_w4
private theorem endpoint_11_80_w6 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 6 2 187121138629054890 = some 187121138629054890 := by decide +kernel
private theorem endpoint_11_80_p8 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 8 187121138629054890 = some 187121138629054890 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 6 2 187121138629054890 187121138629054890 187121138629054890 endpoint_11_80_p6 endpoint_11_80_w6
private theorem endpoint_11_80_w8 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 8 2 187121138629054890 = some 187121138629054890 := by decide +kernel
private theorem endpoint_11_80_p10 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 10 187121138629054890 = some 187121138629054890 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 8 2 187121138629054890 187121138629054890 187121138629054890 endpoint_11_80_p8 endpoint_11_80_w8
def endpoint_11_80 : CertifiedEndpoint :=
  ⟨⟨11, 80, 1641⟩, 187121138629054890, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_11_80_flag endpoint_11_80_sources 10 187121138629054890 187121138629054890 rfl endpoint_11_80_base endpoint_11_80_p10) (by decide)⟩
private def endpoint_11_81_flag : Flag := ⟨11, 81, 1547⟩
private def endpoint_11_81_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_11_81_base : receiptBase endpoint_11_81_flag endpoint_11_81_sources = some 178422660407667313 := by decide +kernel
private theorem endpoint_11_81_w0 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 2 178422660407667313 = some 178422660407667313 := by decide +kernel
private theorem endpoint_11_81_w2 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 2 2 178422660407667313 = some 178422660407667313 := by decide +kernel
private theorem endpoint_11_81_p4 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 4 178422660407667313 = some 178422660407667313 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 2 2 178422660407667313 178422660407667313 178422660407667313 endpoint_11_81_w0 endpoint_11_81_w2
private theorem endpoint_11_81_w4 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 4 2 178422660407667313 = some 178422660407667313 := by decide +kernel
private theorem endpoint_11_81_p6 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 6 178422660407667313 = some 178422660407667313 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 4 2 178422660407667313 178422660407667313 178422660407667313 endpoint_11_81_p4 endpoint_11_81_w4
private theorem endpoint_11_81_w6 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 6 2 178422660407667313 = some 178422660407667313 := by decide +kernel
private theorem endpoint_11_81_p8 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 8 178422660407667313 = some 178422660407667313 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 6 2 178422660407667313 178422660407667313 178422660407667313 endpoint_11_81_p6 endpoint_11_81_w6
private theorem endpoint_11_81_w8 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 8 2 178422660407667313 = some 178422660407667313 := by decide +kernel
private theorem endpoint_11_81_p10 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 10 178422660407667313 = some 178422660407667313 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 8 2 178422660407667313 178422660407667313 178422660407667313 endpoint_11_81_p8 endpoint_11_81_w8
def endpoint_11_81 : CertifiedEndpoint :=
  ⟨⟨11, 81, 1547⟩, 178422660407667313, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_11_81_flag endpoint_11_81_sources 10 178422660407667313 178422660407667313 rfl endpoint_11_81_base endpoint_11_81_p10) (by decide)⟩
private def endpoint_11_82_flag : Flag := ⟨11, 82, 1451⟩
private def endpoint_11_82_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_11_82_base : receiptBase endpoint_11_82_flag endpoint_11_82_sources = some 170468132458877551 := by decide +kernel
private theorem endpoint_11_82_w0 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 2 170468132458877551 = some 170468132458877551 := by decide +kernel
private theorem endpoint_11_82_w2 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 2 2 170468132458877551 = some 170468132458877551 := by decide +kernel
private theorem endpoint_11_82_p4 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 4 170468132458877551 = some 170468132458877551 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 2 2 170468132458877551 170468132458877551 170468132458877551 endpoint_11_82_w0 endpoint_11_82_w2
private theorem endpoint_11_82_w4 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 4 2 170468132458877551 = some 170468132458877551 := by decide +kernel
private theorem endpoint_11_82_p6 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 6 170468132458877551 = some 170468132458877551 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 4 2 170468132458877551 170468132458877551 170468132458877551 endpoint_11_82_p4 endpoint_11_82_w4
private theorem endpoint_11_82_w6 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 6 2 170468132458877551 = some 170468132458877551 := by decide +kernel
private theorem endpoint_11_82_p8 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 8 170468132458877551 = some 170468132458877551 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 6 2 170468132458877551 170468132458877551 170468132458877551 endpoint_11_82_p6 endpoint_11_82_w6
private theorem endpoint_11_82_w8 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 8 2 170468132458877551 = some 170468132458877551 := by decide +kernel
private theorem endpoint_11_82_p10 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 10 170468132458877551 = some 170468132458877551 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 8 2 170468132458877551 170468132458877551 170468132458877551 endpoint_11_82_p8 endpoint_11_82_w8
def endpoint_11_82 : CertifiedEndpoint :=
  ⟨⟨11, 82, 1451⟩, 170468132458877551, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_11_82_flag endpoint_11_82_sources 10 170468132458877551 170468132458877551 rfl endpoint_11_82_base endpoint_11_82_p10) (by decide)⟩
private def endpoint_11_83_flag : Flag := ⟨11, 83, 1351⟩
private def endpoint_11_83_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_11_83_base : receiptBase endpoint_11_83_flag endpoint_11_83_sources = some 160541101481302173 := by decide +kernel
private theorem endpoint_11_83_w0 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 0 2 160541101481302173 = some 160541101481302173 := by decide +kernel
private theorem endpoint_11_83_w2 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 2 2 160541101481302173 = some 160541101481302173 := by decide +kernel
private theorem endpoint_11_83_p4 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 0 4 160541101481302173 = some 160541101481302173 :=
  join_receipt_window endpoint_11_83_flag endpoint_11_83_sources 0 2 2 160541101481302173 160541101481302173 160541101481302173 endpoint_11_83_w0 endpoint_11_83_w2
private theorem endpoint_11_83_w4 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 4 2 160541101481302173 = some 160541101481302173 := by decide +kernel
private theorem endpoint_11_83_p6 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 0 6 160541101481302173 = some 160541101481302173 :=
  join_receipt_window endpoint_11_83_flag endpoint_11_83_sources 0 4 2 160541101481302173 160541101481302173 160541101481302173 endpoint_11_83_p4 endpoint_11_83_w4
private theorem endpoint_11_83_w6 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 6 2 160541101481302173 = some 160541101481302173 := by decide +kernel
private theorem endpoint_11_83_p8 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 0 8 160541101481302173 = some 160541101481302173 :=
  join_receipt_window endpoint_11_83_flag endpoint_11_83_sources 0 6 2 160541101481302173 160541101481302173 160541101481302173 endpoint_11_83_p6 endpoint_11_83_w6
private theorem endpoint_11_83_w8 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 8 2 160541101481302173 = some 160541101481302173 := by decide +kernel
private theorem endpoint_11_83_p10 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 0 10 160541101481302173 = some 160541101481302173 :=
  join_receipt_window endpoint_11_83_flag endpoint_11_83_sources 0 8 2 160541101481302173 160541101481302173 160541101481302173 endpoint_11_83_p8 endpoint_11_83_w8
def endpoint_11_83 : CertifiedEndpoint :=
  ⟨⟨11, 83, 1351⟩, 160541101481302173, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_11_83_flag endpoint_11_83_sources 10 160541101481302173 160541101481302173 rfl endpoint_11_83_base endpoint_11_83_p10) (by decide)⟩
def endpoint_11_84 : CertifiedEndpoint :=
  ⟨⟨11, 84, 1249⟩, 254946168117019933, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_85 : CertifiedEndpoint :=
  ⟨⟨11, 85, 1145⟩, 235804063963387174, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_86 : CertifiedEndpoint :=
  ⟨⟨11, 86, 1037⟩, 215225961514771001, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_87 : CertifiedEndpoint :=
  ⟨⟨11, 87, 927⟩, 193619051116190212, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_88 : CertifiedEndpoint :=
  ⟨⟨11, 88, 815⟩, 170967045843497755, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_89 : CertifiedEndpoint :=
  ⟨⟨11, 89, 699⟩, 146803036629802308, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_90 : CertifiedEndpoint :=
  ⟨⟨11, 90, 581⟩, 121550500744269721, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_91 : CertifiedEndpoint :=
  ⟨⟨11, 91, 461⟩, 95193151262752942, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_92 : CertifiedEndpoint :=
  ⟨⟨11, 92, 337⟩, 67247792194213597, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_93 : CertifiedEndpoint :=
  ⟨⟨11, 93, 211⟩, 38154187731964588, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_12 : CertifiedEndpoint :=
  ⟨⟨12, 12, 4168⟩, 84670077552082128, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_13 : CertifiedEndpoint :=
  ⟨⟨12, 13, 4149⟩, 88297054013558554, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_14 : CertifiedEndpoint :=
  ⟨⟨12, 14, 4129⟩, 91864844300860819, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_15 : CertifiedEndpoint :=
  ⟨⟨12, 15, 4110⟩, 103613754193646283, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_16 : CertifiedEndpoint :=
  ⟨⟨12, 16, 4090⟩, 115218504166118366, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_17 : CertifiedEndpoint :=
  ⟨⟨12, 17, 4070⟩, 126701394279419595, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_18 : CertifiedEndpoint :=
  ⟨⟨12, 18, 4049⟩, 138028235705659067, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_19 : CertifiedEndpoint :=
  ⟨⟨12, 19, 4029⟩, 149264433908931494, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_20 : CertifiedEndpoint :=
  ⟨⟨12, 20, 4008⟩, 160338639041767976, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_21 : CertifiedEndpoint :=
  ⟨⟨12, 21, 3987⟩, 171285039932059416, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_22 : CertifiedEndpoint :=
  ⟨⟨12, 22, 3966⟩, 182103636579805814, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_23 : CertifiedEndpoint :=
  ⟨⟨12, 23, 3944⟩, 192745379198680797, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_24 : CertifiedEndpoint :=
  ⟨⟨12, 24, 3922⟩, 203253373191636550, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_25 : CertifiedEndpoint :=
  ⟨⟨12, 25, 3900⟩, 213627618558673073, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_26 : CertifiedEndpoint :=
  ⟨⟨12, 26, 3878⟩, 223868115299790366, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_27 : CertifiedEndpoint :=
  ⟨⟨12, 27, 3856⟩, 233974863414988429, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_28 : CertifiedEndpoint :=
  ⟨⟨12, 28, 3833⟩, 243883952159505419, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_29 : CertifiedEndpoint :=
  ⟨⟨12, 29, 3810⟩, 253653347894728991, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_12_30_flag : Flag := ⟨12, 30, 3787⟩
private def endpoint_12_30_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_30_base : receiptBase endpoint_12_30_flag endpoint_12_30_sources = some 175473813333197032 := by decide +kernel
private theorem endpoint_12_30_w0 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 2 175473813333197032 = some 175473813333197032 := by decide +kernel
private theorem endpoint_12_30_w2 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 2 2 175473813333197032 = some 175473813333197032 := by decide +kernel
private theorem endpoint_12_30_p4 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 4 175473813333197032 = some 175473813333197032 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 2 2 175473813333197032 175473813333197032 175473813333197032 endpoint_12_30_w0 endpoint_12_30_w2
private theorem endpoint_12_30_w4 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 4 2 175473813333197032 = some 175473813333197032 := by decide +kernel
private theorem endpoint_12_30_p6 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 6 175473813333197032 = some 175473813333197032 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 4 2 175473813333197032 175473813333197032 175473813333197032 endpoint_12_30_p4 endpoint_12_30_w4
private theorem endpoint_12_30_w6 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 6 2 175473813333197032 = some 175473813333197032 := by decide +kernel
private theorem endpoint_12_30_p8 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 8 175473813333197032 = some 175473813333197032 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 6 2 175473813333197032 175473813333197032 175473813333197032 endpoint_12_30_p6 endpoint_12_30_w6
private theorem endpoint_12_30_w8 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 8 2 175473813333197032 = some 175473813333197032 := by decide +kernel
private theorem endpoint_12_30_p10 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 10 175473813333197032 = some 175473813333197032 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 8 2 175473813333197032 175473813333197032 175473813333197032 endpoint_12_30_p8 endpoint_12_30_w8
private theorem endpoint_12_30_w10 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 10 1 175473813333197032 = some 175473813333197032 := by decide +kernel
private theorem endpoint_12_30_p11 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 11 175473813333197032 = some 175473813333197032 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 10 1 175473813333197032 175473813333197032 175473813333197032 endpoint_12_30_p10 endpoint_12_30_w10
def endpoint_12_30 : CertifiedEndpoint :=
  ⟨⟨12, 30, 3787⟩, 175473813333197032, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_30_flag endpoint_12_30_sources 11 175473813333197032 175473813333197032 rfl endpoint_12_30_base endpoint_12_30_p11) (by decide)⟩
private def endpoint_12_31_flag : Flag := ⟨12, 31, 3763⟩
private def endpoint_12_31_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_31_base : receiptBase endpoint_12_31_flag endpoint_12_31_sources = some 179072355193380789 := by decide +kernel
private theorem endpoint_12_31_w0 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 2 179072355193380789 = some 179072355193380789 := by decide +kernel
private theorem endpoint_12_31_w2 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 2 2 179072355193380789 = some 179072355193380789 := by decide +kernel
private theorem endpoint_12_31_p4 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 4 179072355193380789 = some 179072355193380789 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 2 2 179072355193380789 179072355193380789 179072355193380789 endpoint_12_31_w0 endpoint_12_31_w2
private theorem endpoint_12_31_w4 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 4 2 179072355193380789 = some 179072355193380789 := by decide +kernel
private theorem endpoint_12_31_p6 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 6 179072355193380789 = some 179072355193380789 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 4 2 179072355193380789 179072355193380789 179072355193380789 endpoint_12_31_p4 endpoint_12_31_w4
private theorem endpoint_12_31_w6 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 6 2 179072355193380789 = some 179072355193380789 := by decide +kernel
private theorem endpoint_12_31_p8 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 8 179072355193380789 = some 179072355193380789 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 6 2 179072355193380789 179072355193380789 179072355193380789 endpoint_12_31_p6 endpoint_12_31_w6
private theorem endpoint_12_31_w8 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 8 2 179072355193380789 = some 179072355193380789 := by decide +kernel
private theorem endpoint_12_31_p10 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 10 179072355193380789 = some 179072355193380789 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 8 2 179072355193380789 179072355193380789 179072355193380789 endpoint_12_31_p8 endpoint_12_31_w8
private theorem endpoint_12_31_w10 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 10 1 179072355193380789 = some 179072355193380789 := by decide +kernel
private theorem endpoint_12_31_p11 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 11 179072355193380789 = some 179072355193380789 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 10 1 179072355193380789 179072355193380789 179072355193380789 endpoint_12_31_p10 endpoint_12_31_w10
def endpoint_12_31 : CertifiedEndpoint :=
  ⟨⟨12, 31, 3763⟩, 179072355193380789, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_31_flag endpoint_12_31_sources 11 179072355193380789 179072355193380789 rfl endpoint_12_31_base endpoint_12_31_p11) (by decide)⟩
private def endpoint_12_32_flag : Flag := ⟨12, 32, 3739⟩
private def endpoint_12_32_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_32_base : receiptBase endpoint_12_32_flag endpoint_12_32_sources = some 182611055519917854 := by decide +kernel
private theorem endpoint_12_32_w0 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 2 182611055519917854 = some 182611055519917854 := by decide +kernel
private theorem endpoint_12_32_w2 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 2 2 182611055519917854 = some 182611055519917854 := by decide +kernel
private theorem endpoint_12_32_p4 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 4 182611055519917854 = some 182611055519917854 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 2 2 182611055519917854 182611055519917854 182611055519917854 endpoint_12_32_w0 endpoint_12_32_w2
private theorem endpoint_12_32_w4 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 4 2 182611055519917854 = some 182611055519917854 := by decide +kernel
private theorem endpoint_12_32_p6 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 6 182611055519917854 = some 182611055519917854 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 4 2 182611055519917854 182611055519917854 182611055519917854 endpoint_12_32_p4 endpoint_12_32_w4
private theorem endpoint_12_32_w6 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 6 2 182611055519917854 = some 182611055519917854 := by decide +kernel
private theorem endpoint_12_32_p8 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 8 182611055519917854 = some 182611055519917854 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 6 2 182611055519917854 182611055519917854 182611055519917854 endpoint_12_32_p6 endpoint_12_32_w6
private theorem endpoint_12_32_w8 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 8 2 182611055519917854 = some 182611055519917854 := by decide +kernel
private theorem endpoint_12_32_p10 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 10 182611055519917854 = some 182611055519917854 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 8 2 182611055519917854 182611055519917854 182611055519917854 endpoint_12_32_p8 endpoint_12_32_w8
private theorem endpoint_12_32_w10 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 10 1 182611055519917854 = some 182611055519917854 := by decide +kernel
private theorem endpoint_12_32_p11 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 11 182611055519917854 = some 182611055519917854 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 10 1 182611055519917854 182611055519917854 182611055519917854 endpoint_12_32_p10 endpoint_12_32_w10
def endpoint_12_32 : CertifiedEndpoint :=
  ⟨⟨12, 32, 3739⟩, 182611055519917854, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_32_flag endpoint_12_32_sources 11 182611055519917854 182611055519917854 rfl endpoint_12_32_base endpoint_12_32_p11) (by decide)⟩
private def endpoint_12_33_flag : Flag := ⟨12, 33, 3715⟩
private def endpoint_12_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_33_base : receiptBase endpoint_12_33_flag endpoint_12_33_sources = some 186089914312808226 := by decide +kernel
private theorem endpoint_12_33_w0 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 2 186089914312808226 = some 186089914312808226 := by decide +kernel
private theorem endpoint_12_33_w2 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 2 2 186089914312808226 = some 186089914312808226 := by decide +kernel
private theorem endpoint_12_33_p4 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 4 186089914312808226 = some 186089914312808226 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 2 2 186089914312808226 186089914312808226 186089914312808226 endpoint_12_33_w0 endpoint_12_33_w2
private theorem endpoint_12_33_w4 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 4 2 186089914312808226 = some 186089914312808226 := by decide +kernel
private theorem endpoint_12_33_p6 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 6 186089914312808226 = some 186089914312808226 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 4 2 186089914312808226 186089914312808226 186089914312808226 endpoint_12_33_p4 endpoint_12_33_w4
private theorem endpoint_12_33_w6 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 6 2 186089914312808226 = some 186089914312808226 := by decide +kernel
private theorem endpoint_12_33_p8 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 8 186089914312808226 = some 186089914312808226 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 6 2 186089914312808226 186089914312808226 186089914312808226 endpoint_12_33_p6 endpoint_12_33_w6
private theorem endpoint_12_33_w8 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 8 2 186089914312808226 = some 186089914312808226 := by decide +kernel
private theorem endpoint_12_33_p10 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 10 186089914312808226 = some 186089914312808226 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 8 2 186089914312808226 186089914312808226 186089914312808226 endpoint_12_33_p8 endpoint_12_33_w8
private theorem endpoint_12_33_w10 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 10 1 186089914312808226 = some 186089914312808226 := by decide +kernel
private theorem endpoint_12_33_p11 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 11 186089914312808226 = some 186089914312808226 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 10 1 186089914312808226 186089914312808226 186089914312808226 endpoint_12_33_p10 endpoint_12_33_w10
def endpoint_12_33 : CertifiedEndpoint :=
  ⟨⟨12, 33, 3715⟩, 186089914312808226, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_33_flag endpoint_12_33_sources 11 186089914312808226 186089914312808226 rfl endpoint_12_33_base endpoint_12_33_p11) (by decide)⟩
private def endpoint_12_34_flag : Flag := ⟨12, 34, 3690⟩
private def endpoint_12_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_34_base : receiptBase endpoint_12_34_flag endpoint_12_34_sources = some 189458386588694616 := by decide +kernel
private theorem endpoint_12_34_w0 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 2 189458386588694616 = some 189458386588694616 := by decide +kernel
private theorem endpoint_12_34_w2 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 2 2 189458386588694616 = some 189458386588694616 := by decide +kernel
private theorem endpoint_12_34_p4 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 4 189458386588694616 = some 189458386588694616 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 2 2 189458386588694616 189458386588694616 189458386588694616 endpoint_12_34_w0 endpoint_12_34_w2
private theorem endpoint_12_34_w4 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 4 2 189458386588694616 = some 189458386588694616 := by decide +kernel
private theorem endpoint_12_34_p6 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 6 189458386588694616 = some 189458386588694616 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 4 2 189458386588694616 189458386588694616 189458386588694616 endpoint_12_34_p4 endpoint_12_34_w4
private theorem endpoint_12_34_w6 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 6 2 189458386588694616 = some 189458386588694616 := by decide +kernel
private theorem endpoint_12_34_p8 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 8 189458386588694616 = some 189458386588694616 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 6 2 189458386588694616 189458386588694616 189458386588694616 endpoint_12_34_p6 endpoint_12_34_w6
private theorem endpoint_12_34_w8 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 8 2 189458386588694616 = some 189458386588694616 := by decide +kernel
private theorem endpoint_12_34_p10 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 10 189458386588694616 = some 189458386588694616 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 8 2 189458386588694616 189458386588694616 189458386588694616 endpoint_12_34_p8 endpoint_12_34_w8
private theorem endpoint_12_34_w10 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 10 1 189458386588694616 = some 189458386588694616 := by decide +kernel
private theorem endpoint_12_34_p11 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 11 189458386588694616 = some 189458386588694616 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 10 1 189458386588694616 189458386588694616 189458386588694616 endpoint_12_34_p10 endpoint_12_34_w10
def endpoint_12_34 : CertifiedEndpoint :=
  ⟨⟨12, 34, 3690⟩, 189458386588694616, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_34_flag endpoint_12_34_sources 11 189458386588694616 189458386588694616 rfl endpoint_12_34_base endpoint_12_34_p11) (by decide)⟩
private def endpoint_12_35_flag : Flag := ⟨12, 35, 3665⟩
private def endpoint_12_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_35_base : receiptBase endpoint_12_35_flag endpoint_12_35_sources = some 192764575003014246 := by decide +kernel
private theorem endpoint_12_35_w0 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 2 192764575003014246 = some 192764575003014246 := by decide +kernel
private theorem endpoint_12_35_w2 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 2 2 192764575003014246 = some 192764575003014246 := by decide +kernel
private theorem endpoint_12_35_p4 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 4 192764575003014246 = some 192764575003014246 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 2 2 192764575003014246 192764575003014246 192764575003014246 endpoint_12_35_w0 endpoint_12_35_w2
private theorem endpoint_12_35_w4 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 4 2 192764575003014246 = some 192764575003014246 := by decide +kernel
private theorem endpoint_12_35_p6 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 6 192764575003014246 = some 192764575003014246 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 4 2 192764575003014246 192764575003014246 192764575003014246 endpoint_12_35_p4 endpoint_12_35_w4
private theorem endpoint_12_35_w6 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 6 2 192764575003014246 = some 192764575003014246 := by decide +kernel
private theorem endpoint_12_35_p8 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 8 192764575003014246 = some 192764575003014246 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 6 2 192764575003014246 192764575003014246 192764575003014246 endpoint_12_35_p6 endpoint_12_35_w6
private theorem endpoint_12_35_w8 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 8 2 192764575003014246 = some 192764575003014246 := by decide +kernel
private theorem endpoint_12_35_p10 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 10 192764575003014246 = some 192764575003014246 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 8 2 192764575003014246 192764575003014246 192764575003014246 endpoint_12_35_p8 endpoint_12_35_w8
private theorem endpoint_12_35_w10 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 10 1 192764575003014246 = some 192764575003014246 := by decide +kernel
private theorem endpoint_12_35_p11 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 11 192764575003014246 = some 192764575003014246 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 10 1 192764575003014246 192764575003014246 192764575003014246 endpoint_12_35_p10 endpoint_12_35_w10
def endpoint_12_35 : CertifiedEndpoint :=
  ⟨⟨12, 35, 3665⟩, 192764575003014246, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_35_flag endpoint_12_35_sources 11 192764575003014246 192764575003014246 rfl endpoint_12_35_base endpoint_12_35_p11) (by decide)⟩
private def endpoint_12_36_flag : Flag := ⟨12, 36, 3640⟩
private def endpoint_12_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_36_base : receiptBase endpoint_12_36_flag endpoint_12_36_sources = some 196008479555767114 := by decide +kernel
private theorem endpoint_12_36_w0 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 2 196008479555767114 = some 196008479555767114 := by decide +kernel
private theorem endpoint_12_36_w2 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 2 2 196008479555767114 = some 196008479555767114 := by decide +kernel
private theorem endpoint_12_36_p4 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 4 196008479555767114 = some 196008479555767114 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 2 2 196008479555767114 196008479555767114 196008479555767114 endpoint_12_36_w0 endpoint_12_36_w2
private theorem endpoint_12_36_w4 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 4 2 196008479555767114 = some 196008479555767114 := by decide +kernel
private theorem endpoint_12_36_p6 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 6 196008479555767114 = some 196008479555767114 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 4 2 196008479555767114 196008479555767114 196008479555767114 endpoint_12_36_p4 endpoint_12_36_w4
private theorem endpoint_12_36_w6 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 6 2 196008479555767114 = some 196008479555767114 := by decide +kernel
private theorem endpoint_12_36_p8 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 8 196008479555767114 = some 196008479555767114 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 6 2 196008479555767114 196008479555767114 196008479555767114 endpoint_12_36_p6 endpoint_12_36_w6
private theorem endpoint_12_36_w8 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 8 2 196008479555767114 = some 196008479555767114 := by decide +kernel
private theorem endpoint_12_36_p10 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 10 196008479555767114 = some 196008479555767114 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 8 2 196008479555767114 196008479555767114 196008479555767114 endpoint_12_36_p8 endpoint_12_36_w8
private theorem endpoint_12_36_w10 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 10 1 196008479555767114 = some 196008479555767114 := by decide +kernel
private theorem endpoint_12_36_p11 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 11 196008479555767114 = some 196008479555767114 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 10 1 196008479555767114 196008479555767114 196008479555767114 endpoint_12_36_p10 endpoint_12_36_w10
def endpoint_12_36 : CertifiedEndpoint :=
  ⟨⟨12, 36, 3640⟩, 196008479555767114, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_36_flag endpoint_12_36_sources 11 196008479555767114 196008479555767114 rfl endpoint_12_36_base endpoint_12_36_p11) (by decide)⟩
private def endpoint_12_37_flag : Flag := ⟨12, 37, 3614⟩
private def endpoint_12_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_37_base : receiptBase endpoint_12_37_flag endpoint_12_37_sources = some 199135891771715829 := by decide +kernel
private theorem endpoint_12_37_w0 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 2 199135891771715829 = some 199135891771715829 := by decide +kernel
private theorem endpoint_12_37_w2 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 2 2 199135891771715829 = some 199135891771715829 := by decide +kernel
private theorem endpoint_12_37_p4 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 4 199135891771715829 = some 199135891771715829 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 2 2 199135891771715829 199135891771715829 199135891771715829 endpoint_12_37_w0 endpoint_12_37_w2
private theorem endpoint_12_37_w4 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 4 2 199135891771715829 = some 199135891771715829 := by decide +kernel
private theorem endpoint_12_37_p6 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 6 199135891771715829 = some 199135891771715829 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 4 2 199135891771715829 199135891771715829 199135891771715829 endpoint_12_37_p4 endpoint_12_37_w4
private theorem endpoint_12_37_w6 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 6 2 199135891771715829 = some 199135891771715829 := by decide +kernel
private theorem endpoint_12_37_p8 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 8 199135891771715829 = some 199135891771715829 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 6 2 199135891771715829 199135891771715829 199135891771715829 endpoint_12_37_p6 endpoint_12_37_w6
private theorem endpoint_12_37_w8 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 8 2 199135891771715829 = some 199135891771715829 := by decide +kernel
private theorem endpoint_12_37_p10 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 10 199135891771715829 = some 199135891771715829 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 8 2 199135891771715829 199135891771715829 199135891771715829 endpoint_12_37_p8 endpoint_12_37_w8
private theorem endpoint_12_37_w10 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 10 1 199135891771715829 = some 199135891771715829 := by decide +kernel
private theorem endpoint_12_37_p11 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 11 199135891771715829 = some 199135891771715829 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 10 1 199135891771715829 199135891771715829 199135891771715829 endpoint_12_37_p10 endpoint_12_37_w10
def endpoint_12_37 : CertifiedEndpoint :=
  ⟨⟨12, 37, 3614⟩, 199135891771715829, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_37_flag endpoint_12_37_sources 11 199135891771715829 199135891771715829 rfl endpoint_12_37_base endpoint_12_37_p11) (by decide)⟩
private def endpoint_12_38_flag : Flag := ⟨12, 38, 3588⟩
private def endpoint_12_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_38_base : receiptBase endpoint_12_38_flag endpoint_12_38_sources = some 202198577798177716 := by decide +kernel
private theorem endpoint_12_38_w0 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 2 202198577798177716 = some 202198577798177716 := by decide +kernel
private theorem endpoint_12_38_w2 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 2 2 202198577798177716 = some 202198577798177716 := by decide +kernel
private theorem endpoint_12_38_p4 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 4 202198577798177716 = some 202198577798177716 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 2 2 202198577798177716 202198577798177716 202198577798177716 endpoint_12_38_w0 endpoint_12_38_w2
private theorem endpoint_12_38_w4 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 4 2 202198577798177716 = some 202198577798177716 := by decide +kernel
private theorem endpoint_12_38_p6 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 6 202198577798177716 = some 202198577798177716 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 4 2 202198577798177716 202198577798177716 202198577798177716 endpoint_12_38_p4 endpoint_12_38_w4
private theorem endpoint_12_38_w6 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 6 2 202198577798177716 = some 202198577798177716 := by decide +kernel
private theorem endpoint_12_38_p8 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 8 202198577798177716 = some 202198577798177716 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 6 2 202198577798177716 202198577798177716 202198577798177716 endpoint_12_38_p6 endpoint_12_38_w6
private theorem endpoint_12_38_w8 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 8 2 202198577798177716 = some 202198577798177716 := by decide +kernel
private theorem endpoint_12_38_p10 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 10 202198577798177716 = some 202198577798177716 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 8 2 202198577798177716 202198577798177716 202198577798177716 endpoint_12_38_p8 endpoint_12_38_w8
private theorem endpoint_12_38_w10 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 10 1 202198577798177716 = some 202198577798177716 := by decide +kernel
private theorem endpoint_12_38_p11 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 11 202198577798177716 = some 202198577798177716 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 10 1 202198577798177716 202198577798177716 202198577798177716 endpoint_12_38_p10 endpoint_12_38_w10
def endpoint_12_38 : CertifiedEndpoint :=
  ⟨⟨12, 38, 3588⟩, 202198577798177716, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_38_flag endpoint_12_38_sources 11 202198577798177716 202198577798177716 rfl endpoint_12_38_base endpoint_12_38_p11) (by decide)⟩
private def endpoint_12_39_flag : Flag := ⟨12, 39, 3562⟩
private def endpoint_12_39_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_39_base : receiptBase endpoint_12_39_flag endpoint_12_39_sources = some 206013010273332062 := by decide +kernel
private theorem endpoint_12_39_w0 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 2 206013010273332062 = some 206013010273332062 := by decide +kernel
private theorem endpoint_12_39_w2 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 2 2 206013010273332062 = some 206013010273332062 := by decide +kernel
private theorem endpoint_12_39_p4 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 4 206013010273332062 = some 206013010273332062 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 2 2 206013010273332062 206013010273332062 206013010273332062 endpoint_12_39_w0 endpoint_12_39_w2
private theorem endpoint_12_39_w4 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 4 2 206013010273332062 = some 206013010273332062 := by decide +kernel
private theorem endpoint_12_39_p6 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 6 206013010273332062 = some 206013010273332062 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 4 2 206013010273332062 206013010273332062 206013010273332062 endpoint_12_39_p4 endpoint_12_39_w4
private theorem endpoint_12_39_w6 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 6 2 206013010273332062 = some 206013010273332062 := by decide +kernel
private theorem endpoint_12_39_p8 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 8 206013010273332062 = some 206013010273332062 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 6 2 206013010273332062 206013010273332062 206013010273332062 endpoint_12_39_p6 endpoint_12_39_w6
private theorem endpoint_12_39_w8 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 8 2 206013010273332062 = some 206013010273332062 := by decide +kernel
private theorem endpoint_12_39_p10 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 10 206013010273332062 = some 206013010273332062 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 8 2 206013010273332062 206013010273332062 206013010273332062 endpoint_12_39_p8 endpoint_12_39_w8
private theorem endpoint_12_39_w10 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 10 1 206013010273332062 = some 206013010273332062 := by decide +kernel
private theorem endpoint_12_39_p11 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 11 206013010273332062 = some 206013010273332062 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 10 1 206013010273332062 206013010273332062 206013010273332062 endpoint_12_39_p10 endpoint_12_39_w10
def endpoint_12_39 : CertifiedEndpoint :=
  ⟨⟨12, 39, 3562⟩, 206013010273332062, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_39_flag endpoint_12_39_sources 11 206013010273332062 206013010273332062 rfl endpoint_12_39_base endpoint_12_39_p11) (by decide)⟩
private def endpoint_12_40_flag : Flag := ⟨12, 40, 3535⟩
private def endpoint_12_40_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_40_base : receiptBase endpoint_12_40_flag endpoint_12_40_sources = some 208854992818049935 := by decide +kernel
private theorem endpoint_12_40_w0 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 2 208854992818049935 = some 208854992818049935 := by decide +kernel
private theorem endpoint_12_40_w2 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 2 2 208854992818049935 = some 208854992818049935 := by decide +kernel
private theorem endpoint_12_40_p4 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 4 208854992818049935 = some 208854992818049935 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 2 2 208854992818049935 208854992818049935 208854992818049935 endpoint_12_40_w0 endpoint_12_40_w2
private theorem endpoint_12_40_w4 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 4 2 208854992818049935 = some 208854992818049935 := by decide +kernel
private theorem endpoint_12_40_p6 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 6 208854992818049935 = some 208854992818049935 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 4 2 208854992818049935 208854992818049935 208854992818049935 endpoint_12_40_p4 endpoint_12_40_w4
private theorem endpoint_12_40_w6 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 6 2 208854992818049935 = some 208854992818049935 := by decide +kernel
private theorem endpoint_12_40_p8 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 8 208854992818049935 = some 208854992818049935 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 6 2 208854992818049935 208854992818049935 208854992818049935 endpoint_12_40_p6 endpoint_12_40_w6
private theorem endpoint_12_40_w8 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 8 2 208854992818049935 = some 208854992818049935 := by decide +kernel
private theorem endpoint_12_40_p10 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 10 208854992818049935 = some 208854992818049935 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 8 2 208854992818049935 208854992818049935 208854992818049935 endpoint_12_40_p8 endpoint_12_40_w8
private theorem endpoint_12_40_w10 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 10 1 208854992818049935 = some 208854992818049935 := by decide +kernel
private theorem endpoint_12_40_p11 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 11 208854992818049935 = some 208854992818049935 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 10 1 208854992818049935 208854992818049935 208854992818049935 endpoint_12_40_p10 endpoint_12_40_w10
def endpoint_12_40 : CertifiedEndpoint :=
  ⟨⟨12, 40, 3535⟩, 208854992818049935, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_40_flag endpoint_12_40_sources 11 208854992818049935 208854992818049935 rfl endpoint_12_40_base endpoint_12_40_p11) (by decide)⟩
private def endpoint_12_41_flag : Flag := ⟨12, 41, 3507⟩
private def endpoint_12_41_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_41_base : receiptBase endpoint_12_41_flag endpoint_12_41_sources = some 211570648532046757 := by decide +kernel
private theorem endpoint_12_41_w0 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 2 211570648532046757 = some 211570648532046757 := by decide +kernel
private theorem endpoint_12_41_w2 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 2 2 211570648532046757 = some 211570648532046757 := by decide +kernel
private theorem endpoint_12_41_p4 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 4 211570648532046757 = some 211570648532046757 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 2 2 211570648532046757 211570648532046757 211570648532046757 endpoint_12_41_w0 endpoint_12_41_w2
private theorem endpoint_12_41_w4 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 4 2 211570648532046757 = some 211570648532046757 := by decide +kernel
private theorem endpoint_12_41_p6 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 6 211570648532046757 = some 211570648532046757 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 4 2 211570648532046757 211570648532046757 211570648532046757 endpoint_12_41_p4 endpoint_12_41_w4
private theorem endpoint_12_41_w6 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 6 2 211570648532046757 = some 211570648532046757 := by decide +kernel
private theorem endpoint_12_41_p8 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 8 211570648532046757 = some 211570648532046757 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 6 2 211570648532046757 211570648532046757 211570648532046757 endpoint_12_41_p6 endpoint_12_41_w6
private theorem endpoint_12_41_w8 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 8 2 211570648532046757 = some 211570648532046757 := by decide +kernel
private theorem endpoint_12_41_p10 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 10 211570648532046757 = some 211570648532046757 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 8 2 211570648532046757 211570648532046757 211570648532046757 endpoint_12_41_p8 endpoint_12_41_w8
private theorem endpoint_12_41_w10 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 10 1 211570648532046757 = some 211570648532046757 := by decide +kernel
private theorem endpoint_12_41_p11 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 11 211570648532046757 = some 211570648532046757 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 10 1 211570648532046757 211570648532046757 211570648532046757 endpoint_12_41_p10 endpoint_12_41_w10
def endpoint_12_41 : CertifiedEndpoint :=
  ⟨⟨12, 41, 3507⟩, 211570648532046757, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_41_flag endpoint_12_41_sources 11 211570648532046757 211570648532046757 rfl endpoint_12_41_base endpoint_12_41_p11) (by decide)⟩
private def endpoint_12_42_flag : Flag := ⟨12, 42, 3479⟩
private def endpoint_12_42_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_42_base : receiptBase endpoint_12_42_flag endpoint_12_42_sources = some 214216954334516471 := by decide +kernel
private theorem endpoint_12_42_w0 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 2 214216954334516471 = some 214216954334516471 := by decide +kernel
private theorem endpoint_12_42_w2 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 2 2 214216954334516471 = some 214216954334516471 := by decide +kernel
private theorem endpoint_12_42_p4 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 4 214216954334516471 = some 214216954334516471 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 2 2 214216954334516471 214216954334516471 214216954334516471 endpoint_12_42_w0 endpoint_12_42_w2
private theorem endpoint_12_42_w4 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 4 2 214216954334516471 = some 214216954334516471 := by decide +kernel
private theorem endpoint_12_42_p6 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 6 214216954334516471 = some 214216954334516471 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 4 2 214216954334516471 214216954334516471 214216954334516471 endpoint_12_42_p4 endpoint_12_42_w4
private theorem endpoint_12_42_w6 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 6 2 214216954334516471 = some 214216954334516471 := by decide +kernel
private theorem endpoint_12_42_p8 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 8 214216954334516471 = some 214216954334516471 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 6 2 214216954334516471 214216954334516471 214216954334516471 endpoint_12_42_p6 endpoint_12_42_w6
private theorem endpoint_12_42_w8 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 8 2 214216954334516471 = some 214216954334516471 := by decide +kernel
private theorem endpoint_12_42_p10 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 10 214216954334516471 = some 214216954334516471 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 8 2 214216954334516471 214216954334516471 214216954334516471 endpoint_12_42_p8 endpoint_12_42_w8
private theorem endpoint_12_42_w10 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 10 1 214216954334516471 = some 214216954334516471 := by decide +kernel
private theorem endpoint_12_42_p11 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 11 214216954334516471 = some 214216954334516471 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 10 1 214216954334516471 214216954334516471 214216954334516471 endpoint_12_42_p10 endpoint_12_42_w10
def endpoint_12_42 : CertifiedEndpoint :=
  ⟨⟨12, 42, 3479⟩, 214216954334516471, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_42_flag endpoint_12_42_sources 11 214216954334516471 214216954334516471 rfl endpoint_12_42_base endpoint_12_42_p11) (by decide)⟩
private def endpoint_12_43_flag : Flag := ⟨12, 43, 3451⟩
private def endpoint_12_43_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_43_base : receiptBase endpoint_12_43_flag endpoint_12_43_sources = some 216793910225459076 := by decide +kernel
private theorem endpoint_12_43_w0 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 2 216793910225459076 = some 216793910225459076 := by decide +kernel
private theorem endpoint_12_43_w2 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 2 2 216793910225459076 = some 216793910225459076 := by decide +kernel
private theorem endpoint_12_43_p4 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 4 216793910225459076 = some 216793910225459076 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 2 2 216793910225459076 216793910225459076 216793910225459076 endpoint_12_43_w0 endpoint_12_43_w2
private theorem endpoint_12_43_w4 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 4 2 216793910225459076 = some 216793910225459076 := by decide +kernel
private theorem endpoint_12_43_p6 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 6 216793910225459076 = some 216793910225459076 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 4 2 216793910225459076 216793910225459076 216793910225459076 endpoint_12_43_p4 endpoint_12_43_w4
private theorem endpoint_12_43_w6 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 6 2 216793910225459076 = some 216793910225459076 := by decide +kernel
private theorem endpoint_12_43_p8 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 8 216793910225459076 = some 216793910225459076 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 6 2 216793910225459076 216793910225459076 216793910225459076 endpoint_12_43_p6 endpoint_12_43_w6
private theorem endpoint_12_43_w8 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 8 2 216793910225459076 = some 216793910225459076 := by decide +kernel
private theorem endpoint_12_43_p10 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 10 216793910225459076 = some 216793910225459076 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 8 2 216793910225459076 216793910225459076 216793910225459076 endpoint_12_43_p8 endpoint_12_43_w8
private theorem endpoint_12_43_w10 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 10 1 216793910225459076 = some 216793910225459076 := by decide +kernel
private theorem endpoint_12_43_p11 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 11 216793910225459076 = some 216793910225459076 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 10 1 216793910225459076 216793910225459076 216793910225459076 endpoint_12_43_p10 endpoint_12_43_w10
def endpoint_12_43 : CertifiedEndpoint :=
  ⟨⟨12, 43, 3451⟩, 216793910225459076, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_43_flag endpoint_12_43_sources 11 216793910225459076 216793910225459076 rfl endpoint_12_43_base endpoint_12_43_p11) (by decide)⟩
private def endpoint_12_44_flag : Flag := ⟨12, 44, 3422⟩
private def endpoint_12_44_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_44_base : receiptBase endpoint_12_44_flag endpoint_12_44_sources = some 219238455960108077 := by decide +kernel
private theorem endpoint_12_44_w0 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 2 219238455960108077 = some 220509349058247868 := by decide +kernel
private theorem endpoint_12_44_w2 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 2 2 220509349058247868 = some 220509349058247868 := by decide +kernel
private theorem endpoint_12_44_p4 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 4 219238455960108077 = some 220509349058247868 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 2 2 219238455960108077 220509349058247868 220509349058247868 endpoint_12_44_w0 endpoint_12_44_w2
private theorem endpoint_12_44_w4 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 4 2 220509349058247868 = some 220509349058247868 := by decide +kernel
private theorem endpoint_12_44_p6 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 6 219238455960108077 = some 220509349058247868 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 4 2 219238455960108077 220509349058247868 220509349058247868 endpoint_12_44_p4 endpoint_12_44_w4
private theorem endpoint_12_44_w6 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 6 2 220509349058247868 = some 220509349058247868 := by decide +kernel
private theorem endpoint_12_44_p8 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 8 219238455960108077 = some 220509349058247868 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 6 2 219238455960108077 220509349058247868 220509349058247868 endpoint_12_44_p6 endpoint_12_44_w6
private theorem endpoint_12_44_w8 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 8 2 220509349058247868 = some 220509349058247868 := by decide +kernel
private theorem endpoint_12_44_p10 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 10 219238455960108077 = some 220509349058247868 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 8 2 219238455960108077 220509349058247868 220509349058247868 endpoint_12_44_p8 endpoint_12_44_w8
private theorem endpoint_12_44_w10 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 10 1 220509349058247868 = some 220509349058247868 := by decide +kernel
private theorem endpoint_12_44_p11 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 11 219238455960108077 = some 220509349058247868 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 10 1 219238455960108077 220509349058247868 220509349058247868 endpoint_12_44_p10 endpoint_12_44_w10
def endpoint_12_44 : CertifiedEndpoint :=
  ⟨⟨12, 44, 3422⟩, 220509349058247868, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_44_flag endpoint_12_44_sources 11 219238455960108077 220509349058247868 rfl endpoint_12_44_base endpoint_12_44_p11) (by decide)⟩
private def endpoint_12_45_flag : Flag := ⟨12, 45, 3392⟩
private def endpoint_12_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_45_base : receiptBase endpoint_12_45_flag endpoint_12_45_sources = some 221546941543119941 := by decide +kernel
private theorem endpoint_12_45_w0 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 2 221546941543119941 = some 225408783741094338 := by decide +kernel
private theorem endpoint_12_45_w2 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 2 2 225408783741094338 = some 225408783741094338 := by decide +kernel
private theorem endpoint_12_45_p4 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 4 221546941543119941 = some 225408783741094338 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 2 2 221546941543119941 225408783741094338 225408783741094338 endpoint_12_45_w0 endpoint_12_45_w2
private theorem endpoint_12_45_w4 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 4 2 225408783741094338 = some 225408783741094338 := by decide +kernel
private theorem endpoint_12_45_p6 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 6 221546941543119941 = some 225408783741094338 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 4 2 221546941543119941 225408783741094338 225408783741094338 endpoint_12_45_p4 endpoint_12_45_w4
private theorem endpoint_12_45_w6 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 6 2 225408783741094338 = some 225408783741094338 := by decide +kernel
private theorem endpoint_12_45_p8 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 8 221546941543119941 = some 225408783741094338 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 6 2 221546941543119941 225408783741094338 225408783741094338 endpoint_12_45_p6 endpoint_12_45_w6
private theorem endpoint_12_45_w8 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 8 2 225408783741094338 = some 225408783741094338 := by decide +kernel
private theorem endpoint_12_45_p10 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 10 221546941543119941 = some 225408783741094338 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 8 2 221546941543119941 225408783741094338 225408783741094338 endpoint_12_45_p8 endpoint_12_45_w8
private theorem endpoint_12_45_w10 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 10 1 225408783741094338 = some 225408783741094338 := by decide +kernel
private theorem endpoint_12_45_p11 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 11 221546941543119941 = some 225408783741094338 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 10 1 221546941543119941 225408783741094338 225408783741094338 endpoint_12_45_p10 endpoint_12_45_w10
def endpoint_12_45 : CertifiedEndpoint :=
  ⟨⟨12, 45, 3392⟩, 225408783741094338, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_45_flag endpoint_12_45_sources 11 221546941543119941 225408783741094338 rfl endpoint_12_45_base endpoint_12_45_p11) (by decide)⟩
private def endpoint_12_46_flag : Flag := ⟨12, 46, 3362⟩
private def endpoint_12_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_46_base : receiptBase endpoint_12_46_flag endpoint_12_46_sources = some 223781210554146654 := by decide +kernel
private theorem endpoint_12_46_w0 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 2 223781210554146654 = some 230252416792065426 := by decide +kernel
private theorem endpoint_12_46_w2 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 2 2 230252416792065426 = some 230252416792065426 := by decide +kernel
private theorem endpoint_12_46_p4 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 4 223781210554146654 = some 230252416792065426 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 2 2 223781210554146654 230252416792065426 230252416792065426 endpoint_12_46_w0 endpoint_12_46_w2
private theorem endpoint_12_46_w4 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 4 2 230252416792065426 = some 230252416792065426 := by decide +kernel
private theorem endpoint_12_46_p6 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 6 223781210554146654 = some 230252416792065426 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 4 2 223781210554146654 230252416792065426 230252416792065426 endpoint_12_46_p4 endpoint_12_46_w4
private theorem endpoint_12_46_w6 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 6 2 230252416792065426 = some 230252416792065426 := by decide +kernel
private theorem endpoint_12_46_p8 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 8 223781210554146654 = some 230252416792065426 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 6 2 223781210554146654 230252416792065426 230252416792065426 endpoint_12_46_p6 endpoint_12_46_w6
private theorem endpoint_12_46_w8 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 8 2 230252416792065426 = some 230252416792065426 := by decide +kernel
private theorem endpoint_12_46_p10 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 10 223781210554146654 = some 230252416792065426 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 8 2 223781210554146654 230252416792065426 230252416792065426 endpoint_12_46_p8 endpoint_12_46_w8
private theorem endpoint_12_46_w10 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 10 1 230252416792065426 = some 230252416792065426 := by decide +kernel
private theorem endpoint_12_46_p11 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 11 223781210554146654 = some 230252416792065426 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 10 1 223781210554146654 230252416792065426 230252416792065426 endpoint_12_46_p10 endpoint_12_46_w10
def endpoint_12_46 : CertifiedEndpoint :=
  ⟨⟨12, 46, 3362⟩, 230252416792065426, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_46_flag endpoint_12_46_sources 11 223781210554146654 230252416792065426 rfl endpoint_12_46_base endpoint_12_46_p11) (by decide)⟩
private def endpoint_12_47_flag : Flag := ⟨12, 47, 3331⟩
private def endpoint_12_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_47_base : receiptBase endpoint_12_47_flag endpoint_12_47_sources = some 225874552753078187 := by decide +kernel
private theorem endpoint_12_47_w0 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 2 225874552753078187 = some 235005054340213423 := by decide +kernel
private theorem endpoint_12_47_w2 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 2 2 235005054340213423 = some 235005054340213423 := by decide +kernel
private theorem endpoint_12_47_p4 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 4 225874552753078187 = some 235005054340213423 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 2 2 225874552753078187 235005054340213423 235005054340213423 endpoint_12_47_w0 endpoint_12_47_w2
private theorem endpoint_12_47_w4 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 4 2 235005054340213423 = some 235005054340213423 := by decide +kernel
private theorem endpoint_12_47_p6 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 6 225874552753078187 = some 235005054340213423 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 4 2 225874552753078187 235005054340213423 235005054340213423 endpoint_12_47_p4 endpoint_12_47_w4
private theorem endpoint_12_47_w6 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 6 2 235005054340213423 = some 235005054340213423 := by decide +kernel
private theorem endpoint_12_47_p8 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 8 225874552753078187 = some 235005054340213423 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 6 2 225874552753078187 235005054340213423 235005054340213423 endpoint_12_47_p6 endpoint_12_47_w6
private theorem endpoint_12_47_w8 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 8 2 235005054340213423 = some 235005054340213423 := by decide +kernel
private theorem endpoint_12_47_p10 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 10 225874552753078187 = some 235005054340213423 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 8 2 225874552753078187 235005054340213423 235005054340213423 endpoint_12_47_p8 endpoint_12_47_w8
private theorem endpoint_12_47_w10 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 10 1 235005054340213423 = some 235005054340213423 := by decide +kernel
private theorem endpoint_12_47_p11 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 11 225874552753078187 = some 235005054340213423 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 10 1 225874552753078187 235005054340213423 235005054340213423 endpoint_12_47_p10 endpoint_12_47_w10
def endpoint_12_47 : CertifiedEndpoint :=
  ⟨⟨12, 47, 3331⟩, 235005054340213423, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_47_flag endpoint_12_47_sources 11 225874552753078187 235005054340213423 rfl endpoint_12_47_base endpoint_12_47_p11) (by decide)⟩
private def endpoint_12_48_flag : Flag := ⟨12, 48, 3300⟩
private def endpoint_12_48_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_48_base : receiptBase endpoint_12_48_flag endpoint_12_48_sources = some 228418073575782615 := by decide +kernel
private theorem endpoint_12_48_w0 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 2 228418073575782615 = some 231690870593300136 := by decide +kernel
private theorem endpoint_12_48_w2 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 2 2 231690870593300136 = some 231690870593300136 := by decide +kernel
private theorem endpoint_12_48_p4 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 4 228418073575782615 = some 231690870593300136 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 2 2 228418073575782615 231690870593300136 231690870593300136 endpoint_12_48_w0 endpoint_12_48_w2
private theorem endpoint_12_48_w4 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 4 2 231690870593300136 = some 231690870593300136 := by decide +kernel
private theorem endpoint_12_48_p6 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 6 228418073575782615 = some 231690870593300136 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 4 2 228418073575782615 231690870593300136 231690870593300136 endpoint_12_48_p4 endpoint_12_48_w4
private theorem endpoint_12_48_w6 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 6 2 231690870593300136 = some 231690870593300136 := by decide +kernel
private theorem endpoint_12_48_p8 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 8 228418073575782615 = some 231690870593300136 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 6 2 228418073575782615 231690870593300136 231690870593300136 endpoint_12_48_p6 endpoint_12_48_w6
private theorem endpoint_12_48_w8 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 8 2 231690870593300136 = some 231690870593300136 := by decide +kernel
private theorem endpoint_12_48_p10 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 10 228418073575782615 = some 231690870593300136 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 8 2 228418073575782615 231690870593300136 231690870593300136 endpoint_12_48_p8 endpoint_12_48_w8
private theorem endpoint_12_48_w10 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 10 1 231690870593300136 = some 231690870593300136 := by decide +kernel
private theorem endpoint_12_48_p11 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 11 228418073575782615 = some 231690870593300136 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 10 1 228418073575782615 231690870593300136 231690870593300136 endpoint_12_48_p10 endpoint_12_48_w10
def endpoint_12_48 : CertifiedEndpoint :=
  ⟨⟨12, 48, 3300⟩, 231690870593300136, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_48_flag endpoint_12_48_sources 11 228418073575782615 231690870593300136 rfl endpoint_12_48_base endpoint_12_48_p11) (by decide)⟩
private def endpoint_12_49_flag : Flag := ⟨12, 49, 3267⟩
private def endpoint_12_49_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_49_base : receiptBase endpoint_12_49_flag endpoint_12_49_sources = some 230228801658421122 := by decide +kernel
private theorem endpoint_12_49_w0 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 2 230228801658421122 = some 236060490478582681 := by decide +kernel
private theorem endpoint_12_49_w2 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 2 2 236060490478582681 = some 236060490478582681 := by decide +kernel
private theorem endpoint_12_49_p4 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 4 230228801658421122 = some 236060490478582681 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 2 2 230228801658421122 236060490478582681 236060490478582681 endpoint_12_49_w0 endpoint_12_49_w2
private theorem endpoint_12_49_w4 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 4 2 236060490478582681 = some 236060490478582681 := by decide +kernel
private theorem endpoint_12_49_p6 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 6 230228801658421122 = some 236060490478582681 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 4 2 230228801658421122 236060490478582681 236060490478582681 endpoint_12_49_p4 endpoint_12_49_w4
private theorem endpoint_12_49_w6 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 6 2 236060490478582681 = some 236060490478582681 := by decide +kernel
private theorem endpoint_12_49_p8 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 8 230228801658421122 = some 236060490478582681 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 6 2 230228801658421122 236060490478582681 236060490478582681 endpoint_12_49_p6 endpoint_12_49_w6
private theorem endpoint_12_49_w8 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 8 2 236060490478582681 = some 236060490478582681 := by decide +kernel
private theorem endpoint_12_49_p10 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 10 230228801658421122 = some 236060490478582681 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 8 2 230228801658421122 236060490478582681 236060490478582681 endpoint_12_49_p8 endpoint_12_49_w8
private theorem endpoint_12_49_w10 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 10 1 236060490478582681 = some 236060490478582681 := by decide +kernel
private theorem endpoint_12_49_p11 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 11 230228801658421122 = some 236060490478582681 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 10 1 230228801658421122 236060490478582681 236060490478582681 endpoint_12_49_p10 endpoint_12_49_w10
def endpoint_12_49 : CertifiedEndpoint :=
  ⟨⟨12, 49, 3267⟩, 236060490478582681, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_49_flag endpoint_12_49_sources 11 230228801658421122 236060490478582681 rfl endpoint_12_49_base endpoint_12_49_p11) (by decide)⟩
private def endpoint_12_50_flag : Flag := ⟨12, 50, 3234⟩
private def endpoint_12_50_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_50_base : receiptBase endpoint_12_50_flag endpoint_12_50_sources = some 231957707154360220 := by decide +kernel
private theorem endpoint_12_50_w0 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 2 231957707154360220 = some 240369000017538090 := by decide +kernel
private theorem endpoint_12_50_w2 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 2 2 240369000017538090 = some 240369000017538090 := by decide +kernel
private theorem endpoint_12_50_p4 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 4 231957707154360220 = some 240369000017538090 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 2 2 231957707154360220 240369000017538090 240369000017538090 endpoint_12_50_w0 endpoint_12_50_w2
private theorem endpoint_12_50_w4 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 4 2 240369000017538090 = some 240369000017538090 := by decide +kernel
private theorem endpoint_12_50_p6 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 6 231957707154360220 = some 240369000017538090 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 4 2 231957707154360220 240369000017538090 240369000017538090 endpoint_12_50_p4 endpoint_12_50_w4
private theorem endpoint_12_50_w6 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 6 2 240369000017538090 = some 240369000017538090 := by decide +kernel
private theorem endpoint_12_50_p8 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 8 231957707154360220 = some 240369000017538090 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 6 2 231957707154360220 240369000017538090 240369000017538090 endpoint_12_50_p6 endpoint_12_50_w6
private theorem endpoint_12_50_w8 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 8 2 240369000017538090 = some 240369000017538090 := by decide +kernel
private theorem endpoint_12_50_p10 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 10 231957707154360220 = some 240369000017538090 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 8 2 231957707154360220 240369000017538090 240369000017538090 endpoint_12_50_p8 endpoint_12_50_w8
private theorem endpoint_12_50_w10 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 10 1 240369000017538090 = some 240369000017538090 := by decide +kernel
private theorem endpoint_12_50_p11 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 11 231957707154360220 = some 240369000017538090 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 10 1 231957707154360220 240369000017538090 240369000017538090 endpoint_12_50_p10 endpoint_12_50_w10
def endpoint_12_50 : CertifiedEndpoint :=
  ⟨⟨12, 50, 3234⟩, 240369000017538090, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_50_flag endpoint_12_50_sources 11 231957707154360220 240369000017538090 rfl endpoint_12_50_base endpoint_12_50_p11) (by decide)⟩
private def endpoint_12_51_flag : Flag := ⟨12, 51, 3201⟩
private def endpoint_12_51_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_51_base : receiptBase endpoint_12_51_flag endpoint_12_51_sources = some 233604790063599911 := by decide +kernel
private theorem endpoint_12_51_w0 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 2 233604790063599911 = some 244616399210166363 := by decide +kernel
private theorem endpoint_12_51_w2 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 2 2 244616399210166363 = some 244616399210166363 := by decide +kernel
private theorem endpoint_12_51_p4 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 4 233604790063599911 = some 244616399210166363 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 2 2 233604790063599911 244616399210166363 244616399210166363 endpoint_12_51_w0 endpoint_12_51_w2
private theorem endpoint_12_51_w4 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 4 2 244616399210166363 = some 244616399210166363 := by decide +kernel
private theorem endpoint_12_51_p6 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 6 233604790063599911 = some 244616399210166363 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 4 2 233604790063599911 244616399210166363 244616399210166363 endpoint_12_51_p4 endpoint_12_51_w4
private theorem endpoint_12_51_w6 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 6 2 244616399210166363 = some 244616399210166363 := by decide +kernel
private theorem endpoint_12_51_p8 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 8 233604790063599911 = some 244616399210166363 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 6 2 233604790063599911 244616399210166363 244616399210166363 endpoint_12_51_p6 endpoint_12_51_w6
private theorem endpoint_12_51_w8 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 8 2 244616399210166363 = some 244616399210166363 := by decide +kernel
private theorem endpoint_12_51_p10 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 10 233604790063599911 = some 244616399210166363 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 8 2 233604790063599911 244616399210166363 244616399210166363 endpoint_12_51_p8 endpoint_12_51_w8
private theorem endpoint_12_51_w10 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 10 1 244616399210166363 = some 244616399210166363 := by decide +kernel
private theorem endpoint_12_51_p11 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 11 233604790063599911 = some 244616399210166363 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 10 1 233604790063599911 244616399210166363 244616399210166363 endpoint_12_51_p10 endpoint_12_51_w10
def endpoint_12_51 : CertifiedEndpoint :=
  ⟨⟨12, 51, 3201⟩, 244616399210166363, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_51_flag endpoint_12_51_sources 11 233604790063599911 244616399210166363 rfl endpoint_12_51_base endpoint_12_51_p11) (by decide)⟩
private def endpoint_12_52_flag : Flag := ⟨12, 52, 3166⟩
private def endpoint_12_52_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_12_52_base : receiptBase endpoint_12_52_flag endpoint_12_52_sources = some 235893935875500273 := by decide +kernel
private theorem endpoint_12_52_w0 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 2 235893935875500273 = some 244745319516698284 := by decide +kernel
private theorem endpoint_12_52_w2 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 2 2 244745319516698284 = some 244745319516698284 := by decide +kernel
private theorem endpoint_12_52_p4 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 4 235893935875500273 = some 244745319516698284 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 2 2 235893935875500273 244745319516698284 244745319516698284 endpoint_12_52_w0 endpoint_12_52_w2
private theorem endpoint_12_52_w4 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 4 2 244745319516698284 = some 244745319516698284 := by decide +kernel
private theorem endpoint_12_52_p6 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 6 235893935875500273 = some 244745319516698284 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 4 2 235893935875500273 244745319516698284 244745319516698284 endpoint_12_52_p4 endpoint_12_52_w4
private theorem endpoint_12_52_w6 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 6 2 244745319516698284 = some 244745319516698284 := by decide +kernel
private theorem endpoint_12_52_p8 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 8 235893935875500273 = some 244745319516698284 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 6 2 235893935875500273 244745319516698284 244745319516698284 endpoint_12_52_p6 endpoint_12_52_w6
private theorem endpoint_12_52_w8 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 8 2 244745319516698284 = some 244745319516698284 := by decide +kernel
private theorem endpoint_12_52_p10 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 10 235893935875500273 = some 244745319516698284 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 8 2 235893935875500273 244745319516698284 244745319516698284 endpoint_12_52_p8 endpoint_12_52_w8
private theorem endpoint_12_52_w10 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 10 1 244745319516698284 = some 244745319516698284 := by decide +kernel
private theorem endpoint_12_52_p11 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 11 235893935875500273 = some 244745319516698284 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 10 1 235893935875500273 244745319516698284 244745319516698284 endpoint_12_52_p10 endpoint_12_52_w10
def endpoint_12_52 : CertifiedEndpoint :=
  ⟨⟨12, 52, 3166⟩, 244745319516698284, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_12_52_flag endpoint_12_52_sources 11 235893935875500273 244745319516698284 rfl endpoint_12_52_base endpoint_12_52_p11) (by decide)⟩
private def endpoint_12_53_flag : Flag := ⟨12, 53, 3130⟩
private def endpoint_12_53_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_53_base : receiptBase endpoint_12_53_flag endpoint_12_53_sources = some 238880332699211607 := by decide +kernel
private theorem endpoint_12_53_w0 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 2 238880332699211607 = some 241628674901107237 := by decide +kernel
private theorem endpoint_12_53_w2 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 2 2 241628674901107237 = some 241628674901107237 := by decide +kernel
private theorem endpoint_12_53_p4 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 4 238880332699211607 = some 241628674901107237 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 2 2 238880332699211607 241628674901107237 241628674901107237 endpoint_12_53_w0 endpoint_12_53_w2
private theorem endpoint_12_53_w4 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 4 2 241628674901107237 = some 241628674901107237 := by decide +kernel
private theorem endpoint_12_53_p6 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 6 238880332699211607 = some 241628674901107237 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 4 2 238880332699211607 241628674901107237 241628674901107237 endpoint_12_53_p4 endpoint_12_53_w4
private theorem endpoint_12_53_w6 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 6 2 241628674901107237 = some 241628674901107237 := by decide +kernel
private theorem endpoint_12_53_p8 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 8 238880332699211607 = some 241628674901107237 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 6 2 238880332699211607 241628674901107237 241628674901107237 endpoint_12_53_p6 endpoint_12_53_w6
private theorem endpoint_12_53_w8 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 8 2 241628674901107237 = some 241628674901107237 := by decide +kernel
private theorem endpoint_12_53_p10 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 10 238880332699211607 = some 241628674901107237 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 8 2 238880332699211607 241628674901107237 241628674901107237 endpoint_12_53_p8 endpoint_12_53_w8
private theorem endpoint_12_53_w10 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 10 1 241628674901107237 = some 241628674901107237 := by decide +kernel
private theorem endpoint_12_53_p11 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 11 238880332699211607 = some 241628674901107237 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 10 1 238880332699211607 241628674901107237 241628674901107237 endpoint_12_53_p10 endpoint_12_53_w10
def endpoint_12_53 : CertifiedEndpoint :=
  ⟨⟨12, 53, 3130⟩, 241628674901107237, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_53_flag endpoint_12_53_sources 11 238880332699211607 241628674901107237 rfl endpoint_12_53_base endpoint_12_53_p11) (by decide)⟩
private def endpoint_12_54_flag : Flag := ⟨12, 54, 3094⟩
private def endpoint_12_54_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_54_base : receiptBase endpoint_12_54_flag endpoint_12_54_sources = some 240008748803386282 := by decide +kernel
private theorem endpoint_12_54_w0 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 2 240008748803386282 = some 245324466100939368 := by decide +kernel
private theorem endpoint_12_54_w2 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 2 2 245324466100939368 = some 245324466100939368 := by decide +kernel
private theorem endpoint_12_54_p4 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 4 240008748803386282 = some 245324466100939368 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 2 2 240008748803386282 245324466100939368 245324466100939368 endpoint_12_54_w0 endpoint_12_54_w2
private theorem endpoint_12_54_w4 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 4 2 245324466100939368 = some 245324466100939368 := by decide +kernel
private theorem endpoint_12_54_p6 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 6 240008748803386282 = some 245324466100939368 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 4 2 240008748803386282 245324466100939368 245324466100939368 endpoint_12_54_p4 endpoint_12_54_w4
private theorem endpoint_12_54_w6 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 6 2 245324466100939368 = some 245324466100939368 := by decide +kernel
private theorem endpoint_12_54_p8 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 8 240008748803386282 = some 245324466100939368 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 6 2 240008748803386282 245324466100939368 245324466100939368 endpoint_12_54_p6 endpoint_12_54_w6
private theorem endpoint_12_54_w8 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 8 2 245324466100939368 = some 245324466100939368 := by decide +kernel
private theorem endpoint_12_54_p10 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 10 240008748803386282 = some 245324466100939368 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 8 2 240008748803386282 245324466100939368 245324466100939368 endpoint_12_54_p8 endpoint_12_54_w8
private theorem endpoint_12_54_w10 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 10 1 245324466100939368 = some 245324466100939368 := by decide +kernel
private theorem endpoint_12_54_p11 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 11 240008748803386282 = some 245324466100939368 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 10 1 240008748803386282 245324466100939368 245324466100939368 endpoint_12_54_p10 endpoint_12_54_w10
def endpoint_12_54 : CertifiedEndpoint :=
  ⟨⟨12, 54, 3094⟩, 245324466100939368, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_54_flag endpoint_12_54_sources 11 240008748803386282 245324466100939368 rfl endpoint_12_54_base endpoint_12_54_p11) (by decide)⟩
private def endpoint_12_55_flag : Flag := ⟨12, 55, 3056⟩
private def endpoint_12_55_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_55_base : receiptBase endpoint_12_55_flag endpoint_12_55_sources = some 240892248456346437 := by decide +kernel
private theorem endpoint_12_55_w0 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 2 240892248456346437 = some 248869293926225847 := by decide +kernel
private theorem endpoint_12_55_w2 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 2 2 248869293926225847 = some 248869293926225847 := by decide +kernel
private theorem endpoint_12_55_p4 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 4 240892248456346437 = some 248869293926225847 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 2 2 240892248456346437 248869293926225847 248869293926225847 endpoint_12_55_w0 endpoint_12_55_w2
private theorem endpoint_12_55_w4 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 4 2 248869293926225847 = some 248869293926225847 := by decide +kernel
private theorem endpoint_12_55_p6 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 6 240892248456346437 = some 248869293926225847 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 4 2 240892248456346437 248869293926225847 248869293926225847 endpoint_12_55_p4 endpoint_12_55_w4
private theorem endpoint_12_55_w6 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 6 2 248869293926225847 = some 248869293926225847 := by decide +kernel
private theorem endpoint_12_55_p8 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 8 240892248456346437 = some 248869293926225847 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 6 2 240892248456346437 248869293926225847 248869293926225847 endpoint_12_55_p6 endpoint_12_55_w6
private theorem endpoint_12_55_w8 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 8 2 248869293926225847 = some 248869293926225847 := by decide +kernel
private theorem endpoint_12_55_p10 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 10 240892248456346437 = some 248869293926225847 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 8 2 240892248456346437 248869293926225847 248869293926225847 endpoint_12_55_p8 endpoint_12_55_w8
private theorem endpoint_12_55_w10 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 10 1 248869293926225847 = some 248869293926225847 := by decide +kernel
private theorem endpoint_12_55_p11 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 11 240892248456346437 = some 248869293926225847 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 10 1 240892248456346437 248869293926225847 248869293926225847 endpoint_12_55_p10 endpoint_12_55_w10
def endpoint_12_55 : CertifiedEndpoint :=
  ⟨⟨12, 55, 3056⟩, 248869293926225847, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_55_flag endpoint_12_55_sources 11 240892248456346437 248869293926225847 rfl endpoint_12_55_base endpoint_12_55_p11) (by decide)⟩
private def endpoint_12_56_flag : Flag := ⟨12, 56, 3017⟩
private def endpoint_12_56_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_56_base : receiptBase endpoint_12_56_flag endpoint_12_56_sources = some 241602424971825601 := by decide +kernel
private theorem endpoint_12_56_w0 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 2 241602424971825601 = some 252301006605140260 := by decide +kernel
private theorem endpoint_12_56_w2 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 2 2 252301006605140260 = some 252301006605140260 := by decide +kernel
private theorem endpoint_12_56_p4 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 4 241602424971825601 = some 252301006605140260 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 2 2 241602424971825601 252301006605140260 252301006605140260 endpoint_12_56_w0 endpoint_12_56_w2
private theorem endpoint_12_56_w4 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 4 2 252301006605140260 = some 252301006605140260 := by decide +kernel
private theorem endpoint_12_56_p6 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 6 241602424971825601 = some 252301006605140260 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 4 2 241602424971825601 252301006605140260 252301006605140260 endpoint_12_56_p4 endpoint_12_56_w4
private theorem endpoint_12_56_w6 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 6 2 252301006605140260 = some 252301006605140260 := by decide +kernel
private theorem endpoint_12_56_p8 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 8 241602424971825601 = some 252301006605140260 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 6 2 241602424971825601 252301006605140260 252301006605140260 endpoint_12_56_p6 endpoint_12_56_w6
private theorem endpoint_12_56_w8 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 8 2 252301006605140260 = some 252301006605140260 := by decide +kernel
private theorem endpoint_12_56_p10 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 10 241602424971825601 = some 252301006605140260 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 8 2 241602424971825601 252301006605140260 252301006605140260 endpoint_12_56_p8 endpoint_12_56_w8
private theorem endpoint_12_56_w10 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 10 1 252301006605140260 = some 252301006605140260 := by decide +kernel
private theorem endpoint_12_56_p11 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 11 241602424971825601 = some 252301006605140260 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 10 1 241602424971825601 252301006605140260 252301006605140260 endpoint_12_56_p10 endpoint_12_56_w10
def endpoint_12_56 : CertifiedEndpoint :=
  ⟨⟨12, 56, 3017⟩, 252301006605140260, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_56_flag endpoint_12_56_sources 11 241602424971825601 252301006605140260 rfl endpoint_12_56_base endpoint_12_56_p11) (by decide)⟩
private def endpoint_12_57_flag : Flag := ⟨12, 57, 2977⟩
private def endpoint_12_57_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_12_57_base : receiptBase endpoint_12_57_flag endpoint_12_57_sources = some 243121612680545253 := by decide +kernel
private theorem endpoint_12_57_w0 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 2 243121612680545253 = some 248070795011335428 := by decide +kernel
private theorem endpoint_12_57_w2 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 2 2 248070795011335428 = some 248070795011335428 := by decide +kernel
private theorem endpoint_12_57_p4 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 4 243121612680545253 = some 248070795011335428 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 2 2 243121612680545253 248070795011335428 248070795011335428 endpoint_12_57_w0 endpoint_12_57_w2
private theorem endpoint_12_57_w4 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 4 2 248070795011335428 = some 248070795011335428 := by decide +kernel
private theorem endpoint_12_57_p6 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 6 243121612680545253 = some 248070795011335428 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 4 2 243121612680545253 248070795011335428 248070795011335428 endpoint_12_57_p4 endpoint_12_57_w4
private theorem endpoint_12_57_w6 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 6 2 248070795011335428 = some 248070795011335428 := by decide +kernel
private theorem endpoint_12_57_p8 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 8 243121612680545253 = some 248070795011335428 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 6 2 243121612680545253 248070795011335428 248070795011335428 endpoint_12_57_p6 endpoint_12_57_w6
private theorem endpoint_12_57_w8 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 8 2 248070795011335428 = some 248070795011335428 := by decide +kernel
private theorem endpoint_12_57_p10 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 10 243121612680545253 = some 248070795011335428 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 8 2 243121612680545253 248070795011335428 248070795011335428 endpoint_12_57_p8 endpoint_12_57_w8
private theorem endpoint_12_57_w10 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 10 1 248070795011335428 = some 248070795011335428 := by decide +kernel
private theorem endpoint_12_57_p11 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 11 243121612680545253 = some 248070795011335428 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 10 1 243121612680545253 248070795011335428 248070795011335428 endpoint_12_57_p10 endpoint_12_57_w10
def endpoint_12_57 : CertifiedEndpoint :=
  ⟨⟨12, 57, 2977⟩, 248070795011335428, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_12_57_flag endpoint_12_57_sources 11 243121612680545253 248070795011335428 rfl endpoint_12_57_base endpoint_12_57_p11) (by decide)⟩
private def endpoint_12_58_flag : Flag := ⟨12, 58, 2936⟩
private def endpoint_12_58_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_12_58_base : receiptBase endpoint_12_58_flag endpoint_12_58_sources = some 243479119352779815 := by decide +kernel
private theorem endpoint_12_58_w0 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 2 243479119352779815 = some 251118278793325672 := by decide +kernel
private theorem endpoint_12_58_w2 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 2 2 251118278793325672 = some 251118278793325672 := by decide +kernel
private theorem endpoint_12_58_p4 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 4 243479119352779815 = some 251118278793325672 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 2 2 243479119352779815 251118278793325672 251118278793325672 endpoint_12_58_w0 endpoint_12_58_w2
private theorem endpoint_12_58_w4 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 4 2 251118278793325672 = some 251118278793325672 := by decide +kernel
private theorem endpoint_12_58_p6 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 6 243479119352779815 = some 251118278793325672 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 4 2 243479119352779815 251118278793325672 251118278793325672 endpoint_12_58_p4 endpoint_12_58_w4
private theorem endpoint_12_58_w6 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 6 2 251118278793325672 = some 251118278793325672 := by decide +kernel
private theorem endpoint_12_58_p8 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 8 243479119352779815 = some 251118278793325672 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 6 2 243479119352779815 251118278793325672 251118278793325672 endpoint_12_58_p6 endpoint_12_58_w6
private theorem endpoint_12_58_w8 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 8 2 251118278793325672 = some 251118278793325672 := by decide +kernel
private theorem endpoint_12_58_p10 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 10 243479119352779815 = some 251118278793325672 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 8 2 243479119352779815 251118278793325672 251118278793325672 endpoint_12_58_p8 endpoint_12_58_w8
private theorem endpoint_12_58_w10 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 10 1 251118278793325672 = some 251118278793325672 := by decide +kernel
private theorem endpoint_12_58_p11 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 11 243479119352779815 = some 251118278793325672 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 10 1 243479119352779815 251118278793325672 251118278793325672 endpoint_12_58_p10 endpoint_12_58_w10
def endpoint_12_58 : CertifiedEndpoint :=
  ⟨⟨12, 58, 2936⟩, 251118278793325672, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_12_58_flag endpoint_12_58_sources 11 243479119352779815 251118278793325672 rfl endpoint_12_58_base endpoint_12_58_p11) (by decide)⟩
private def endpoint_12_59_flag : Flag := ⟨12, 59, 2892⟩
private def endpoint_12_59_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_12_59_base : receiptBase endpoint_12_59_flag endpoint_12_59_sources = some 243485017079602795 := by decide +kernel
private theorem endpoint_12_59_w0 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 2 243485017079602795 = some 253953061757563785 := by decide +kernel
private theorem endpoint_12_59_w2 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 2 2 253953061757563785 = some 253953061757563785 := by decide +kernel
private theorem endpoint_12_59_p4 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 4 243485017079602795 = some 253953061757563785 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 2 2 243485017079602795 253953061757563785 253953061757563785 endpoint_12_59_w0 endpoint_12_59_w2
private theorem endpoint_12_59_w4 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 4 2 253953061757563785 = some 253953061757563785 := by decide +kernel
private theorem endpoint_12_59_p6 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 6 243485017079602795 = some 253953061757563785 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 4 2 243485017079602795 253953061757563785 253953061757563785 endpoint_12_59_p4 endpoint_12_59_w4
private theorem endpoint_12_59_w6 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 6 2 253953061757563785 = some 253953061757563785 := by decide +kernel
private theorem endpoint_12_59_p8 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 8 243485017079602795 = some 253953061757563785 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 6 2 243485017079602795 253953061757563785 253953061757563785 endpoint_12_59_p6 endpoint_12_59_w6
private theorem endpoint_12_59_w8 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 8 2 253953061757563785 = some 253953061757563785 := by decide +kernel
private theorem endpoint_12_59_p10 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 10 243485017079602795 = some 253953061757563785 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 8 2 243485017079602795 253953061757563785 253953061757563785 endpoint_12_59_p8 endpoint_12_59_w8
private theorem endpoint_12_59_w10 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 10 1 253953061757563785 = some 253953061757563785 := by decide +kernel
private theorem endpoint_12_59_p11 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 11 243485017079602795 = some 253953061757563785 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 10 1 243485017079602795 253953061757563785 253953061757563785 endpoint_12_59_p10 endpoint_12_59_w10
def endpoint_12_59 : CertifiedEndpoint :=
  ⟨⟨12, 59, 2892⟩, 253953061757563785, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_12_59_flag endpoint_12_59_sources 11 243485017079602795 253953061757563785 rfl endpoint_12_59_base endpoint_12_59_p11) (by decide)⟩
private def endpoint_12_60_flag : Flag := ⟨12, 60, 2848⟩
private def endpoint_12_60_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_12_60_base : receiptBase endpoint_12_60_flag endpoint_12_60_sources = some 244435978826844921 := by decide +kernel
private theorem endpoint_12_60_w0 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 2 244435978826844921 = some 250953861520479924 := by decide +kernel
private theorem endpoint_12_60_w2 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 2 2 250953861520479924 = some 250953861520479924 := by decide +kernel
private theorem endpoint_12_60_p4 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 4 244435978826844921 = some 250953861520479924 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 2 2 244435978826844921 250953861520479924 250953861520479924 endpoint_12_60_w0 endpoint_12_60_w2
private theorem endpoint_12_60_w4 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 4 2 250953861520479924 = some 250953861520479924 := by decide +kernel
private theorem endpoint_12_60_p6 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 6 244435978826844921 = some 250953861520479924 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 4 2 244435978826844921 250953861520479924 250953861520479924 endpoint_12_60_p4 endpoint_12_60_w4
private theorem endpoint_12_60_w6 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 6 2 250953861520479924 = some 250953861520479924 := by decide +kernel
private theorem endpoint_12_60_p8 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 8 244435978826844921 = some 250953861520479924 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 6 2 244435978826844921 250953861520479924 250953861520479924 endpoint_12_60_p6 endpoint_12_60_w6
private theorem endpoint_12_60_w8 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 8 2 250953861520479924 = some 250953861520479924 := by decide +kernel
private theorem endpoint_12_60_p10 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 10 244435978826844921 = some 250953861520479924 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 8 2 244435978826844921 250953861520479924 250953861520479924 endpoint_12_60_p8 endpoint_12_60_w8
private theorem endpoint_12_60_w10 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 10 1 250953861520479924 = some 250953861520479924 := by decide +kernel
private theorem endpoint_12_60_p11 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 11 244435978826844921 = some 250953861520479924 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 10 1 244435978826844921 250953861520479924 250953861520479924 endpoint_12_60_p10 endpoint_12_60_w10
def endpoint_12_60 : CertifiedEndpoint :=
  ⟨⟨12, 60, 2848⟩, 250953861520479924, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_12_60_flag endpoint_12_60_sources 11 244435978826844921 250953861520479924 rfl endpoint_12_60_base endpoint_12_60_p11) (by decide)⟩
private def endpoint_12_61_flag : Flag := ⟨12, 61, 2801⟩
private def endpoint_12_61_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_12_61_base : receiptBase endpoint_12_61_flag endpoint_12_61_sources = some 243966894724512178 := by decide +kernel
private theorem endpoint_12_61_w0 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 2 243966894724512178 = some 253376798210075067 := by decide +kernel
private theorem endpoint_12_61_w2 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 2 2 253376798210075067 = some 253376798210075067 := by decide +kernel
private theorem endpoint_12_61_p4 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 4 243966894724512178 = some 253376798210075067 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 2 2 243966894724512178 253376798210075067 253376798210075067 endpoint_12_61_w0 endpoint_12_61_w2
private theorem endpoint_12_61_w4 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 4 2 253376798210075067 = some 253376798210075067 := by decide +kernel
private theorem endpoint_12_61_p6 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 6 243966894724512178 = some 253376798210075067 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 4 2 243966894724512178 253376798210075067 253376798210075067 endpoint_12_61_p4 endpoint_12_61_w4
private theorem endpoint_12_61_w6 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 6 2 253376798210075067 = some 253376798210075067 := by decide +kernel
private theorem endpoint_12_61_p8 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 8 243966894724512178 = some 253376798210075067 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 6 2 243966894724512178 253376798210075067 253376798210075067 endpoint_12_61_p6 endpoint_12_61_w6
private theorem endpoint_12_61_w8 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 8 2 253376798210075067 = some 253376798210075067 := by decide +kernel
private theorem endpoint_12_61_p10 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 10 243966894724512178 = some 253376798210075067 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 8 2 243966894724512178 253376798210075067 253376798210075067 endpoint_12_61_p8 endpoint_12_61_w8
private theorem endpoint_12_61_w10 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 10 1 253376798210075067 = some 253376798210075067 := by decide +kernel
private theorem endpoint_12_61_p11 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 11 243966894724512178 = some 253376798210075067 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 10 1 243966894724512178 253376798210075067 253376798210075067 endpoint_12_61_p10 endpoint_12_61_w10
def endpoint_12_61 : CertifiedEndpoint :=
  ⟨⟨12, 61, 2801⟩, 253376798210075067, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_12_61_flag endpoint_12_61_sources 11 243966894724512178 253376798210075067 rfl endpoint_12_61_base endpoint_12_61_p11) (by decide)⟩
private def endpoint_12_62_flag : Flag := ⟨12, 62, 2752⟩
private def endpoint_12_62_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_12_62_base : receiptBase endpoint_12_62_flag endpoint_12_62_sources = some 244314358646267276 := by decide +kernel
private theorem endpoint_12_62_w0 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 2 244314358646267276 = some 251671102594100620 := by decide +kernel
private theorem endpoint_12_62_w2 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 2 2 251671102594100620 = some 251671102594100620 := by decide +kernel
private theorem endpoint_12_62_p4 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 4 244314358646267276 = some 251671102594100620 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 2 2 244314358646267276 251671102594100620 251671102594100620 endpoint_12_62_w0 endpoint_12_62_w2
private theorem endpoint_12_62_w4 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 4 2 251671102594100620 = some 251671102594100620 := by decide +kernel
private theorem endpoint_12_62_p6 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 6 244314358646267276 = some 251671102594100620 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 4 2 244314358646267276 251671102594100620 251671102594100620 endpoint_12_62_p4 endpoint_12_62_w4
private theorem endpoint_12_62_w6 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 6 2 251671102594100620 = some 251671102594100620 := by decide +kernel
private theorem endpoint_12_62_p8 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 8 244314358646267276 = some 251671102594100620 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 6 2 244314358646267276 251671102594100620 251671102594100620 endpoint_12_62_p6 endpoint_12_62_w6
private theorem endpoint_12_62_w8 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 8 2 251671102594100620 = some 251671102594100620 := by decide +kernel
private theorem endpoint_12_62_p10 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 10 244314358646267276 = some 251671102594100620 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 8 2 244314358646267276 251671102594100620 251671102594100620 endpoint_12_62_p8 endpoint_12_62_w8
private theorem endpoint_12_62_w10 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 10 1 251671102594100620 = some 251671102594100620 := by decide +kernel
private theorem endpoint_12_62_p11 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 11 244314358646267276 = some 251671102594100620 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 10 1 244314358646267276 251671102594100620 251671102594100620 endpoint_12_62_p10 endpoint_12_62_w10
def endpoint_12_62 : CertifiedEndpoint :=
  ⟨⟨12, 62, 2752⟩, 251671102594100620, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_12_62_flag endpoint_12_62_sources 11 244314358646267276 251671102594100620 rfl endpoint_12_62_base endpoint_12_62_p11) (by decide)⟩
private def endpoint_12_63_flag : Flag := ⟨12, 63, 2701⟩
private def endpoint_12_63_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_12_63_base : receiptBase endpoint_12_63_flag endpoint_12_63_sources = some 244397553823791593 := by decide +kernel
private theorem endpoint_12_63_w0 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 2 244397553823791593 = some 251076628699524495 := by decide +kernel
private theorem endpoint_12_63_w2 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 2 2 251076628699524495 = some 251076628699524495 := by decide +kernel
private theorem endpoint_12_63_p4 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 4 244397553823791593 = some 251076628699524495 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 2 2 244397553823791593 251076628699524495 251076628699524495 endpoint_12_63_w0 endpoint_12_63_w2
private theorem endpoint_12_63_w4 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 4 2 251076628699524495 = some 251076628699524495 := by decide +kernel
private theorem endpoint_12_63_p6 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 6 244397553823791593 = some 251076628699524495 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 4 2 244397553823791593 251076628699524495 251076628699524495 endpoint_12_63_p4 endpoint_12_63_w4
private theorem endpoint_12_63_w6 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 6 2 251076628699524495 = some 251076628699524495 := by decide +kernel
private theorem endpoint_12_63_p8 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 8 244397553823791593 = some 251076628699524495 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 6 2 244397553823791593 251076628699524495 251076628699524495 endpoint_12_63_p6 endpoint_12_63_w6
private theorem endpoint_12_63_w8 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 8 2 251076628699524495 = some 251076628699524495 := by decide +kernel
private theorem endpoint_12_63_p10 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 10 244397553823791593 = some 251076628699524495 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 8 2 244397553823791593 251076628699524495 251076628699524495 endpoint_12_63_p8 endpoint_12_63_w8
private theorem endpoint_12_63_w10 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 10 1 251076628699524495 = some 251076628699524495 := by decide +kernel
private theorem endpoint_12_63_p11 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 11 244397553823791593 = some 251076628699524495 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 10 1 244397553823791593 251076628699524495 251076628699524495 endpoint_12_63_p10 endpoint_12_63_w10
def endpoint_12_63 : CertifiedEndpoint :=
  ⟨⟨12, 63, 2701⟩, 251076628699524495, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_12_63_flag endpoint_12_63_sources 11 244397553823791593 251076628699524495 rfl endpoint_12_63_base endpoint_12_63_p11) (by decide)⟩
private def endpoint_12_64_flag : Flag := ⟨12, 64, 2648⟩
private def endpoint_12_64_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_64_base : receiptBase endpoint_12_64_flag endpoint_12_64_sources = some 244047397371481440 := by decide +kernel
private theorem endpoint_12_64_w0 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 2 244047397371481440 = some 245584532318725288 := by decide +kernel
private theorem endpoint_12_64_w2 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 2 2 245584532318725288 = some 245584532318725288 := by decide +kernel
private theorem endpoint_12_64_p4 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 4 244047397371481440 = some 245584532318725288 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 2 2 244047397371481440 245584532318725288 245584532318725288 endpoint_12_64_w0 endpoint_12_64_w2
private theorem endpoint_12_64_w4 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 4 2 245584532318725288 = some 245584532318725288 := by decide +kernel
private theorem endpoint_12_64_p6 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 6 244047397371481440 = some 245584532318725288 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 4 2 244047397371481440 245584532318725288 245584532318725288 endpoint_12_64_p4 endpoint_12_64_w4
private theorem endpoint_12_64_w6 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 6 2 245584532318725288 = some 245584532318725288 := by decide +kernel
private theorem endpoint_12_64_p8 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 8 244047397371481440 = some 245584532318725288 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 6 2 244047397371481440 245584532318725288 245584532318725288 endpoint_12_64_p6 endpoint_12_64_w6
private theorem endpoint_12_64_w8 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 8 2 245584532318725288 = some 245584532318725288 := by decide +kernel
private theorem endpoint_12_64_p10 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 10 244047397371481440 = some 245584532318725288 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 8 2 244047397371481440 245584532318725288 245584532318725288 endpoint_12_64_p8 endpoint_12_64_w8
private theorem endpoint_12_64_w10 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 10 1 245584532318725288 = some 245584532318725288 := by decide +kernel
private theorem endpoint_12_64_p11 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 11 244047397371481440 = some 245584532318725288 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 10 1 244047397371481440 245584532318725288 245584532318725288 endpoint_12_64_p10 endpoint_12_64_w10
def endpoint_12_64 : CertifiedEndpoint :=
  ⟨⟨12, 64, 2648⟩, 245584532318725288, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_64_flag endpoint_12_64_sources 11 244047397371481440 245584532318725288 rfl endpoint_12_64_base endpoint_12_64_p11) (by decide)⟩
private def endpoint_12_65_flag : Flag := ⟨12, 65, 2592⟩
private def endpoint_12_65_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_65_base : receiptBase endpoint_12_65_flag endpoint_12_65_sources = some 242255505864359313 := by decide +kernel
private theorem endpoint_12_65_w0 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 2 242255505864359313 = some 246949883747369793 := by decide +kernel
private theorem endpoint_12_65_w2 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 2 2 246949883747369793 = some 246949883747369793 := by decide +kernel
private theorem endpoint_12_65_p4 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 4 242255505864359313 = some 246949883747369793 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 2 2 242255505864359313 246949883747369793 246949883747369793 endpoint_12_65_w0 endpoint_12_65_w2
private theorem endpoint_12_65_w4 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 4 2 246949883747369793 = some 246949883747369793 := by decide +kernel
private theorem endpoint_12_65_p6 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 6 242255505864359313 = some 246949883747369793 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 4 2 242255505864359313 246949883747369793 246949883747369793 endpoint_12_65_p4 endpoint_12_65_w4
private theorem endpoint_12_65_w6 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 6 2 246949883747369793 = some 246949883747369793 := by decide +kernel
private theorem endpoint_12_65_p8 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 8 242255505864359313 = some 246949883747369793 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 6 2 242255505864359313 246949883747369793 246949883747369793 endpoint_12_65_p6 endpoint_12_65_w6
private theorem endpoint_12_65_w8 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 8 2 246949883747369793 = some 246949883747369793 := by decide +kernel
private theorem endpoint_12_65_p10 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 10 242255505864359313 = some 246949883747369793 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 8 2 242255505864359313 246949883747369793 246949883747369793 endpoint_12_65_p8 endpoint_12_65_w8
private theorem endpoint_12_65_w10 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 10 1 246949883747369793 = some 246949883747369793 := by decide +kernel
private theorem endpoint_12_65_p11 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 11 242255505864359313 = some 246949883747369793 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 10 1 242255505864359313 246949883747369793 246949883747369793 endpoint_12_65_p10 endpoint_12_65_w10
def endpoint_12_65 : CertifiedEndpoint :=
  ⟨⟨12, 65, 2592⟩, 246949883747369793, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_65_flag endpoint_12_65_sources 11 242255505864359313 246949883747369793 rfl endpoint_12_65_base endpoint_12_65_p11) (by decide)⟩
private def endpoint_12_66_flag : Flag := ⟨12, 66, 2534⟩
private def endpoint_12_66_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_66_base : receiptBase endpoint_12_66_flag endpoint_12_66_sources = some 240132794577665605 := by decide +kernel
private theorem endpoint_12_66_w0 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 2 240132794577665605 = some 248109415085467188 := by decide +kernel
private theorem endpoint_12_66_w2 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 2 2 248109415085467188 = some 248109415085467188 := by decide +kernel
private theorem endpoint_12_66_p4 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 4 240132794577665605 = some 248109415085467188 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 2 2 240132794577665605 248109415085467188 248109415085467188 endpoint_12_66_w0 endpoint_12_66_w2
private theorem endpoint_12_66_w4 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 4 2 248109415085467188 = some 248109415085467188 := by decide +kernel
private theorem endpoint_12_66_p6 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 6 240132794577665605 = some 248109415085467188 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 4 2 240132794577665605 248109415085467188 248109415085467188 endpoint_12_66_p4 endpoint_12_66_w4
private theorem endpoint_12_66_w6 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 6 2 248109415085467188 = some 248109415085467188 := by decide +kernel
private theorem endpoint_12_66_p8 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 8 240132794577665605 = some 248109415085467188 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 6 2 240132794577665605 248109415085467188 248109415085467188 endpoint_12_66_p6 endpoint_12_66_w6
private theorem endpoint_12_66_w8 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 8 2 248109415085467188 = some 248109415085467188 := by decide +kernel
private theorem endpoint_12_66_p10 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 10 240132794577665605 = some 248109415085467188 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 8 2 240132794577665605 248109415085467188 248109415085467188 endpoint_12_66_p8 endpoint_12_66_w8
private theorem endpoint_12_66_w10 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 10 1 248109415085467188 = some 248109415085467188 := by decide +kernel
private theorem endpoint_12_66_p11 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 11 240132794577665605 = some 248109415085467188 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 10 1 240132794577665605 248109415085467188 248109415085467188 endpoint_12_66_p10 endpoint_12_66_w10
def endpoint_12_66 : CertifiedEndpoint :=
  ⟨⟨12, 66, 2534⟩, 248109415085467188, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_66_flag endpoint_12_66_sources 11 240132794577665605 248109415085467188 rfl endpoint_12_66_base endpoint_12_66_p11) (by decide)⟩
private def endpoint_12_67_flag : Flag := ⟨12, 67, 2474⟩
private def endpoint_12_67_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_67_base : receiptBase endpoint_12_67_flag endpoint_12_67_sources = some 237671639544595081 := by decide +kernel
private theorem endpoint_12_67_w0 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 2 237671639544595081 = some 249057817618565719 := by decide +kernel
private theorem endpoint_12_67_w2 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 2 2 249057817618565719 = some 249057817618565719 := by decide +kernel
private theorem endpoint_12_67_p4 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 4 237671639544595081 = some 249057817618565719 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 2 2 237671639544595081 249057817618565719 249057817618565719 endpoint_12_67_w0 endpoint_12_67_w2
private theorem endpoint_12_67_w4 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 4 2 249057817618565719 = some 249057817618565719 := by decide +kernel
private theorem endpoint_12_67_p6 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 6 237671639544595081 = some 249057817618565719 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 4 2 237671639544595081 249057817618565719 249057817618565719 endpoint_12_67_p4 endpoint_12_67_w4
private theorem endpoint_12_67_w6 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 6 2 249057817618565719 = some 249057817618565719 := by decide +kernel
private theorem endpoint_12_67_p8 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 8 237671639544595081 = some 249057817618565719 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 6 2 237671639544595081 249057817618565719 249057817618565719 endpoint_12_67_p6 endpoint_12_67_w6
private theorem endpoint_12_67_w8 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 8 2 249057817618565719 = some 249057817618565719 := by decide +kernel
private theorem endpoint_12_67_p10 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 10 237671639544595081 = some 249057817618565719 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 8 2 237671639544595081 249057817618565719 249057817618565719 endpoint_12_67_p8 endpoint_12_67_w8
private theorem endpoint_12_67_w10 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 10 1 249057817618565719 = some 249057817618565719 := by decide +kernel
private theorem endpoint_12_67_p11 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 11 237671639544595081 = some 249057817618565719 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 10 1 237671639544595081 249057817618565719 249057817618565719 endpoint_12_67_p10 endpoint_12_67_w10
def endpoint_12_67 : CertifiedEndpoint :=
  ⟨⟨12, 67, 2474⟩, 249057817618565719, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_67_flag endpoint_12_67_sources 11 237671639544595081 249057817618565719 rfl endpoint_12_67_base endpoint_12_67_p11) (by decide)⟩
private def endpoint_12_68_flag : Flag := ⟨12, 68, 2411⟩
private def endpoint_12_68_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_12_68_base : receiptBase endpoint_12_68_flag endpoint_12_68_sources = some 240170364042926827 := by decide +kernel
private theorem endpoint_12_68_w0 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 2 240170364042926827 = some 240170364042926827 := by decide +kernel
private theorem endpoint_12_68_w2 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 2 2 240170364042926827 = some 240170364042926827 := by decide +kernel
private theorem endpoint_12_68_p4 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 4 240170364042926827 = some 240170364042926827 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 2 2 240170364042926827 240170364042926827 240170364042926827 endpoint_12_68_w0 endpoint_12_68_w2
private theorem endpoint_12_68_w4 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 4 2 240170364042926827 = some 240170364042926827 := by decide +kernel
private theorem endpoint_12_68_p6 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 6 240170364042926827 = some 240170364042926827 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 4 2 240170364042926827 240170364042926827 240170364042926827 endpoint_12_68_p4 endpoint_12_68_w4
private theorem endpoint_12_68_w6 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 6 2 240170364042926827 = some 240170364042926827 := by decide +kernel
private theorem endpoint_12_68_p8 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 8 240170364042926827 = some 240170364042926827 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 6 2 240170364042926827 240170364042926827 240170364042926827 endpoint_12_68_p6 endpoint_12_68_w6
private theorem endpoint_12_68_w8 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 8 2 240170364042926827 = some 240170364042926827 := by decide +kernel
private theorem endpoint_12_68_p10 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 10 240170364042926827 = some 240170364042926827 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 8 2 240170364042926827 240170364042926827 240170364042926827 endpoint_12_68_p8 endpoint_12_68_w8
private theorem endpoint_12_68_w10 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 10 1 240170364042926827 = some 240170364042926827 := by decide +kernel
private theorem endpoint_12_68_p11 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 11 240170364042926827 = some 240170364042926827 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 10 1 240170364042926827 240170364042926827 240170364042926827 endpoint_12_68_p10 endpoint_12_68_w10
def endpoint_12_68 : CertifiedEndpoint :=
  ⟨⟨12, 68, 2411⟩, 240170364042926827, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_12_68_flag endpoint_12_68_sources 11 240170364042926827 240170364042926827 rfl endpoint_12_68_base endpoint_12_68_p11) (by decide)⟩
private def endpoint_12_69_flag : Flag := ⟨12, 69, 2346⟩
private def endpoint_12_69_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_12_69_base : receiptBase endpoint_12_69_flag endpoint_12_69_sources = some 236878881703534603 := by decide +kernel
private theorem endpoint_12_69_w0 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 2 236878881703534603 = some 237424621026383175 := by decide +kernel
private theorem endpoint_12_69_w2 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 2 2 237424621026383175 = some 237424621026383175 := by decide +kernel
private theorem endpoint_12_69_p4 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 4 236878881703534603 = some 237424621026383175 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 2 2 236878881703534603 237424621026383175 237424621026383175 endpoint_12_69_w0 endpoint_12_69_w2
private theorem endpoint_12_69_w4 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 4 2 237424621026383175 = some 237424621026383175 := by decide +kernel
private theorem endpoint_12_69_p6 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 6 236878881703534603 = some 237424621026383175 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 4 2 236878881703534603 237424621026383175 237424621026383175 endpoint_12_69_p4 endpoint_12_69_w4
private theorem endpoint_12_69_w6 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 6 2 237424621026383175 = some 237424621026383175 := by decide +kernel
private theorem endpoint_12_69_p8 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 8 236878881703534603 = some 237424621026383175 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 6 2 236878881703534603 237424621026383175 237424621026383175 endpoint_12_69_p6 endpoint_12_69_w6
private theorem endpoint_12_69_w8 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 8 2 237424621026383175 = some 237424621026383175 := by decide +kernel
private theorem endpoint_12_69_p10 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 10 236878881703534603 = some 237424621026383175 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 8 2 236878881703534603 237424621026383175 237424621026383175 endpoint_12_69_p8 endpoint_12_69_w8
private theorem endpoint_12_69_w10 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 10 1 237424621026383175 = some 237424621026383175 := by decide +kernel
private theorem endpoint_12_69_p11 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 11 236878881703534603 = some 237424621026383175 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 10 1 236878881703534603 237424621026383175 237424621026383175 endpoint_12_69_p10 endpoint_12_69_w10
def endpoint_12_69 : CertifiedEndpoint :=
  ⟨⟨12, 69, 2346⟩, 237424621026383175, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_12_69_flag endpoint_12_69_sources 11 236878881703534603 237424621026383175 rfl endpoint_12_69_base endpoint_12_69_p11) (by decide)⟩
private def endpoint_12_70_flag : Flag := ⟨12, 70, 2278⟩
private def endpoint_12_70_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_12_70_base : receiptBase endpoint_12_70_flag endpoint_12_70_sources = some 233120871337471228 := by decide +kernel
private theorem endpoint_12_70_w0 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 2 233120871337471228 = some 237390000819286244 := by decide +kernel
private theorem endpoint_12_70_w2 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 2 2 237390000819286244 = some 237390000819286244 := by decide +kernel
private theorem endpoint_12_70_p4 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 4 233120871337471228 = some 237390000819286244 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 2 2 233120871337471228 237390000819286244 237390000819286244 endpoint_12_70_w0 endpoint_12_70_w2
private theorem endpoint_12_70_w4 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 4 2 237390000819286244 = some 237390000819286244 := by decide +kernel
private theorem endpoint_12_70_p6 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 6 233120871337471228 = some 237390000819286244 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 4 2 233120871337471228 237390000819286244 237390000819286244 endpoint_12_70_p4 endpoint_12_70_w4
private theorem endpoint_12_70_w6 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 6 2 237390000819286244 = some 237390000819286244 := by decide +kernel
private theorem endpoint_12_70_p8 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 8 233120871337471228 = some 237390000819286244 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 6 2 233120871337471228 237390000819286244 237390000819286244 endpoint_12_70_p6 endpoint_12_70_w6
private theorem endpoint_12_70_w8 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 8 2 237390000819286244 = some 237390000819286244 := by decide +kernel
private theorem endpoint_12_70_p10 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 10 233120871337471228 = some 237390000819286244 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 8 2 233120871337471228 237390000819286244 237390000819286244 endpoint_12_70_p8 endpoint_12_70_w8
private theorem endpoint_12_70_w10 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 10 1 237390000819286244 = some 237390000819286244 := by decide +kernel
private theorem endpoint_12_70_p11 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 11 233120871337471228 = some 237390000819286244 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 10 1 233120871337471228 237390000819286244 237390000819286244 endpoint_12_70_p10 endpoint_12_70_w10
def endpoint_12_70 : CertifiedEndpoint :=
  ⟨⟨12, 70, 2278⟩, 237390000819286244, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_12_70_flag endpoint_12_70_sources 11 233120871337471228 237390000819286244 rfl endpoint_12_70_base endpoint_12_70_p11) (by decide)⟩
private def endpoint_12_71_flag : Flag := ⟨12, 71, 2208⟩
private def endpoint_12_71_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_12_71_base : receiptBase endpoint_12_71_flag endpoint_12_71_sources = some 230424983238680985 := by decide +kernel
private theorem endpoint_12_71_w0 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 2 230424983238680985 = some 230424983238680985 := by decide +kernel
private theorem endpoint_12_71_w2 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 2 2 230424983238680985 = some 230424983238680985 := by decide +kernel
private theorem endpoint_12_71_p4 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 4 230424983238680985 = some 230424983238680985 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 2 2 230424983238680985 230424983238680985 230424983238680985 endpoint_12_71_w0 endpoint_12_71_w2
private theorem endpoint_12_71_w4 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 4 2 230424983238680985 = some 230424983238680985 := by decide +kernel
private theorem endpoint_12_71_p6 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 6 230424983238680985 = some 230424983238680985 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 4 2 230424983238680985 230424983238680985 230424983238680985 endpoint_12_71_p4 endpoint_12_71_w4
private theorem endpoint_12_71_w6 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 6 2 230424983238680985 = some 230424983238680985 := by decide +kernel
private theorem endpoint_12_71_p8 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 8 230424983238680985 = some 230424983238680985 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 6 2 230424983238680985 230424983238680985 230424983238680985 endpoint_12_71_p6 endpoint_12_71_w6
private theorem endpoint_12_71_w8 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 8 2 230424983238680985 = some 230424983238680985 := by decide +kernel
private theorem endpoint_12_71_p10 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 10 230424983238680985 = some 230424983238680985 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 8 2 230424983238680985 230424983238680985 230424983238680985 endpoint_12_71_p8 endpoint_12_71_w8
private theorem endpoint_12_71_w10 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 10 1 230424983238680985 = some 230424983238680985 := by decide +kernel
private theorem endpoint_12_71_p11 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 11 230424983238680985 = some 230424983238680985 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 10 1 230424983238680985 230424983238680985 230424983238680985 endpoint_12_71_p10 endpoint_12_71_w10
def endpoint_12_71 : CertifiedEndpoint :=
  ⟨⟨12, 71, 2208⟩, 230424983238680985, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_12_71_flag endpoint_12_71_sources 11 230424983238680985 230424983238680985 rfl endpoint_12_71_base endpoint_12_71_p11) (by decide)⟩
private def endpoint_12_72_flag : Flag := ⟨12, 72, 2136⟩
private def endpoint_12_72_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_12_72_base : receiptBase endpoint_12_72_flag endpoint_12_72_sources = some 225877375022378454 := by decide +kernel
private theorem endpoint_12_72_w0 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 2 225877375022378454 = some 225877375022378454 := by decide +kernel
private theorem endpoint_12_72_w2 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 2 2 225877375022378454 = some 225877375022378454 := by decide +kernel
private theorem endpoint_12_72_p4 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 4 225877375022378454 = some 225877375022378454 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 2 2 225877375022378454 225877375022378454 225877375022378454 endpoint_12_72_w0 endpoint_12_72_w2
private theorem endpoint_12_72_w4 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 4 2 225877375022378454 = some 225877375022378454 := by decide +kernel
private theorem endpoint_12_72_p6 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 6 225877375022378454 = some 225877375022378454 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 4 2 225877375022378454 225877375022378454 225877375022378454 endpoint_12_72_p4 endpoint_12_72_w4
private theorem endpoint_12_72_w6 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 6 2 225877375022378454 = some 225877375022378454 := by decide +kernel
private theorem endpoint_12_72_p8 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 8 225877375022378454 = some 225877375022378454 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 6 2 225877375022378454 225877375022378454 225877375022378454 endpoint_12_72_p6 endpoint_12_72_w6
private theorem endpoint_12_72_w8 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 8 2 225877375022378454 = some 225877375022378454 := by decide +kernel
private theorem endpoint_12_72_p10 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 10 225877375022378454 = some 225877375022378454 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 8 2 225877375022378454 225877375022378454 225877375022378454 endpoint_12_72_p8 endpoint_12_72_w8
private theorem endpoint_12_72_w10 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 10 1 225877375022378454 = some 225877375022378454 := by decide +kernel
private theorem endpoint_12_72_p11 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 11 225877375022378454 = some 225877375022378454 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 10 1 225877375022378454 225877375022378454 225877375022378454 endpoint_12_72_p10 endpoint_12_72_w10
def endpoint_12_72 : CertifiedEndpoint :=
  ⟨⟨12, 72, 2136⟩, 225877375022378454, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_12_72_flag endpoint_12_72_sources 11 225877375022378454 225877375022378454 rfl endpoint_12_72_base endpoint_12_72_p11) (by decide)⟩
private def endpoint_12_73_flag : Flag := ⟨12, 73, 2060⟩
private def endpoint_12_73_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_12_73_base : receiptBase endpoint_12_73_flag endpoint_12_73_sources = some 222273885544669359 := by decide +kernel
private theorem endpoint_12_73_w0 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 2 222273885544669359 = some 222273885544669359 := by decide +kernel
private theorem endpoint_12_73_w2 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 2 2 222273885544669359 = some 222273885544669359 := by decide +kernel
private theorem endpoint_12_73_p4 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 4 222273885544669359 = some 222273885544669359 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 2 2 222273885544669359 222273885544669359 222273885544669359 endpoint_12_73_w0 endpoint_12_73_w2
private theorem endpoint_12_73_w4 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 4 2 222273885544669359 = some 222273885544669359 := by decide +kernel
private theorem endpoint_12_73_p6 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 6 222273885544669359 = some 222273885544669359 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 4 2 222273885544669359 222273885544669359 222273885544669359 endpoint_12_73_p4 endpoint_12_73_w4
private theorem endpoint_12_73_w6 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 6 2 222273885544669359 = some 222273885544669359 := by decide +kernel
private theorem endpoint_12_73_p8 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 8 222273885544669359 = some 222273885544669359 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 6 2 222273885544669359 222273885544669359 222273885544669359 endpoint_12_73_p6 endpoint_12_73_w6
private theorem endpoint_12_73_w8 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 8 2 222273885544669359 = some 222273885544669359 := by decide +kernel
private theorem endpoint_12_73_p10 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 10 222273885544669359 = some 222273885544669359 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 8 2 222273885544669359 222273885544669359 222273885544669359 endpoint_12_73_p8 endpoint_12_73_w8
private theorem endpoint_12_73_w10 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 10 1 222273885544669359 = some 222273885544669359 := by decide +kernel
private theorem endpoint_12_73_p11 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 11 222273885544669359 = some 222273885544669359 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 10 1 222273885544669359 222273885544669359 222273885544669359 endpoint_12_73_p10 endpoint_12_73_w10
def endpoint_12_73 : CertifiedEndpoint :=
  ⟨⟨12, 73, 2060⟩, 222273885544669359, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_12_73_flag endpoint_12_73_sources 11 222273885544669359 222273885544669359 rfl endpoint_12_73_base endpoint_12_73_p11) (by decide)⟩
private def endpoint_12_74_flag : Flag := ⟨12, 74, 1983⟩
private def endpoint_12_74_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_12_74_base : receiptBase endpoint_12_74_flag endpoint_12_74_sources = some 216676551490828602 := by decide +kernel
private theorem endpoint_12_74_w0 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 2 216676551490828602 = some 216676551490828602 := by decide +kernel
private theorem endpoint_12_74_w2 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 2 2 216676551490828602 = some 216676551490828602 := by decide +kernel
private theorem endpoint_12_74_p4 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 4 216676551490828602 = some 216676551490828602 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 2 2 216676551490828602 216676551490828602 216676551490828602 endpoint_12_74_w0 endpoint_12_74_w2
private theorem endpoint_12_74_w4 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 4 2 216676551490828602 = some 216676551490828602 := by decide +kernel
private theorem endpoint_12_74_p6 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 6 216676551490828602 = some 216676551490828602 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 4 2 216676551490828602 216676551490828602 216676551490828602 endpoint_12_74_p4 endpoint_12_74_w4
private theorem endpoint_12_74_w6 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 6 2 216676551490828602 = some 216676551490828602 := by decide +kernel
private theorem endpoint_12_74_p8 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 8 216676551490828602 = some 216676551490828602 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 6 2 216676551490828602 216676551490828602 216676551490828602 endpoint_12_74_p6 endpoint_12_74_w6
private theorem endpoint_12_74_w8 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 8 2 216676551490828602 = some 216676551490828602 := by decide +kernel
private theorem endpoint_12_74_p10 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 10 216676551490828602 = some 216676551490828602 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 8 2 216676551490828602 216676551490828602 216676551490828602 endpoint_12_74_p8 endpoint_12_74_w8
private theorem endpoint_12_74_w10 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 10 1 216676551490828602 = some 216676551490828602 := by decide +kernel
private theorem endpoint_12_74_p11 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 11 216676551490828602 = some 216676551490828602 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 10 1 216676551490828602 216676551490828602 216676551490828602 endpoint_12_74_p10 endpoint_12_74_w10
def endpoint_12_74 : CertifiedEndpoint :=
  ⟨⟨12, 74, 1983⟩, 216676551490828602, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_12_74_flag endpoint_12_74_sources 11 216676551490828602 216676551490828602 rfl endpoint_12_74_base endpoint_12_74_p11) (by decide)⟩
private def endpoint_12_75_flag : Flag := ⟨12, 75, 1902⟩
private def endpoint_12_75_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_12_75_base : receiptBase endpoint_12_75_flag endpoint_12_75_sources = some 212121415533254214 := by decide +kernel
private theorem endpoint_12_75_w0 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 2 212121415533254214 = some 212121415533254214 := by decide +kernel
private theorem endpoint_12_75_w2 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 2 2 212121415533254214 = some 212121415533254214 := by decide +kernel
private theorem endpoint_12_75_p4 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 4 212121415533254214 = some 212121415533254214 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 2 2 212121415533254214 212121415533254214 212121415533254214 endpoint_12_75_w0 endpoint_12_75_w2
private theorem endpoint_12_75_w4 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 4 2 212121415533254214 = some 212121415533254214 := by decide +kernel
private theorem endpoint_12_75_p6 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 6 212121415533254214 = some 212121415533254214 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 4 2 212121415533254214 212121415533254214 212121415533254214 endpoint_12_75_p4 endpoint_12_75_w4
private theorem endpoint_12_75_w6 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 6 2 212121415533254214 = some 212121415533254214 := by decide +kernel
private theorem endpoint_12_75_p8 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 8 212121415533254214 = some 212121415533254214 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 6 2 212121415533254214 212121415533254214 212121415533254214 endpoint_12_75_p6 endpoint_12_75_w6
private theorem endpoint_12_75_w8 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 8 2 212121415533254214 = some 212121415533254214 := by decide +kernel
private theorem endpoint_12_75_p10 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 10 212121415533254214 = some 212121415533254214 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 8 2 212121415533254214 212121415533254214 212121415533254214 endpoint_12_75_p8 endpoint_12_75_w8
private theorem endpoint_12_75_w10 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 10 1 212121415533254214 = some 212121415533254214 := by decide +kernel
private theorem endpoint_12_75_p11 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 11 212121415533254214 = some 212121415533254214 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 10 1 212121415533254214 212121415533254214 212121415533254214 endpoint_12_75_p10 endpoint_12_75_w10
def endpoint_12_75 : CertifiedEndpoint :=
  ⟨⟨12, 75, 1902⟩, 212121415533254214, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_12_75_flag endpoint_12_75_sources 11 212121415533254214 212121415533254214 rfl endpoint_12_75_base endpoint_12_75_p11) (by decide)⟩
private def endpoint_12_76_flag : Flag := ⟨12, 76, 1819⟩
private def endpoint_12_76_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_12_76_base : receiptBase endpoint_12_76_flag endpoint_12_76_sources = some 205363707183387113 := by decide +kernel
private theorem endpoint_12_76_w0 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 2 205363707183387113 = some 205363707183387113 := by decide +kernel
private theorem endpoint_12_76_w2 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 2 2 205363707183387113 = some 205363707183387113 := by decide +kernel
private theorem endpoint_12_76_p4 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 4 205363707183387113 = some 205363707183387113 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 2 2 205363707183387113 205363707183387113 205363707183387113 endpoint_12_76_w0 endpoint_12_76_w2
private theorem endpoint_12_76_w4 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 4 2 205363707183387113 = some 205363707183387113 := by decide +kernel
private theorem endpoint_12_76_p6 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 6 205363707183387113 = some 205363707183387113 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 4 2 205363707183387113 205363707183387113 205363707183387113 endpoint_12_76_p4 endpoint_12_76_w4
private theorem endpoint_12_76_w6 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 6 2 205363707183387113 = some 205363707183387113 := by decide +kernel
private theorem endpoint_12_76_p8 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 8 205363707183387113 = some 205363707183387113 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 6 2 205363707183387113 205363707183387113 205363707183387113 endpoint_12_76_p6 endpoint_12_76_w6
private theorem endpoint_12_76_w8 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 8 2 205363707183387113 = some 205363707183387113 := by decide +kernel
private theorem endpoint_12_76_p10 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 10 205363707183387113 = some 205363707183387113 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 8 2 205363707183387113 205363707183387113 205363707183387113 endpoint_12_76_p8 endpoint_12_76_w8
private theorem endpoint_12_76_w10 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 10 1 205363707183387113 = some 205363707183387113 := by decide +kernel
private theorem endpoint_12_76_p11 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 11 205363707183387113 = some 205363707183387113 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 10 1 205363707183387113 205363707183387113 205363707183387113 endpoint_12_76_p10 endpoint_12_76_w10
def endpoint_12_76 : CertifiedEndpoint :=
  ⟨⟨12, 76, 1819⟩, 205363707183387113, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_12_76_flag endpoint_12_76_sources 11 205363707183387113 205363707183387113 rfl endpoint_12_76_base endpoint_12_76_p11) (by decide)⟩
private def endpoint_12_77_flag : Flag := ⟨12, 77, 1734⟩
private def endpoint_12_77_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_12_77_base : receiptBase endpoint_12_77_flag endpoint_12_77_sources = some 198159730829014425 := by decide +kernel
private theorem endpoint_12_77_w0 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 2 198159730829014425 = some 198159730829014425 := by decide +kernel
private theorem endpoint_12_77_w2 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 2 2 198159730829014425 = some 198159730829014425 := by decide +kernel
private theorem endpoint_12_77_p4 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 4 198159730829014425 = some 198159730829014425 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 2 2 198159730829014425 198159730829014425 198159730829014425 endpoint_12_77_w0 endpoint_12_77_w2
private theorem endpoint_12_77_w4 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 4 2 198159730829014425 = some 198159730829014425 := by decide +kernel
private theorem endpoint_12_77_p6 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 6 198159730829014425 = some 198159730829014425 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 4 2 198159730829014425 198159730829014425 198159730829014425 endpoint_12_77_p4 endpoint_12_77_w4
private theorem endpoint_12_77_w6 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 6 2 198159730829014425 = some 198159730829014425 := by decide +kernel
private theorem endpoint_12_77_p8 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 8 198159730829014425 = some 198159730829014425 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 6 2 198159730829014425 198159730829014425 198159730829014425 endpoint_12_77_p6 endpoint_12_77_w6
private theorem endpoint_12_77_w8 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 8 2 198159730829014425 = some 198159730829014425 := by decide +kernel
private theorem endpoint_12_77_p10 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 10 198159730829014425 = some 198159730829014425 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 8 2 198159730829014425 198159730829014425 198159730829014425 endpoint_12_77_p8 endpoint_12_77_w8
private theorem endpoint_12_77_w10 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 10 1 198159730829014425 = some 198159730829014425 := by decide +kernel
private theorem endpoint_12_77_p11 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 11 198159730829014425 = some 198159730829014425 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 10 1 198159730829014425 198159730829014425 198159730829014425 endpoint_12_77_p10 endpoint_12_77_w10
def endpoint_12_77 : CertifiedEndpoint :=
  ⟨⟨12, 77, 1734⟩, 198159730829014425, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_12_77_flag endpoint_12_77_sources 11 198159730829014425 198159730829014425 rfl endpoint_12_77_base endpoint_12_77_p11) (by decide)⟩
private def endpoint_12_78_flag : Flag := ⟨12, 78, 1646⟩
private def endpoint_12_78_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_12_78_base : receiptBase endpoint_12_78_flag endpoint_12_78_sources = some 193623779997683291 := by decide +kernel
private theorem endpoint_12_78_w0 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 2 193623779997683291 = some 193623779997683291 := by decide +kernel
private theorem endpoint_12_78_w2 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 2 2 193623779997683291 = some 193623779997683291 := by decide +kernel
private theorem endpoint_12_78_p4 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 4 193623779997683291 = some 193623779997683291 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 2 2 193623779997683291 193623779997683291 193623779997683291 endpoint_12_78_w0 endpoint_12_78_w2
private theorem endpoint_12_78_w4 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 4 2 193623779997683291 = some 193623779997683291 := by decide +kernel
private theorem endpoint_12_78_p6 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 6 193623779997683291 = some 193623779997683291 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 4 2 193623779997683291 193623779997683291 193623779997683291 endpoint_12_78_p4 endpoint_12_78_w4
private theorem endpoint_12_78_w6 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 6 2 193623779997683291 = some 193623779997683291 := by decide +kernel
private theorem endpoint_12_78_p8 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 8 193623779997683291 = some 193623779997683291 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 6 2 193623779997683291 193623779997683291 193623779997683291 endpoint_12_78_p6 endpoint_12_78_w6
private theorem endpoint_12_78_w8 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 8 2 193623779997683291 = some 193623779997683291 := by decide +kernel
private theorem endpoint_12_78_p10 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 10 193623779997683291 = some 193623779997683291 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 8 2 193623779997683291 193623779997683291 193623779997683291 endpoint_12_78_p8 endpoint_12_78_w8
private theorem endpoint_12_78_w10 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 10 1 193623779997683291 = some 193623779997683291 := by decide +kernel
private theorem endpoint_12_78_p11 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 11 193623779997683291 = some 193623779997683291 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 10 1 193623779997683291 193623779997683291 193623779997683291 endpoint_12_78_p10 endpoint_12_78_w10
def endpoint_12_78 : CertifiedEndpoint :=
  ⟨⟨12, 78, 1646⟩, 193623779997683291, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_12_78_flag endpoint_12_78_sources 11 193623779997683291 193623779997683291 rfl endpoint_12_78_base endpoint_12_78_p11) (by decide)⟩
private def endpoint_12_79_flag : Flag := ⟨12, 79, 1555⟩
private def endpoint_12_79_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_12_79_base : receiptBase endpoint_12_79_flag endpoint_12_79_sources = some 185073507973370689 := by decide +kernel
private theorem endpoint_12_79_w0 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 2 185073507973370689 = some 185073507973370689 := by decide +kernel
private theorem endpoint_12_79_w2 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 2 2 185073507973370689 = some 185073507973370689 := by decide +kernel
private theorem endpoint_12_79_p4 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 4 185073507973370689 = some 185073507973370689 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 2 2 185073507973370689 185073507973370689 185073507973370689 endpoint_12_79_w0 endpoint_12_79_w2
private theorem endpoint_12_79_w4 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 4 2 185073507973370689 = some 185073507973370689 := by decide +kernel
private theorem endpoint_12_79_p6 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 6 185073507973370689 = some 185073507973370689 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 4 2 185073507973370689 185073507973370689 185073507973370689 endpoint_12_79_p4 endpoint_12_79_w4
private theorem endpoint_12_79_w6 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 6 2 185073507973370689 = some 185073507973370689 := by decide +kernel
private theorem endpoint_12_79_p8 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 8 185073507973370689 = some 185073507973370689 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 6 2 185073507973370689 185073507973370689 185073507973370689 endpoint_12_79_p6 endpoint_12_79_w6
private theorem endpoint_12_79_w8 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 8 2 185073507973370689 = some 185073507973370689 := by decide +kernel
private theorem endpoint_12_79_p10 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 10 185073507973370689 = some 185073507973370689 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 8 2 185073507973370689 185073507973370689 185073507973370689 endpoint_12_79_p8 endpoint_12_79_w8
private theorem endpoint_12_79_w10 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 10 1 185073507973370689 = some 185073507973370689 := by decide +kernel
private theorem endpoint_12_79_p11 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 11 185073507973370689 = some 185073507973370689 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 10 1 185073507973370689 185073507973370689 185073507973370689 endpoint_12_79_p10 endpoint_12_79_w10
def endpoint_12_79 : CertifiedEndpoint :=
  ⟨⟨12, 79, 1555⟩, 185073507973370689, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_12_79_flag endpoint_12_79_sources 11 185073507973370689 185073507973370689 rfl endpoint_12_79_base endpoint_12_79_p11) (by decide)⟩
private def endpoint_12_80_flag : Flag := ⟨12, 80, 1462⟩
private def endpoint_12_80_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_12_80_base : receiptBase endpoint_12_80_flag endpoint_12_80_sources = some 176381598087497730 := by decide +kernel
private theorem endpoint_12_80_w0 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 2 176381598087497730 = some 176381598087497730 := by decide +kernel
private theorem endpoint_12_80_w2 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 2 2 176381598087497730 = some 176381598087497730 := by decide +kernel
private theorem endpoint_12_80_p4 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 4 176381598087497730 = some 176381598087497730 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 2 2 176381598087497730 176381598087497730 176381598087497730 endpoint_12_80_w0 endpoint_12_80_w2
private theorem endpoint_12_80_w4 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 4 2 176381598087497730 = some 176381598087497730 := by decide +kernel
private theorem endpoint_12_80_p6 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 6 176381598087497730 = some 176381598087497730 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 4 2 176381598087497730 176381598087497730 176381598087497730 endpoint_12_80_p4 endpoint_12_80_w4
private theorem endpoint_12_80_w6 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 6 2 176381598087497730 = some 176381598087497730 := by decide +kernel
private theorem endpoint_12_80_p8 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 8 176381598087497730 = some 176381598087497730 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 6 2 176381598087497730 176381598087497730 176381598087497730 endpoint_12_80_p6 endpoint_12_80_w6
private theorem endpoint_12_80_w8 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 8 2 176381598087497730 = some 176381598087497730 := by decide +kernel
private theorem endpoint_12_80_p10 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 10 176381598087497730 = some 176381598087497730 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 8 2 176381598087497730 176381598087497730 176381598087497730 endpoint_12_80_p8 endpoint_12_80_w8
private theorem endpoint_12_80_w10 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 10 1 176381598087497730 = some 176381598087497730 := by decide +kernel
private theorem endpoint_12_80_p11 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 11 176381598087497730 = some 176381598087497730 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 10 1 176381598087497730 176381598087497730 176381598087497730 endpoint_12_80_p10 endpoint_12_80_w10
def endpoint_12_80 : CertifiedEndpoint :=
  ⟨⟨12, 80, 1462⟩, 176381598087497730, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_12_80_flag endpoint_12_80_sources 11 176381598087497730 176381598087497730 rfl endpoint_12_80_base endpoint_12_80_p11) (by decide)⟩
private def endpoint_12_81_flag : Flag := ⟨12, 81, 1366⟩
private def endpoint_12_81_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_12_81_base : receiptBase endpoint_12_81_flag endpoint_12_81_sources = some 167661679112684734 := by decide +kernel
private theorem endpoint_12_81_w0 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 2 167661679112684734 = some 167661679112684734 := by decide +kernel
private theorem endpoint_12_81_w2 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 2 2 167661679112684734 = some 167661679112684734 := by decide +kernel
private theorem endpoint_12_81_p4 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 4 167661679112684734 = some 167661679112684734 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 2 2 167661679112684734 167661679112684734 167661679112684734 endpoint_12_81_w0 endpoint_12_81_w2
private theorem endpoint_12_81_w4 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 4 2 167661679112684734 = some 167661679112684734 := by decide +kernel
private theorem endpoint_12_81_p6 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 6 167661679112684734 = some 167661679112684734 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 4 2 167661679112684734 167661679112684734 167661679112684734 endpoint_12_81_p4 endpoint_12_81_w4
private theorem endpoint_12_81_w6 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 6 2 167661679112684734 = some 167661679112684734 := by decide +kernel
private theorem endpoint_12_81_p8 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 8 167661679112684734 = some 167661679112684734 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 6 2 167661679112684734 167661679112684734 167661679112684734 endpoint_12_81_p6 endpoint_12_81_w6
private theorem endpoint_12_81_w8 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 8 2 167661679112684734 = some 167661679112684734 := by decide +kernel
private theorem endpoint_12_81_p10 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 10 167661679112684734 = some 167661679112684734 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 8 2 167661679112684734 167661679112684734 167661679112684734 endpoint_12_81_p8 endpoint_12_81_w8
private theorem endpoint_12_81_w10 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 10 1 167661679112684734 = some 167661679112684734 := by decide +kernel
private theorem endpoint_12_81_p11 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 11 167661679112684734 = some 167661679112684734 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 10 1 167661679112684734 167661679112684734 167661679112684734 endpoint_12_81_p10 endpoint_12_81_w10
def endpoint_12_81 : CertifiedEndpoint :=
  ⟨⟨12, 81, 1366⟩, 167661679112684734, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_12_81_flag endpoint_12_81_sources 11 167661679112684734 167661679112684734 rfl endpoint_12_81_base endpoint_12_81_p11) (by decide)⟩
private def endpoint_12_82_flag : Flag := ⟨12, 82, 1268⟩
private def endpoint_12_82_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_12_82_base : receiptBase endpoint_12_82_flag endpoint_12_82_sources = some 157464106442532133 := by decide +kernel
private theorem endpoint_12_82_w0 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 2 157464106442532133 = some 157464106442532133 := by decide +kernel
private theorem endpoint_12_82_w2 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 2 2 157464106442532133 = some 157464106442532133 := by decide +kernel
private theorem endpoint_12_82_p4 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 4 157464106442532133 = some 157464106442532133 :=
  join_receipt_window endpoint_12_82_flag endpoint_12_82_sources 0 2 2 157464106442532133 157464106442532133 157464106442532133 endpoint_12_82_w0 endpoint_12_82_w2
private theorem endpoint_12_82_w4 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 4 2 157464106442532133 = some 157464106442532133 := by decide +kernel
private theorem endpoint_12_82_p6 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 6 157464106442532133 = some 157464106442532133 :=
  join_receipt_window endpoint_12_82_flag endpoint_12_82_sources 0 4 2 157464106442532133 157464106442532133 157464106442532133 endpoint_12_82_p4 endpoint_12_82_w4
private theorem endpoint_12_82_w6 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 6 2 157464106442532133 = some 157464106442532133 := by decide +kernel
private theorem endpoint_12_82_p8 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 8 157464106442532133 = some 157464106442532133 :=
  join_receipt_window endpoint_12_82_flag endpoint_12_82_sources 0 6 2 157464106442532133 157464106442532133 157464106442532133 endpoint_12_82_p6 endpoint_12_82_w6
private theorem endpoint_12_82_w8 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 8 2 157464106442532133 = some 157464106442532133 := by decide +kernel
private theorem endpoint_12_82_p10 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 10 157464106442532133 = some 157464106442532133 :=
  join_receipt_window endpoint_12_82_flag endpoint_12_82_sources 0 8 2 157464106442532133 157464106442532133 157464106442532133 endpoint_12_82_p8 endpoint_12_82_w8
private theorem endpoint_12_82_w10 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 10 1 157464106442532133 = some 157464106442532133 := by decide +kernel
private theorem endpoint_12_82_p11 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 11 157464106442532133 = some 157464106442532133 :=
  join_receipt_window endpoint_12_82_flag endpoint_12_82_sources 0 10 1 157464106442532133 157464106442532133 157464106442532133 endpoint_12_82_p10 endpoint_12_82_w10
def endpoint_12_82 : CertifiedEndpoint :=
  ⟨⟨12, 82, 1268⟩, 157464106442532133, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_12_82_flag endpoint_12_82_sources 11 157464106442532133 157464106442532133 rfl endpoint_12_82_base endpoint_12_82_p11) (by decide)⟩
def endpoint_12_83 : CertifiedEndpoint :=
  ⟨⟨12, 83, 1167⟩, 255195414935705936, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_84 : CertifiedEndpoint :=
  ⟨⟨12, 84, 1063⟩, 234459022787805157, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_85 : CertifiedEndpoint :=
  ⟨⟨12, 85, 956⟩, 212401465564523129, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_86 : CertifiedEndpoint :=
  ⟨⟨12, 86, 847⟩, 189232291403289301, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_87 : CertifiedEndpoint :=
  ⟨⟨12, 87, 736⟩, 164933667153981109, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_88 : CertifiedEndpoint :=
  ⟨⟨12, 88, 621⟩, 139003275174501023, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_89 : CertifiedEndpoint :=
  ⟨⟨12, 89, 504⟩, 111895878039953069, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_90 : CertifiedEndpoint :=
  ⟨⟨12, 90, 384⟩, 83345455970853012, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_91 : CertifiedEndpoint :=
  ⟨⟨12, 91, 262⟩, 53576418063065771, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_92 : CertifiedEndpoint :=
  ⟨⟨12, 92, 137⟩, 22316800153732923, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_13 : CertifiedEndpoint :=
  ⟨⟨13, 13, 4049⟩, 95869968833710950, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_14 : CertifiedEndpoint :=
  ⟨⟨13, 14, 4029⟩, 99636423243374548, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_15 : CertifiedEndpoint :=
  ⟨⟨13, 15, 4009⟩, 103360614107913066, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_16 : CertifiedEndpoint :=
  ⟨⟨13, 16, 3988⟩, 115648572349646128, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_17 : CertifiedEndpoint :=
  ⟨⟨13, 17, 3968⟩, 127829952649147167, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_18 : CertifiedEndpoint :=
  ⟨⟨13, 18, 3947⟩, 139843369729490819, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_19 : CertifiedEndpoint :=
  ⟨⟨13, 19, 3926⟩, 151717901281131593, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_20 : CertifiedEndpoint :=
  ⟨⟨13, 20, 3904⟩, 163411550029549596, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_21 : CertifiedEndpoint :=
  ⟨⟨13, 21, 3883⟩, 175005080627768268, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_22 : CertifiedEndpoint :=
  ⟨⟨13, 22, 3861⟩, 186411268630731477, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_23 : CertifiedEndpoint :=
  ⟨⟨13, 23, 3839⟩, 197672111312959116, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_24 : CertifiedEndpoint :=
  ⟨⟨13, 24, 3817⟩, 208787608674451185, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_25 : CertifiedEndpoint :=
  ⟨⟨13, 25, 3794⟩, 219699613960606061, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_26 : CertifiedEndpoint :=
  ⟨⟨13, 26, 3771⟩, 230459814133992675, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_27 : CertifiedEndpoint :=
  ⟨⟨13, 27, 3748⟩, 241068209194611027, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_28 : CertifiedEndpoint :=
  ⟨⟨13, 28, 3725⟩, 251524799142461117, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_13_29_flag : Flag := ⟨13, 29, 3701⟩
private def endpoint_13_29_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_29_base : receiptBase endpoint_13_29_flag endpoint_13_29_sources = some 175928064504167445 := by decide +kernel
private theorem endpoint_13_29_w0 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 2 175928064504167445 = some 175928064504167445 := by decide +kernel
private theorem endpoint_13_29_w2 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 2 2 175928064504167445 = some 175928064504167445 := by decide +kernel
private theorem endpoint_13_29_p4 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 4 175928064504167445 = some 175928064504167445 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 2 2 175928064504167445 175928064504167445 175928064504167445 endpoint_13_29_w0 endpoint_13_29_w2
private theorem endpoint_13_29_w4 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 4 2 175928064504167445 = some 175928064504167445 := by decide +kernel
private theorem endpoint_13_29_p6 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 6 175928064504167445 = some 175928064504167445 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 4 2 175928064504167445 175928064504167445 175928064504167445 endpoint_13_29_p4 endpoint_13_29_w4
private theorem endpoint_13_29_w6 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 6 2 175928064504167445 = some 175928064504167445 := by decide +kernel
private theorem endpoint_13_29_p8 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 8 175928064504167445 = some 175928064504167445 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 6 2 175928064504167445 175928064504167445 175928064504167445 endpoint_13_29_p6 endpoint_13_29_w6
private theorem endpoint_13_29_w8 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 8 2 175928064504167445 = some 175928064504167445 := by decide +kernel
private theorem endpoint_13_29_p10 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 10 175928064504167445 = some 175928064504167445 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 8 2 175928064504167445 175928064504167445 175928064504167445 endpoint_13_29_p8 endpoint_13_29_w8
private theorem endpoint_13_29_w10 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 10 2 175928064504167445 = some 175928064504167445 := by decide +kernel
private theorem endpoint_13_29_p12 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 12 175928064504167445 = some 175928064504167445 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 10 2 175928064504167445 175928064504167445 175928064504167445 endpoint_13_29_p10 endpoint_13_29_w10
def endpoint_13_29 : CertifiedEndpoint :=
  ⟨⟨13, 29, 3701⟩, 175928064504167445, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_29_flag endpoint_13_29_sources 12 175928064504167445 175928064504167445 rfl endpoint_13_29_base endpoint_13_29_p12) (by decide)⟩
private def endpoint_13_30_flag : Flag := ⟨13, 30, 3677⟩
private def endpoint_13_30_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_30_base : receiptBase endpoint_13_30_flag endpoint_13_30_sources = some 179714506304109280 := by decide +kernel
private theorem endpoint_13_30_w0 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 2 179714506304109280 = some 179714506304109280 := by decide +kernel
private theorem endpoint_13_30_w2 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 2 2 179714506304109280 = some 179714506304109280 := by decide +kernel
private theorem endpoint_13_30_p4 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 4 179714506304109280 = some 179714506304109280 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 2 2 179714506304109280 179714506304109280 179714506304109280 endpoint_13_30_w0 endpoint_13_30_w2
private theorem endpoint_13_30_w4 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 4 2 179714506304109280 = some 179714506304109280 := by decide +kernel
private theorem endpoint_13_30_p6 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 6 179714506304109280 = some 179714506304109280 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 4 2 179714506304109280 179714506304109280 179714506304109280 endpoint_13_30_p4 endpoint_13_30_w4
private theorem endpoint_13_30_w6 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 6 2 179714506304109280 = some 179714506304109280 := by decide +kernel
private theorem endpoint_13_30_p8 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 8 179714506304109280 = some 179714506304109280 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 6 2 179714506304109280 179714506304109280 179714506304109280 endpoint_13_30_p6 endpoint_13_30_w6
private theorem endpoint_13_30_w8 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 8 2 179714506304109280 = some 179714506304109280 := by decide +kernel
private theorem endpoint_13_30_p10 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 10 179714506304109280 = some 179714506304109280 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 8 2 179714506304109280 179714506304109280 179714506304109280 endpoint_13_30_p8 endpoint_13_30_w8
private theorem endpoint_13_30_w10 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 10 2 179714506304109280 = some 179714506304109280 := by decide +kernel
private theorem endpoint_13_30_p12 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 12 179714506304109280 = some 179714506304109280 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 10 2 179714506304109280 179714506304109280 179714506304109280 endpoint_13_30_p10 endpoint_13_30_w10
def endpoint_13_30 : CertifiedEndpoint :=
  ⟨⟨13, 30, 3677⟩, 179714506304109280, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_30_flag endpoint_13_30_sources 12 179714506304109280 179714506304109280 rfl endpoint_13_30_base endpoint_13_30_p12) (by decide)⟩
private def endpoint_13_31_flag : Flag := ⟨13, 31, 3653⟩
private def endpoint_13_31_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_31_base : receiptBase endpoint_13_31_flag endpoint_13_31_sources = some 183436951536064825 := by decide +kernel
private theorem endpoint_13_31_w0 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 2 183436951536064825 = some 183436951536064825 := by decide +kernel
private theorem endpoint_13_31_w2 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 2 2 183436951536064825 = some 183436951536064825 := by decide +kernel
private theorem endpoint_13_31_p4 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 4 183436951536064825 = some 183436951536064825 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 2 2 183436951536064825 183436951536064825 183436951536064825 endpoint_13_31_w0 endpoint_13_31_w2
private theorem endpoint_13_31_w4 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 4 2 183436951536064825 = some 183436951536064825 := by decide +kernel
private theorem endpoint_13_31_p6 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 6 183436951536064825 = some 183436951536064825 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 4 2 183436951536064825 183436951536064825 183436951536064825 endpoint_13_31_p4 endpoint_13_31_w4
private theorem endpoint_13_31_w6 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 6 2 183436951536064825 = some 183436951536064825 := by decide +kernel
private theorem endpoint_13_31_p8 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 8 183436951536064825 = some 183436951536064825 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 6 2 183436951536064825 183436951536064825 183436951536064825 endpoint_13_31_p6 endpoint_13_31_w6
private theorem endpoint_13_31_w8 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 8 2 183436951536064825 = some 183436951536064825 := by decide +kernel
private theorem endpoint_13_31_p10 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 10 183436951536064825 = some 183436951536064825 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 8 2 183436951536064825 183436951536064825 183436951536064825 endpoint_13_31_p8 endpoint_13_31_w8
private theorem endpoint_13_31_w10 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 10 2 183436951536064825 = some 183436951536064825 := by decide +kernel
private theorem endpoint_13_31_p12 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 12 183436951536064825 = some 183436951536064825 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 10 2 183436951536064825 183436951536064825 183436951536064825 endpoint_13_31_p10 endpoint_13_31_w10
def endpoint_13_31 : CertifiedEndpoint :=
  ⟨⟨13, 31, 3653⟩, 183436951536064825, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_31_flag endpoint_13_31_sources 12 183436951536064825 183436951536064825 rfl endpoint_13_31_base endpoint_13_31_p12) (by decide)⟩

def endpointBlock08 : List CertifiedEndpoint := [
  endpoint_11_67, endpoint_11_68, endpoint_11_69, endpoint_11_70, endpoint_11_71, endpoint_11_72, endpoint_11_73,
  endpoint_11_74, endpoint_11_75, endpoint_11_76, endpoint_11_77, endpoint_11_78, endpoint_11_79, endpoint_11_80,
  endpoint_11_81, endpoint_11_82, endpoint_11_83, endpoint_11_84, endpoint_11_85, endpoint_11_86, endpoint_11_87,
  endpoint_11_88, endpoint_11_89, endpoint_11_90, endpoint_11_91, endpoint_11_92, endpoint_11_93, endpoint_12_12,
  endpoint_12_13, endpoint_12_14, endpoint_12_15, endpoint_12_16, endpoint_12_17, endpoint_12_18, endpoint_12_19,
  endpoint_12_20, endpoint_12_21, endpoint_12_22, endpoint_12_23, endpoint_12_24, endpoint_12_25, endpoint_12_26,
  endpoint_12_27, endpoint_12_28, endpoint_12_29, endpoint_12_30, endpoint_12_31, endpoint_12_32, endpoint_12_33,
  endpoint_12_34, endpoint_12_35, endpoint_12_36, endpoint_12_37, endpoint_12_38, endpoint_12_39, endpoint_12_40,
  endpoint_12_41, endpoint_12_42, endpoint_12_43, endpoint_12_44, endpoint_12_45, endpoint_12_46, endpoint_12_47,
  endpoint_12_48, endpoint_12_49, endpoint_12_50, endpoint_12_51, endpoint_12_52, endpoint_12_53, endpoint_12_54,
  endpoint_12_55, endpoint_12_56, endpoint_12_57, endpoint_12_58, endpoint_12_59, endpoint_12_60, endpoint_12_61,
  endpoint_12_62, endpoint_12_63, endpoint_12_64, endpoint_12_65, endpoint_12_66, endpoint_12_67, endpoint_12_68,
  endpoint_12_69, endpoint_12_70, endpoint_12_71, endpoint_12_72, endpoint_12_73, endpoint_12_74, endpoint_12_75,
  endpoint_12_76, endpoint_12_77, endpoint_12_78, endpoint_12_79, endpoint_12_80, endpoint_12_81, endpoint_12_82,
  endpoint_12_83, endpoint_12_84, endpoint_12_85, endpoint_12_86, endpoint_12_87, endpoint_12_88, endpoint_12_89,
  endpoint_12_90, endpoint_12_91, endpoint_12_92, endpoint_13_13, endpoint_13_14, endpoint_13_15, endpoint_13_16,
  endpoint_13_17, endpoint_13_18, endpoint_13_19, endpoint_13_20, endpoint_13_21, endpoint_13_22, endpoint_13_23,
  endpoint_13_24, endpoint_13_25, endpoint_13_26, endpoint_13_27, endpoint_13_28, endpoint_13_29, endpoint_13_30,
  endpoint_13_31
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
