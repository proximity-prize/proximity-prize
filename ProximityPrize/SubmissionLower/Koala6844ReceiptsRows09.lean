import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def endpoint_13_24 : CertifiedEndpoint :=
  ⟨⟨13, 24, 4295⟩, 235037867078213591, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_25 : CertifiedEndpoint :=
  ⟨⟨13, 25, 4268⟩, 247261175641775363, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_26 : CertifiedEndpoint :=
  ⟨⟨13, 26, 4242⟩, 259368216575056074, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_13_27_flag : Flag := ⟨13, 27, 4215⟩
private def endpoint_13_27_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_27_base : receiptBase endpoint_13_27_flag endpoint_13_27_sources = some 188818851240820198 := by decide +kernel
private theorem endpoint_13_27_w0 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 0 2 188818851240820198 = some 188818851240820198 := by decide +kernel
private theorem endpoint_13_27_w2 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 2 2 188818851240820198 = some 188818851240820198 := by decide +kernel
private theorem endpoint_13_27_p4 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 0 4 188818851240820198 = some 188818851240820198 :=
  join_receipt_window endpoint_13_27_flag endpoint_13_27_sources 0 2 2 188818851240820198 188818851240820198 188818851240820198 endpoint_13_27_w0 endpoint_13_27_w2
private theorem endpoint_13_27_w4 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 4 2 188818851240820198 = some 188818851240820198 := by decide +kernel
private theorem endpoint_13_27_p6 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 0 6 188818851240820198 = some 188818851240820198 :=
  join_receipt_window endpoint_13_27_flag endpoint_13_27_sources 0 4 2 188818851240820198 188818851240820198 188818851240820198 endpoint_13_27_p4 endpoint_13_27_w4
private theorem endpoint_13_27_w6 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 6 2 188818851240820198 = some 188818851240820198 := by decide +kernel
private theorem endpoint_13_27_p8 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 0 8 188818851240820198 = some 188818851240820198 :=
  join_receipt_window endpoint_13_27_flag endpoint_13_27_sources 0 6 2 188818851240820198 188818851240820198 188818851240820198 endpoint_13_27_p6 endpoint_13_27_w6
private theorem endpoint_13_27_w8 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 8 2 188818851240820198 = some 188818851240820198 := by decide +kernel
private theorem endpoint_13_27_p10 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 0 10 188818851240820198 = some 188818851240820198 :=
  join_receipt_window endpoint_13_27_flag endpoint_13_27_sources 0 8 2 188818851240820198 188818851240820198 188818851240820198 endpoint_13_27_p8 endpoint_13_27_w8
private theorem endpoint_13_27_w10 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 10 2 188818851240820198 = some 188818851240820198 := by decide +kernel
private theorem endpoint_13_27_p12 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 0 12 188818851240820198 = some 188818851240820198 :=
  join_receipt_window endpoint_13_27_flag endpoint_13_27_sources 0 10 2 188818851240820198 188818851240820198 188818851240820198 endpoint_13_27_p10 endpoint_13_27_w10
def endpoint_13_27 : CertifiedEndpoint :=
  ⟨⟨13, 27, 4215⟩, 188818851240820198, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_27_flag endpoint_13_27_sources 12 188818851240820198 188818851240820198 rfl endpoint_13_27_base endpoint_13_27_p12) (by decide)⟩
private def endpoint_13_28_flag : Flag := ⟨13, 28, 4188⟩
private def endpoint_13_28_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_28_base : receiptBase endpoint_13_28_flag endpoint_13_28_sources = some 193207572855438822 := by decide +kernel
private theorem endpoint_13_28_w0 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 0 2 193207572855438822 = some 193207572855438822 := by decide +kernel
private theorem endpoint_13_28_w2 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 2 2 193207572855438822 = some 193207572855438822 := by decide +kernel
private theorem endpoint_13_28_p4 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 0 4 193207572855438822 = some 193207572855438822 :=
  join_receipt_window endpoint_13_28_flag endpoint_13_28_sources 0 2 2 193207572855438822 193207572855438822 193207572855438822 endpoint_13_28_w0 endpoint_13_28_w2
private theorem endpoint_13_28_w4 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 4 2 193207572855438822 = some 193207572855438822 := by decide +kernel
private theorem endpoint_13_28_p6 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 0 6 193207572855438822 = some 193207572855438822 :=
  join_receipt_window endpoint_13_28_flag endpoint_13_28_sources 0 4 2 193207572855438822 193207572855438822 193207572855438822 endpoint_13_28_p4 endpoint_13_28_w4
private theorem endpoint_13_28_w6 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 6 2 193207572855438822 = some 193207572855438822 := by decide +kernel
private theorem endpoint_13_28_p8 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 0 8 193207572855438822 = some 193207572855438822 :=
  join_receipt_window endpoint_13_28_flag endpoint_13_28_sources 0 6 2 193207572855438822 193207572855438822 193207572855438822 endpoint_13_28_p6 endpoint_13_28_w6
private theorem endpoint_13_28_w8 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 8 2 193207572855438822 = some 193207572855438822 := by decide +kernel
private theorem endpoint_13_28_p10 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 0 10 193207572855438822 = some 193207572855438822 :=
  join_receipt_window endpoint_13_28_flag endpoint_13_28_sources 0 8 2 193207572855438822 193207572855438822 193207572855438822 endpoint_13_28_p8 endpoint_13_28_w8
private theorem endpoint_13_28_w10 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 10 2 193207572855438822 = some 193207572855438822 := by decide +kernel
private theorem endpoint_13_28_p12 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 0 12 193207572855438822 = some 193207572855438822 :=
  join_receipt_window endpoint_13_28_flag endpoint_13_28_sources 0 10 2 193207572855438822 193207572855438822 193207572855438822 endpoint_13_28_p10 endpoint_13_28_w10
def endpoint_13_28 : CertifiedEndpoint :=
  ⟨⟨13, 28, 4188⟩, 193207572855438822, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_28_flag endpoint_13_28_sources 12 193207572855438822 193207572855438822 rfl endpoint_13_28_base endpoint_13_28_p12) (by decide)⟩
private def endpoint_13_29_flag : Flag := ⟨13, 29, 4161⟩
private def endpoint_13_29_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_29_base : receiptBase endpoint_13_29_flag endpoint_13_29_sources = some 197524464066863007 := by decide +kernel
private theorem endpoint_13_29_w0 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 2 197524464066863007 = some 197524464066863007 := by decide +kernel
private theorem endpoint_13_29_w2 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 2 2 197524464066863007 = some 197524464066863007 := by decide +kernel
private theorem endpoint_13_29_p4 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 4 197524464066863007 = some 197524464066863007 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 2 2 197524464066863007 197524464066863007 197524464066863007 endpoint_13_29_w0 endpoint_13_29_w2
private theorem endpoint_13_29_w4 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 4 2 197524464066863007 = some 197524464066863007 := by decide +kernel
private theorem endpoint_13_29_p6 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 6 197524464066863007 = some 197524464066863007 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 4 2 197524464066863007 197524464066863007 197524464066863007 endpoint_13_29_p4 endpoint_13_29_w4
private theorem endpoint_13_29_w6 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 6 2 197524464066863007 = some 197524464066863007 := by decide +kernel
private theorem endpoint_13_29_p8 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 8 197524464066863007 = some 197524464066863007 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 6 2 197524464066863007 197524464066863007 197524464066863007 endpoint_13_29_p6 endpoint_13_29_w6
private theorem endpoint_13_29_w8 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 8 2 197524464066863007 = some 197524464066863007 := by decide +kernel
private theorem endpoint_13_29_p10 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 10 197524464066863007 = some 197524464066863007 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 8 2 197524464066863007 197524464066863007 197524464066863007 endpoint_13_29_p8 endpoint_13_29_w8
private theorem endpoint_13_29_w10 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 10 2 197524464066863007 = some 197524464066863007 := by decide +kernel
private theorem endpoint_13_29_p12 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 12 197524464066863007 = some 197524464066863007 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 10 2 197524464066863007 197524464066863007 197524464066863007 endpoint_13_29_p10 endpoint_13_29_w10
def endpoint_13_29 : CertifiedEndpoint :=
  ⟨⟨13, 29, 4161⟩, 197524464066863007, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_29_flag endpoint_13_29_sources 12 197524464066863007 197524464066863007 rfl endpoint_13_29_base endpoint_13_29_p12) (by decide)⟩
private def endpoint_13_30_flag : Flag := ⟨13, 30, 4133⟩
private def endpoint_13_30_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_30_base : receiptBase endpoint_13_30_flag endpoint_13_30_sources = some 201721387515516845 := by decide +kernel
private theorem endpoint_13_30_w0 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 2 201721387515516845 = some 201721387515516845 := by decide +kernel
private theorem endpoint_13_30_w2 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 2 2 201721387515516845 = some 201721387515516845 := by decide +kernel
private theorem endpoint_13_30_p4 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 4 201721387515516845 = some 201721387515516845 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 2 2 201721387515516845 201721387515516845 201721387515516845 endpoint_13_30_w0 endpoint_13_30_w2
private theorem endpoint_13_30_w4 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 4 2 201721387515516845 = some 201721387515516845 := by decide +kernel
private theorem endpoint_13_30_p6 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 6 201721387515516845 = some 201721387515516845 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 4 2 201721387515516845 201721387515516845 201721387515516845 endpoint_13_30_p4 endpoint_13_30_w4
private theorem endpoint_13_30_w6 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 6 2 201721387515516845 = some 201721387515516845 := by decide +kernel
private theorem endpoint_13_30_p8 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 8 201721387515516845 = some 201721387515516845 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 6 2 201721387515516845 201721387515516845 201721387515516845 endpoint_13_30_p6 endpoint_13_30_w6
private theorem endpoint_13_30_w8 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 8 2 201721387515516845 = some 201721387515516845 := by decide +kernel
private theorem endpoint_13_30_p10 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 10 201721387515516845 = some 201721387515516845 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 8 2 201721387515516845 201721387515516845 201721387515516845 endpoint_13_30_p8 endpoint_13_30_w8
private theorem endpoint_13_30_w10 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 10 2 201721387515516845 = some 201721387515516845 := by decide +kernel
private theorem endpoint_13_30_p12 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 12 201721387515516845 = some 201721387515516845 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 10 2 201721387515516845 201721387515516845 201721387515516845 endpoint_13_30_p10 endpoint_13_30_w10
def endpoint_13_30 : CertifiedEndpoint :=
  ⟨⟨13, 30, 4133⟩, 201721387515516845, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_30_flag endpoint_13_30_sources 12 201721387515516845 201721387515516845 rfl endpoint_13_30_base endpoint_13_30_p12) (by decide)⟩
private def endpoint_13_31_flag : Flag := ⟨13, 31, 4104⟩
private def endpoint_13_31_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_31_base : receiptBase endpoint_13_31_flag endpoint_13_31_sources = some 205794426283856416 := by decide +kernel
private theorem endpoint_13_31_w0 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 2 205794426283856416 = some 205794426283856416 := by decide +kernel
private theorem endpoint_13_31_w2 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 2 2 205794426283856416 = some 205794426283856416 := by decide +kernel
private theorem endpoint_13_31_p4 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 4 205794426283856416 = some 205794426283856416 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 2 2 205794426283856416 205794426283856416 205794426283856416 endpoint_13_31_w0 endpoint_13_31_w2
private theorem endpoint_13_31_w4 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 4 2 205794426283856416 = some 205794426283856416 := by decide +kernel
private theorem endpoint_13_31_p6 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 6 205794426283856416 = some 205794426283856416 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 4 2 205794426283856416 205794426283856416 205794426283856416 endpoint_13_31_p4 endpoint_13_31_w4
private theorem endpoint_13_31_w6 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 6 2 205794426283856416 = some 205794426283856416 := by decide +kernel
private theorem endpoint_13_31_p8 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 8 205794426283856416 = some 205794426283856416 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 6 2 205794426283856416 205794426283856416 205794426283856416 endpoint_13_31_p6 endpoint_13_31_w6
private theorem endpoint_13_31_w8 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 8 2 205794426283856416 = some 205794426283856416 := by decide +kernel
private theorem endpoint_13_31_p10 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 10 205794426283856416 = some 205794426283856416 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 8 2 205794426283856416 205794426283856416 205794426283856416 endpoint_13_31_p8 endpoint_13_31_w8
private theorem endpoint_13_31_w10 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 10 2 205794426283856416 = some 205794426283856416 := by decide +kernel
private theorem endpoint_13_31_p12 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 12 205794426283856416 = some 205794426283856416 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 10 2 205794426283856416 205794426283856416 205794426283856416 endpoint_13_31_p10 endpoint_13_31_w10
def endpoint_13_31 : CertifiedEndpoint :=
  ⟨⟨13, 31, 4104⟩, 205794426283856416, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_31_flag endpoint_13_31_sources 12 205794426283856416 205794426283856416 rfl endpoint_13_31_base endpoint_13_31_p12) (by decide)⟩
private def endpoint_13_32_flag : Flag := ⟨13, 32, 4076⟩
private def endpoint_13_32_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_32_base : receiptBase endpoint_13_32_flag endpoint_13_32_sources = some 209841160730214843 := by decide +kernel
private theorem endpoint_13_32_w0 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 2 209841160730214843 = some 209841160730214843 := by decide +kernel
private theorem endpoint_13_32_w2 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 2 2 209841160730214843 = some 209841160730214843 := by decide +kernel
private theorem endpoint_13_32_p4 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 4 209841160730214843 = some 209841160730214843 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 2 2 209841160730214843 209841160730214843 209841160730214843 endpoint_13_32_w0 endpoint_13_32_w2
private theorem endpoint_13_32_w4 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 4 2 209841160730214843 = some 209841160730214843 := by decide +kernel
private theorem endpoint_13_32_p6 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 6 209841160730214843 = some 209841160730214843 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 4 2 209841160730214843 209841160730214843 209841160730214843 endpoint_13_32_p4 endpoint_13_32_w4
private theorem endpoint_13_32_w6 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 6 2 209841160730214843 = some 209841160730214843 := by decide +kernel
private theorem endpoint_13_32_p8 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 8 209841160730214843 = some 209841160730214843 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 6 2 209841160730214843 209841160730214843 209841160730214843 endpoint_13_32_p6 endpoint_13_32_w6
private theorem endpoint_13_32_w8 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 8 2 209841160730214843 = some 209841160730214843 := by decide +kernel
private theorem endpoint_13_32_p10 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 10 209841160730214843 = some 209841160730214843 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 8 2 209841160730214843 209841160730214843 209841160730214843 endpoint_13_32_p8 endpoint_13_32_w8
private theorem endpoint_13_32_w10 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 10 2 209841160730214843 = some 209841160730214843 := by decide +kernel
private theorem endpoint_13_32_p12 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 12 209841160730214843 = some 209841160730214843 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 10 2 209841160730214843 209841160730214843 209841160730214843 endpoint_13_32_p10 endpoint_13_32_w10
def endpoint_13_32 : CertifiedEndpoint :=
  ⟨⟨13, 32, 4076⟩, 209841160730214843, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_32_flag endpoint_13_32_sources 12 209841160730214843 209841160730214843 rfl endpoint_13_32_base endpoint_13_32_p12) (by decide)⟩
private def endpoint_13_33_flag : Flag := ⟨13, 33, 4047⟩
private def endpoint_13_33_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_33_base : receiptBase endpoint_13_33_flag endpoint_13_33_sources = some 213761399217896390 := by decide +kernel
private theorem endpoint_13_33_w0 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 2 213761399217896390 = some 213761399217896390 := by decide +kernel
private theorem endpoint_13_33_w2 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 2 2 213761399217896390 = some 213761399217896390 := by decide +kernel
private theorem endpoint_13_33_p4 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 4 213761399217896390 = some 213761399217896390 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 2 2 213761399217896390 213761399217896390 213761399217896390 endpoint_13_33_w0 endpoint_13_33_w2
private theorem endpoint_13_33_w4 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 4 2 213761399217896390 = some 213761399217896390 := by decide +kernel
private theorem endpoint_13_33_p6 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 6 213761399217896390 = some 213761399217896390 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 4 2 213761399217896390 213761399217896390 213761399217896390 endpoint_13_33_p4 endpoint_13_33_w4
private theorem endpoint_13_33_w6 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 6 2 213761399217896390 = some 213761399217896390 := by decide +kernel
private theorem endpoint_13_33_p8 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 8 213761399217896390 = some 213761399217896390 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 6 2 213761399217896390 213761399217896390 213761399217896390 endpoint_13_33_p6 endpoint_13_33_w6
private theorem endpoint_13_33_w8 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 8 2 213761399217896390 = some 213761399217896390 := by decide +kernel
private theorem endpoint_13_33_p10 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 10 213761399217896390 = some 213761399217896390 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 8 2 213761399217896390 213761399217896390 213761399217896390 endpoint_13_33_p8 endpoint_13_33_w8
private theorem endpoint_13_33_w10 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 10 2 213761399217896390 = some 213761399217896390 := by decide +kernel
private theorem endpoint_13_33_p12 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 12 213761399217896390 = some 213761399217896390 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 10 2 213761399217896390 213761399217896390 213761399217896390 endpoint_13_33_p10 endpoint_13_33_w10
def endpoint_13_33 : CertifiedEndpoint :=
  ⟨⟨13, 33, 4047⟩, 213761399217896390, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_33_flag endpoint_13_33_sources 12 213761399217896390 213761399217896390 rfl endpoint_13_33_base endpoint_13_33_p12) (by decide)⟩
private def endpoint_13_34_flag : Flag := ⟨13, 34, 4017⟩
private def endpoint_13_34_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_34_base : receiptBase endpoint_13_34_flag endpoint_13_34_sources = some 217551224829357137 := by decide +kernel
private theorem endpoint_13_34_w0 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 2 217551224829357137 = some 217551224829357137 := by decide +kernel
private theorem endpoint_13_34_w2 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 2 2 217551224829357137 = some 217551224829357137 := by decide +kernel
private theorem endpoint_13_34_p4 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 4 217551224829357137 = some 217551224829357137 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 2 2 217551224829357137 217551224829357137 217551224829357137 endpoint_13_34_w0 endpoint_13_34_w2
private theorem endpoint_13_34_w4 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 4 2 217551224829357137 = some 217551224829357137 := by decide +kernel
private theorem endpoint_13_34_p6 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 6 217551224829357137 = some 217551224829357137 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 4 2 217551224829357137 217551224829357137 217551224829357137 endpoint_13_34_p4 endpoint_13_34_w4
private theorem endpoint_13_34_w6 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 6 2 217551224829357137 = some 217551224829357137 := by decide +kernel
private theorem endpoint_13_34_p8 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 8 217551224829357137 = some 217551224829357137 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 6 2 217551224829357137 217551224829357137 217551224829357137 endpoint_13_34_p6 endpoint_13_34_w6
private theorem endpoint_13_34_w8 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 8 2 217551224829357137 = some 217551224829357137 := by decide +kernel
private theorem endpoint_13_34_p10 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 10 217551224829357137 = some 217551224829357137 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 8 2 217551224829357137 217551224829357137 217551224829357137 endpoint_13_34_p8 endpoint_13_34_w8
private theorem endpoint_13_34_w10 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 10 2 217551224829357137 = some 217551224829357137 := by decide +kernel
private theorem endpoint_13_34_p12 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 12 217551224829357137 = some 217551224829357137 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 10 2 217551224829357137 217551224829357137 217551224829357137 endpoint_13_34_p10 endpoint_13_34_w10
def endpoint_13_34 : CertifiedEndpoint :=
  ⟨⟨13, 34, 4017⟩, 217551224829357137, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_34_flag endpoint_13_34_sources 12 217551224829357137 217551224829357137 rfl endpoint_13_34_base endpoint_13_34_p12) (by decide)⟩
private def endpoint_13_35_flag : Flag := ⟨13, 35, 3987⟩
private def endpoint_13_35_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_35_base : receiptBase endpoint_13_35_flag endpoint_13_35_sources = some 221949990725790489 := by decide +kernel
private theorem endpoint_13_35_w0 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 2 221949990725790489 = some 221949990725790489 := by decide +kernel
private theorem endpoint_13_35_w2 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 2 2 221949990725790489 = some 221949990725790489 := by decide +kernel
private theorem endpoint_13_35_p4 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 4 221949990725790489 = some 221949990725790489 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 2 2 221949990725790489 221949990725790489 221949990725790489 endpoint_13_35_w0 endpoint_13_35_w2
private theorem endpoint_13_35_w4 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 4 2 221949990725790489 = some 221949990725790489 := by decide +kernel
private theorem endpoint_13_35_p6 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 6 221949990725790489 = some 221949990725790489 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 4 2 221949990725790489 221949990725790489 221949990725790489 endpoint_13_35_p4 endpoint_13_35_w4
private theorem endpoint_13_35_w6 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 6 2 221949990725790489 = some 221949990725790489 := by decide +kernel
private theorem endpoint_13_35_p8 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 8 221949990725790489 = some 221949990725790489 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 6 2 221949990725790489 221949990725790489 221949990725790489 endpoint_13_35_p6 endpoint_13_35_w6
private theorem endpoint_13_35_w8 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 8 2 221949990725790489 = some 221949990725790489 := by decide +kernel
private theorem endpoint_13_35_p10 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 10 221949990725790489 = some 221949990725790489 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 8 2 221949990725790489 221949990725790489 221949990725790489 endpoint_13_35_p8 endpoint_13_35_w8
private theorem endpoint_13_35_w10 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 10 2 221949990725790489 = some 221949990725790489 := by decide +kernel
private theorem endpoint_13_35_p12 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 12 221949990725790489 = some 221949990725790489 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 10 2 221949990725790489 221949990725790489 221949990725790489 endpoint_13_35_p10 endpoint_13_35_w10
def endpoint_13_35 : CertifiedEndpoint :=
  ⟨⟨13, 35, 3987⟩, 221949990725790489, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_35_flag endpoint_13_35_sources 12 221949990725790489 221949990725790489 rfl endpoint_13_35_base endpoint_13_35_p12) (by decide)⟩
private def endpoint_13_36_flag : Flag := ⟨13, 36, 3956⟩
private def endpoint_13_36_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_36_base : receiptBase endpoint_13_36_flag endpoint_13_36_sources = some 225427203483383768 := by decide +kernel
private theorem endpoint_13_36_w0 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 2 225427203483383768 = some 225427203483383768 := by decide +kernel
private theorem endpoint_13_36_w2 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 2 2 225427203483383768 = some 225427203483383768 := by decide +kernel
private theorem endpoint_13_36_p4 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 4 225427203483383768 = some 225427203483383768 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 2 2 225427203483383768 225427203483383768 225427203483383768 endpoint_13_36_w0 endpoint_13_36_w2
private theorem endpoint_13_36_w4 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 4 2 225427203483383768 = some 225427203483383768 := by decide +kernel
private theorem endpoint_13_36_p6 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 6 225427203483383768 = some 225427203483383768 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 4 2 225427203483383768 225427203483383768 225427203483383768 endpoint_13_36_p4 endpoint_13_36_w4
private theorem endpoint_13_36_w6 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 6 2 225427203483383768 = some 225427203483383768 := by decide +kernel
private theorem endpoint_13_36_p8 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 8 225427203483383768 = some 225427203483383768 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 6 2 225427203483383768 225427203483383768 225427203483383768 endpoint_13_36_p6 endpoint_13_36_w6
private theorem endpoint_13_36_w8 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 8 2 225427203483383768 = some 225427203483383768 := by decide +kernel
private theorem endpoint_13_36_p10 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 10 225427203483383768 = some 225427203483383768 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 8 2 225427203483383768 225427203483383768 225427203483383768 endpoint_13_36_p8 endpoint_13_36_w8
private theorem endpoint_13_36_w10 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 10 2 225427203483383768 = some 225427203483383768 := by decide +kernel
private theorem endpoint_13_36_p12 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 12 225427203483383768 = some 225427203483383768 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 10 2 225427203483383768 225427203483383768 225427203483383768 endpoint_13_36_p10 endpoint_13_36_w10
def endpoint_13_36 : CertifiedEndpoint :=
  ⟨⟨13, 36, 3956⟩, 225427203483383768, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_36_flag endpoint_13_36_sources 12 225427203483383768 225427203483383768 rfl endpoint_13_36_base endpoint_13_36_p12) (by decide)⟩
private def endpoint_13_37_flag : Flag := ⟨13, 37, 3925⟩
private def endpoint_13_37_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_37_base : receiptBase endpoint_13_37_flag endpoint_13_37_sources = some 228823436945519087 := by decide +kernel
private theorem endpoint_13_37_w0 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 2 228823436945519087 = some 228823436945519087 := by decide +kernel
private theorem endpoint_13_37_w2 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 2 2 228823436945519087 = some 228823436945519087 := by decide +kernel
private theorem endpoint_13_37_p4 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 4 228823436945519087 = some 228823436945519087 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 2 2 228823436945519087 228823436945519087 228823436945519087 endpoint_13_37_w0 endpoint_13_37_w2
private theorem endpoint_13_37_w4 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 4 2 228823436945519087 = some 228823436945519087 := by decide +kernel
private theorem endpoint_13_37_p6 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 6 228823436945519087 = some 228823436945519087 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 4 2 228823436945519087 228823436945519087 228823436945519087 endpoint_13_37_p4 endpoint_13_37_w4
private theorem endpoint_13_37_w6 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 6 2 228823436945519087 = some 228823436945519087 := by decide +kernel
private theorem endpoint_13_37_p8 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 8 228823436945519087 = some 228823436945519087 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 6 2 228823436945519087 228823436945519087 228823436945519087 endpoint_13_37_p6 endpoint_13_37_w6
private theorem endpoint_13_37_w8 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 8 2 228823436945519087 = some 228823436945519087 := by decide +kernel
private theorem endpoint_13_37_p10 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 10 228823436945519087 = some 228823436945519087 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 8 2 228823436945519087 228823436945519087 228823436945519087 endpoint_13_37_p8 endpoint_13_37_w8
private theorem endpoint_13_37_w10 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 10 2 228823436945519087 = some 228823436945519087 := by decide +kernel
private theorem endpoint_13_37_p12 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 12 228823436945519087 = some 228823436945519087 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 10 2 228823436945519087 228823436945519087 228823436945519087 endpoint_13_37_p10 endpoint_13_37_w10
def endpoint_13_37 : CertifiedEndpoint :=
  ⟨⟨13, 37, 3925⟩, 228823436945519087, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_37_flag endpoint_13_37_sources 12 228823436945519087 228823436945519087 rfl endpoint_13_37_base endpoint_13_37_p12) (by decide)⟩
private def endpoint_13_38_flag : Flag := ⟨13, 38, 3894⟩
private def endpoint_13_38_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_38_base : receiptBase endpoint_13_38_flag endpoint_13_38_sources = some 232138691112196447 := by decide +kernel
private theorem endpoint_13_38_w0 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 2 232138691112196447 = some 232138691112196447 := by decide +kernel
private theorem endpoint_13_38_w2 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 2 2 232138691112196447 = some 232138691112196447 := by decide +kernel
private theorem endpoint_13_38_p4 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 4 232138691112196447 = some 232138691112196447 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 2 2 232138691112196447 232138691112196447 232138691112196447 endpoint_13_38_w0 endpoint_13_38_w2
private theorem endpoint_13_38_w4 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 4 2 232138691112196447 = some 232138691112196447 := by decide +kernel
private theorem endpoint_13_38_p6 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 6 232138691112196447 = some 232138691112196447 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 4 2 232138691112196447 232138691112196447 232138691112196447 endpoint_13_38_p4 endpoint_13_38_w4
private theorem endpoint_13_38_w6 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 6 2 232138691112196447 = some 232138691112196447 := by decide +kernel
private theorem endpoint_13_38_p8 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 8 232138691112196447 = some 232138691112196447 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 6 2 232138691112196447 232138691112196447 232138691112196447 endpoint_13_38_p6 endpoint_13_38_w6
private theorem endpoint_13_38_w8 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 8 2 232138691112196447 = some 232138691112196447 := by decide +kernel
private theorem endpoint_13_38_p10 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 10 232138691112196447 = some 232138691112196447 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 8 2 232138691112196447 232138691112196447 232138691112196447 endpoint_13_38_p8 endpoint_13_38_w8
private theorem endpoint_13_38_w10 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 10 2 232138691112196447 = some 232138691112196447 := by decide +kernel
private theorem endpoint_13_38_p12 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 12 232138691112196447 = some 232138691112196447 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 10 2 232138691112196447 232138691112196447 232138691112196447 endpoint_13_38_p10 endpoint_13_38_w10
def endpoint_13_38 : CertifiedEndpoint :=
  ⟨⟨13, 38, 3894⟩, 232138691112196447, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_38_flag endpoint_13_38_sources 12 232138691112196447 232138691112196447 rfl endpoint_13_38_base endpoint_13_38_p12) (by decide)⟩
private def endpoint_13_39_flag : Flag := ⟨13, 39, 3862⟩
private def endpoint_13_39_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_39_base : receiptBase endpoint_13_39_flag endpoint_13_39_sources = some 235312899468505845 := by decide +kernel
private theorem endpoint_13_39_w0 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 2 235312899468505845 = some 235312899468505845 := by decide +kernel
private theorem endpoint_13_39_w2 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 2 2 235312899468505845 = some 235312899468505845 := by decide +kernel
private theorem endpoint_13_39_p4 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 4 235312899468505845 = some 235312899468505845 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 2 2 235312899468505845 235312899468505845 235312899468505845 endpoint_13_39_w0 endpoint_13_39_w2
private theorem endpoint_13_39_w4 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 4 2 235312899468505845 = some 235312899468505845 := by decide +kernel
private theorem endpoint_13_39_p6 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 6 235312899468505845 = some 235312899468505845 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 4 2 235312899468505845 235312899468505845 235312899468505845 endpoint_13_39_p4 endpoint_13_39_w4
private theorem endpoint_13_39_w6 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 6 2 235312899468505845 = some 235312899468505845 := by decide +kernel
private theorem endpoint_13_39_p8 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 8 235312899468505845 = some 235312899468505845 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 6 2 235312899468505845 235312899468505845 235312899468505845 endpoint_13_39_p6 endpoint_13_39_w6
private theorem endpoint_13_39_w8 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 8 2 235312899468505845 = some 235312899468505845 := by decide +kernel
private theorem endpoint_13_39_p10 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 10 235312899468505845 = some 235312899468505845 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 8 2 235312899468505845 235312899468505845 235312899468505845 endpoint_13_39_p8 endpoint_13_39_w8
private theorem endpoint_13_39_w10 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 10 2 235312899468505845 = some 235312899468505845 := by decide +kernel
private theorem endpoint_13_39_p12 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 12 235312899468505845 = some 235312899468505845 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 10 2 235312899468505845 235312899468505845 235312899468505845 endpoint_13_39_p10 endpoint_13_39_w10
def endpoint_13_39 : CertifiedEndpoint :=
  ⟨⟨13, 39, 3862⟩, 235312899468505845, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_39_flag endpoint_13_39_sources 12 235312899468505845 235312899468505845 rfl endpoint_13_39_base endpoint_13_39_p12) (by decide)⟩
private def endpoint_13_40_flag : Flag := ⟨13, 40, 3829⟩
private def endpoint_13_40_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_40_base : receiptBase endpoint_13_40_flag endpoint_13_40_sources = some 238802572215107212 := by decide +kernel
private theorem endpoint_13_40_w0 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 2 238802572215107212 = some 238802572215107212 := by decide +kernel
private theorem endpoint_13_40_w2 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 2 2 238802572215107212 = some 238802572215107212 := by decide +kernel
private theorem endpoint_13_40_p4 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 4 238802572215107212 = some 238802572215107212 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 2 2 238802572215107212 238802572215107212 238802572215107212 endpoint_13_40_w0 endpoint_13_40_w2
private theorem endpoint_13_40_w4 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 4 2 238802572215107212 = some 238802572215107212 := by decide +kernel
private theorem endpoint_13_40_p6 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 6 238802572215107212 = some 238802572215107212 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 4 2 238802572215107212 238802572215107212 238802572215107212 endpoint_13_40_p4 endpoint_13_40_w4
private theorem endpoint_13_40_w6 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 6 2 238802572215107212 = some 238802572215107212 := by decide +kernel
private theorem endpoint_13_40_p8 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 8 238802572215107212 = some 238802572215107212 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 6 2 238802572215107212 238802572215107212 238802572215107212 endpoint_13_40_p6 endpoint_13_40_w6
private theorem endpoint_13_40_w8 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 8 2 238802572215107212 = some 238802572215107212 := by decide +kernel
private theorem endpoint_13_40_p10 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 10 238802572215107212 = some 238802572215107212 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 8 2 238802572215107212 238802572215107212 238802572215107212 endpoint_13_40_p8 endpoint_13_40_w8
private theorem endpoint_13_40_w10 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 10 2 238802572215107212 = some 238802572215107212 := by decide +kernel
private theorem endpoint_13_40_p12 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 12 238802572215107212 = some 238802572215107212 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 10 2 238802572215107212 238802572215107212 238802572215107212 endpoint_13_40_p10 endpoint_13_40_w10
def endpoint_13_40 : CertifiedEndpoint :=
  ⟨⟨13, 40, 3829⟩, 238802572215107212, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_40_flag endpoint_13_40_sources 12 238802572215107212 238802572215107212 rfl endpoint_13_40_base endpoint_13_40_p12) (by decide)⟩
private def endpoint_13_41_flag : Flag := ⟨13, 41, 3796⟩
private def endpoint_13_41_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_41_base : receiptBase endpoint_13_41_flag endpoint_13_41_sources = some 241758524276893152 := by decide +kernel
private theorem endpoint_13_41_w0 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 2 241758524276893152 = some 241758524276893152 := by decide +kernel
private theorem endpoint_13_41_w2 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 2 2 241758524276893152 = some 241758524276893152 := by decide +kernel
private theorem endpoint_13_41_p4 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 4 241758524276893152 = some 241758524276893152 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 2 2 241758524276893152 241758524276893152 241758524276893152 endpoint_13_41_w0 endpoint_13_41_w2
private theorem endpoint_13_41_w4 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 4 2 241758524276893152 = some 241758524276893152 := by decide +kernel
private theorem endpoint_13_41_p6 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 6 241758524276893152 = some 241758524276893152 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 4 2 241758524276893152 241758524276893152 241758524276893152 endpoint_13_41_p4 endpoint_13_41_w4
private theorem endpoint_13_41_w6 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 6 2 241758524276893152 = some 241758524276893152 := by decide +kernel
private theorem endpoint_13_41_p8 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 8 241758524276893152 = some 241758524276893152 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 6 2 241758524276893152 241758524276893152 241758524276893152 endpoint_13_41_p6 endpoint_13_41_w6
private theorem endpoint_13_41_w8 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 8 2 241758524276893152 = some 241758524276893152 := by decide +kernel
private theorem endpoint_13_41_p10 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 10 241758524276893152 = some 241758524276893152 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 8 2 241758524276893152 241758524276893152 241758524276893152 endpoint_13_41_p8 endpoint_13_41_w8
private theorem endpoint_13_41_w10 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 10 2 241758524276893152 = some 241758524276893152 := by decide +kernel
private theorem endpoint_13_41_p12 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 12 241758524276893152 = some 241758524276893152 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 10 2 241758524276893152 241758524276893152 241758524276893152 endpoint_13_41_p10 endpoint_13_41_w10
def endpoint_13_41 : CertifiedEndpoint :=
  ⟨⟨13, 41, 3796⟩, 241758524276893152, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_41_flag endpoint_13_41_sources 12 241758524276893152 241758524276893152 rfl endpoint_13_41_base endpoint_13_41_p12) (by decide)⟩
private def endpoint_13_42_flag : Flag := ⟨13, 42, 3762⟩
private def endpoint_13_42_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_42_base : receiptBase endpoint_13_42_flag endpoint_13_42_sources = some 244563996294216604 := by decide +kernel
private theorem endpoint_13_42_w0 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 2 244563996294216604 = some 244563996294216604 := by decide +kernel
private theorem endpoint_13_42_w2 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 2 2 244563996294216604 = some 244563996294216604 := by decide +kernel
private theorem endpoint_13_42_p4 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 4 244563996294216604 = some 244563996294216604 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 2 2 244563996294216604 244563996294216604 244563996294216604 endpoint_13_42_w0 endpoint_13_42_w2
private theorem endpoint_13_42_w4 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 4 2 244563996294216604 = some 244563996294216604 := by decide +kernel
private theorem endpoint_13_42_p6 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 6 244563996294216604 = some 244563996294216604 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 4 2 244563996294216604 244563996294216604 244563996294216604 endpoint_13_42_p4 endpoint_13_42_w4
private theorem endpoint_13_42_w6 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 6 2 244563996294216604 = some 244563996294216604 := by decide +kernel
private theorem endpoint_13_42_p8 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 8 244563996294216604 = some 244563996294216604 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 6 2 244563996294216604 244563996294216604 244563996294216604 endpoint_13_42_p6 endpoint_13_42_w6
private theorem endpoint_13_42_w8 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 8 2 244563996294216604 = some 244563996294216604 := by decide +kernel
private theorem endpoint_13_42_p10 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 10 244563996294216604 = some 244563996294216604 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 8 2 244563996294216604 244563996294216604 244563996294216604 endpoint_13_42_p8 endpoint_13_42_w8
private theorem endpoint_13_42_w10 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 10 2 244563996294216604 = some 244563996294216604 := by decide +kernel
private theorem endpoint_13_42_p12 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 12 244563996294216604 = some 244563996294216604 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 10 2 244563996294216604 244563996294216604 244563996294216604 endpoint_13_42_p10 endpoint_13_42_w10
def endpoint_13_42 : CertifiedEndpoint :=
  ⟨⟨13, 42, 3762⟩, 244563996294216604, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_42_flag endpoint_13_42_sources 12 244563996294216604 244563996294216604 rfl endpoint_13_42_base endpoint_13_42_p12) (by decide)⟩
private def endpoint_13_43_flag : Flag := ⟨13, 43, 3727⟩
private def endpoint_13_43_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_43_base : receiptBase endpoint_13_43_flag endpoint_13_43_sources = some 247215118609057430 := by decide +kernel
private theorem endpoint_13_43_w0 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 2 247215118609057430 = some 247215118609057430 := by decide +kernel
private theorem endpoint_13_43_w2 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 2 2 247215118609057430 = some 247215118609057430 := by decide +kernel
private theorem endpoint_13_43_p4 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 4 247215118609057430 = some 247215118609057430 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 2 2 247215118609057430 247215118609057430 247215118609057430 endpoint_13_43_w0 endpoint_13_43_w2
private theorem endpoint_13_43_w4 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 4 2 247215118609057430 = some 247215118609057430 := by decide +kernel
private theorem endpoint_13_43_p6 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 6 247215118609057430 = some 247215118609057430 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 4 2 247215118609057430 247215118609057430 247215118609057430 endpoint_13_43_p4 endpoint_13_43_w4
private theorem endpoint_13_43_w6 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 6 2 247215118609057430 = some 247215118609057430 := by decide +kernel
private theorem endpoint_13_43_p8 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 8 247215118609057430 = some 247215118609057430 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 6 2 247215118609057430 247215118609057430 247215118609057430 endpoint_13_43_p6 endpoint_13_43_w6
private theorem endpoint_13_43_w8 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 8 2 247215118609057430 = some 247215118609057430 := by decide +kernel
private theorem endpoint_13_43_p10 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 10 247215118609057430 = some 247215118609057430 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 8 2 247215118609057430 247215118609057430 247215118609057430 endpoint_13_43_p8 endpoint_13_43_w8
private theorem endpoint_13_43_w10 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 10 2 247215118609057430 = some 247215118609057430 := by decide +kernel
private theorem endpoint_13_43_p12 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 12 247215118609057430 = some 247215118609057430 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 10 2 247215118609057430 247215118609057430 247215118609057430 endpoint_13_43_p10 endpoint_13_43_w10
def endpoint_13_43 : CertifiedEndpoint :=
  ⟨⟨13, 43, 3727⟩, 247215118609057430, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_43_flag endpoint_13_43_sources 12 247215118609057430 247215118609057430 rfl endpoint_13_43_base endpoint_13_43_p12) (by decide)⟩
private def endpoint_13_44_flag : Flag := ⟨13, 44, 3692⟩
private def endpoint_13_44_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_44_base : receiptBase endpoint_13_44_flag endpoint_13_44_sources = some 249774654517816650 := by decide +kernel
private theorem endpoint_13_44_w0 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 2 249774654517816650 = some 249774654517816650 := by decide +kernel
private theorem endpoint_13_44_w2 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 2 2 249774654517816650 = some 249774654517816650 := by decide +kernel
private theorem endpoint_13_44_p4 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 4 249774654517816650 = some 249774654517816650 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 2 2 249774654517816650 249774654517816650 249774654517816650 endpoint_13_44_w0 endpoint_13_44_w2
private theorem endpoint_13_44_w4 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 4 2 249774654517816650 = some 249774654517816650 := by decide +kernel
private theorem endpoint_13_44_p6 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 6 249774654517816650 = some 249774654517816650 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 4 2 249774654517816650 249774654517816650 249774654517816650 endpoint_13_44_p4 endpoint_13_44_w4
private theorem endpoint_13_44_w6 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 6 2 249774654517816650 = some 249774654517816650 := by decide +kernel
private theorem endpoint_13_44_p8 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 8 249774654517816650 = some 249774654517816650 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 6 2 249774654517816650 249774654517816650 249774654517816650 endpoint_13_44_p6 endpoint_13_44_w6
private theorem endpoint_13_44_w8 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 8 2 249774654517816650 = some 249774654517816650 := by decide +kernel
private theorem endpoint_13_44_p10 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 10 249774654517816650 = some 249774654517816650 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 8 2 249774654517816650 249774654517816650 249774654517816650 endpoint_13_44_p8 endpoint_13_44_w8
private theorem endpoint_13_44_w10 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 10 2 249774654517816650 = some 249774654517816650 := by decide +kernel
private theorem endpoint_13_44_p12 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 12 249774654517816650 = some 249774654517816650 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 10 2 249774654517816650 249774654517816650 249774654517816650 endpoint_13_44_p10 endpoint_13_44_w10
def endpoint_13_44 : CertifiedEndpoint :=
  ⟨⟨13, 44, 3692⟩, 249774654517816650, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_44_flag endpoint_13_44_sources 12 249774654517816650 249774654517816650 rfl endpoint_13_44_base endpoint_13_44_p12) (by decide)⟩
private def endpoint_13_45_flag : Flag := ⟨13, 45, 3656⟩
private def endpoint_13_45_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_45_base : receiptBase endpoint_13_45_flag endpoint_13_45_sources = some 252174681180066394 := by decide +kernel
private theorem endpoint_13_45_w0 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 2 252174681180066394 = some 252174681180066394 := by decide +kernel
private theorem endpoint_13_45_w2 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 2 2 252174681180066394 = some 252174681180066394 := by decide +kernel
private theorem endpoint_13_45_p4 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 4 252174681180066394 = some 252174681180066394 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 2 2 252174681180066394 252174681180066394 252174681180066394 endpoint_13_45_w0 endpoint_13_45_w2
private theorem endpoint_13_45_w4 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 4 2 252174681180066394 = some 252174681180066394 := by decide +kernel
private theorem endpoint_13_45_p6 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 6 252174681180066394 = some 252174681180066394 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 4 2 252174681180066394 252174681180066394 252174681180066394 endpoint_13_45_p4 endpoint_13_45_w4
private theorem endpoint_13_45_w6 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 6 2 252174681180066394 = some 252174681180066394 := by decide +kernel
private theorem endpoint_13_45_p8 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 8 252174681180066394 = some 252174681180066394 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 6 2 252174681180066394 252174681180066394 252174681180066394 endpoint_13_45_p6 endpoint_13_45_w6
private theorem endpoint_13_45_w8 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 8 2 252174681180066394 = some 252174681180066394 := by decide +kernel
private theorem endpoint_13_45_p10 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 10 252174681180066394 = some 252174681180066394 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 8 2 252174681180066394 252174681180066394 252174681180066394 endpoint_13_45_p8 endpoint_13_45_w8
private theorem endpoint_13_45_w10 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 10 2 252174681180066394 = some 252174681180066394 := by decide +kernel
private theorem endpoint_13_45_p12 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 12 252174681180066394 = some 252174681180066394 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 10 2 252174681180066394 252174681180066394 252174681180066394 endpoint_13_45_p10 endpoint_13_45_w10
def endpoint_13_45 : CertifiedEndpoint :=
  ⟨⟨13, 45, 3656⟩, 252174681180066394, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_45_flag endpoint_13_45_sources 12 252174681180066394 252174681180066394 rfl endpoint_13_45_base endpoint_13_45_p12) (by decide)⟩
private def endpoint_13_46_flag : Flag := ⟨13, 46, 3619⟩
private def endpoint_13_46_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_46_base : receiptBase endpoint_13_46_flag endpoint_13_46_sources = some 254411328937786524 := by decide +kernel
private theorem endpoint_13_46_w0 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 2 254411328937786524 = some 254411328937786524 := by decide +kernel
private theorem endpoint_13_46_w2 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 2 2 254411328937786524 = some 254411328937786524 := by decide +kernel
private theorem endpoint_13_46_p4 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 4 254411328937786524 = some 254411328937786524 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 2 2 254411328937786524 254411328937786524 254411328937786524 endpoint_13_46_w0 endpoint_13_46_w2
private theorem endpoint_13_46_w4 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 4 2 254411328937786524 = some 254411328937786524 := by decide +kernel
private theorem endpoint_13_46_p6 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 6 254411328937786524 = some 254411328937786524 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 4 2 254411328937786524 254411328937786524 254411328937786524 endpoint_13_46_p4 endpoint_13_46_w4
private theorem endpoint_13_46_w6 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 6 2 254411328937786524 = some 254411328937786524 := by decide +kernel
private theorem endpoint_13_46_p8 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 8 254411328937786524 = some 254411328937786524 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 6 2 254411328937786524 254411328937786524 254411328937786524 endpoint_13_46_p6 endpoint_13_46_w6
private theorem endpoint_13_46_w8 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 8 2 254411328937786524 = some 254411328937786524 := by decide +kernel
private theorem endpoint_13_46_p10 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 10 254411328937786524 = some 254411328937786524 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 8 2 254411328937786524 254411328937786524 254411328937786524 endpoint_13_46_p8 endpoint_13_46_w8
private theorem endpoint_13_46_w10 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 10 2 254411328937786524 = some 254411328937786524 := by decide +kernel
private theorem endpoint_13_46_p12 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 12 254411328937786524 = some 254411328937786524 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 10 2 254411328937786524 254411328937786524 254411328937786524 endpoint_13_46_p10 endpoint_13_46_w10
def endpoint_13_46 : CertifiedEndpoint :=
  ⟨⟨13, 46, 3619⟩, 254411328937786524, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_46_flag endpoint_13_46_sources 12 254411328937786524 254411328937786524 rfl endpoint_13_46_base endpoint_13_46_p12) (by decide)⟩
private def endpoint_13_47_flag : Flag := ⟨13, 47, 3581⟩
private def endpoint_13_47_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_47_base : receiptBase endpoint_13_47_flag endpoint_13_47_sources = some 256480728132956904 := by decide +kernel
private theorem endpoint_13_47_w0 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 2 256480728132956904 = some 256480728132956904 := by decide +kernel
private theorem endpoint_13_47_w2 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 2 2 256480728132956904 = some 256480728132956904 := by decide +kernel
private theorem endpoint_13_47_p4 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 4 256480728132956904 = some 256480728132956904 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 2 2 256480728132956904 256480728132956904 256480728132956904 endpoint_13_47_w0 endpoint_13_47_w2
private theorem endpoint_13_47_w4 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 4 2 256480728132956904 = some 256480728132956904 := by decide +kernel
private theorem endpoint_13_47_p6 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 6 256480728132956904 = some 256480728132956904 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 4 2 256480728132956904 256480728132956904 256480728132956904 endpoint_13_47_p4 endpoint_13_47_w4
private theorem endpoint_13_47_w6 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 6 2 256480728132956904 = some 256480728132956904 := by decide +kernel
private theorem endpoint_13_47_p8 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 8 256480728132956904 = some 256480728132956904 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 6 2 256480728132956904 256480728132956904 256480728132956904 endpoint_13_47_p6 endpoint_13_47_w6
private theorem endpoint_13_47_w8 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 8 2 256480728132956904 = some 256480728132956904 := by decide +kernel
private theorem endpoint_13_47_p10 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 10 256480728132956904 = some 256480728132956904 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 8 2 256480728132956904 256480728132956904 256480728132956904 endpoint_13_47_p8 endpoint_13_47_w8
private theorem endpoint_13_47_w10 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 10 2 256480728132956904 = some 256480728132956904 := by decide +kernel
private theorem endpoint_13_47_p12 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 12 256480728132956904 = some 256480728132956904 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 10 2 256480728132956904 256480728132956904 256480728132956904 endpoint_13_47_p10 endpoint_13_47_w10
def endpoint_13_47 : CertifiedEndpoint :=
  ⟨⟨13, 47, 3581⟩, 256480728132956904, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_47_flag endpoint_13_47_sources 12 256480728132956904 256480728132956904 rfl endpoint_13_47_base endpoint_13_47_p12) (by decide)⟩
private def endpoint_13_48_flag : Flag := ⟨13, 48, 3542⟩
private def endpoint_13_48_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_48_base : receiptBase endpoint_13_48_flag endpoint_13_48_sources = some 259233024730472253 := by decide +kernel
private theorem endpoint_13_48_w0 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 2 259233024730472253 = some 259233024730472253 := by decide +kernel
private theorem endpoint_13_48_w2 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 2 2 259233024730472253 = some 259233024730472253 := by decide +kernel
private theorem endpoint_13_48_p4 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 4 259233024730472253 = some 259233024730472253 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 2 2 259233024730472253 259233024730472253 259233024730472253 endpoint_13_48_w0 endpoint_13_48_w2
private theorem endpoint_13_48_w4 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 4 2 259233024730472253 = some 259233024730472253 := by decide +kernel
private theorem endpoint_13_48_p6 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 6 259233024730472253 = some 259233024730472253 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 4 2 259233024730472253 259233024730472253 259233024730472253 endpoint_13_48_p4 endpoint_13_48_w4
private theorem endpoint_13_48_w6 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 6 2 259233024730472253 = some 259233024730472253 := by decide +kernel
private theorem endpoint_13_48_p8 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 8 259233024730472253 = some 259233024730472253 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 6 2 259233024730472253 259233024730472253 259233024730472253 endpoint_13_48_p6 endpoint_13_48_w6
private theorem endpoint_13_48_w8 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 8 2 259233024730472253 = some 259233024730472253 := by decide +kernel
private theorem endpoint_13_48_p10 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 10 259233024730472253 = some 259233024730472253 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 8 2 259233024730472253 259233024730472253 259233024730472253 endpoint_13_48_p8 endpoint_13_48_w8
private theorem endpoint_13_48_w10 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 10 2 259233024730472253 = some 259233024730472253 := by decide +kernel
private theorem endpoint_13_48_p12 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 12 259233024730472253 = some 259233024730472253 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 10 2 259233024730472253 259233024730472253 259233024730472253 endpoint_13_48_p10 endpoint_13_48_w10
def endpoint_13_48 : CertifiedEndpoint :=
  ⟨⟨13, 48, 3542⟩, 259233024730472253, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_48_flag endpoint_13_48_sources 12 259233024730472253 259233024730472253 rfl endpoint_13_48_base endpoint_13_48_p12) (by decide)⟩
private def endpoint_13_49_flag : Flag := ⟨13, 49, 3503⟩
private def endpoint_13_49_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_49_base : receiptBase endpoint_13_49_flag endpoint_13_49_sources = some 261041313659178777 := by decide +kernel
private theorem endpoint_13_49_w0 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 2 261041313659178777 = some 261041313659178777 := by decide +kernel
private theorem endpoint_13_49_w2 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 2 2 261041313659178777 = some 261041313659178777 := by decide +kernel
private theorem endpoint_13_49_p4 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 4 261041313659178777 = some 261041313659178777 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 2 2 261041313659178777 261041313659178777 261041313659178777 endpoint_13_49_w0 endpoint_13_49_w2
private theorem endpoint_13_49_w4 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 4 2 261041313659178777 = some 261041313659178777 := by decide +kernel
private theorem endpoint_13_49_p6 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 6 261041313659178777 = some 261041313659178777 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 4 2 261041313659178777 261041313659178777 261041313659178777 endpoint_13_49_p4 endpoint_13_49_w4
private theorem endpoint_13_49_w6 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 6 2 261041313659178777 = some 261041313659178777 := by decide +kernel
private theorem endpoint_13_49_p8 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 8 261041313659178777 = some 261041313659178777 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 6 2 261041313659178777 261041313659178777 261041313659178777 endpoint_13_49_p6 endpoint_13_49_w6
private theorem endpoint_13_49_w8 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 8 2 261041313659178777 = some 261041313659178777 := by decide +kernel
private theorem endpoint_13_49_p10 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 10 261041313659178777 = some 261041313659178777 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 8 2 261041313659178777 261041313659178777 261041313659178777 endpoint_13_49_p8 endpoint_13_49_w8
private theorem endpoint_13_49_w10 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 10 2 261041313659178777 = some 261041313659178777 := by decide +kernel
private theorem endpoint_13_49_p12 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 12 261041313659178777 = some 261041313659178777 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 10 2 261041313659178777 261041313659178777 261041313659178777 endpoint_13_49_p10 endpoint_13_49_w10
def endpoint_13_49 : CertifiedEndpoint :=
  ⟨⟨13, 49, 3503⟩, 261041313659178777, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_49_flag endpoint_13_49_sources 12 261041313659178777 261041313659178777 rfl endpoint_13_49_base endpoint_13_49_p12) (by decide)⟩
private def endpoint_13_50_flag : Flag := ⟨13, 50, 3462⟩
private def endpoint_13_50_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_50_base : receiptBase endpoint_13_50_flag endpoint_13_50_sources = some 262597581985995247 := by decide +kernel
private theorem endpoint_13_50_w0 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 2 262597581985995247 = some 262597581985995247 := by decide +kernel
private theorem endpoint_13_50_w2 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 2 2 262597581985995247 = some 262597581985995247 := by decide +kernel
private theorem endpoint_13_50_p4 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 4 262597581985995247 = some 262597581985995247 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 2 2 262597581985995247 262597581985995247 262597581985995247 endpoint_13_50_w0 endpoint_13_50_w2
private theorem endpoint_13_50_w4 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 4 2 262597581985995247 = some 262597581985995247 := by decide +kernel
private theorem endpoint_13_50_p6 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 6 262597581985995247 = some 262597581985995247 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 4 2 262597581985995247 262597581985995247 262597581985995247 endpoint_13_50_p4 endpoint_13_50_w4
private theorem endpoint_13_50_w6 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 6 2 262597581985995247 = some 262597581985995247 := by decide +kernel
private theorem endpoint_13_50_p8 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 8 262597581985995247 = some 262597581985995247 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 6 2 262597581985995247 262597581985995247 262597581985995247 endpoint_13_50_p6 endpoint_13_50_w6
private theorem endpoint_13_50_w8 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 8 2 262597581985995247 = some 262597581985995247 := by decide +kernel
private theorem endpoint_13_50_p10 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 10 262597581985995247 = some 262597581985995247 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 8 2 262597581985995247 262597581985995247 262597581985995247 endpoint_13_50_p8 endpoint_13_50_w8
private theorem endpoint_13_50_w10 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 10 2 262597581985995247 = some 262597581985995247 := by decide +kernel
private theorem endpoint_13_50_p12 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 12 262597581985995247 = some 262597581985995247 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 10 2 262597581985995247 262597581985995247 262597581985995247 endpoint_13_50_p10 endpoint_13_50_w10
def endpoint_13_50 : CertifiedEndpoint :=
  ⟨⟨13, 50, 3462⟩, 262597581985995247, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_50_flag endpoint_13_50_sources 12 262597581985995247 262597581985995247 rfl endpoint_13_50_base endpoint_13_50_p12) (by decide)⟩
private def endpoint_13_51_flag : Flag := ⟨13, 51, 3420⟩
private def endpoint_13_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_51_base : receiptBase endpoint_13_51_flag endpoint_13_51_sources = some 262508008266571878 := by decide +kernel
private theorem endpoint_13_51_w0 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 2 262508008266571878 = some 262508008266571878 := by decide +kernel
private theorem endpoint_13_51_w2 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 2 2 262508008266571878 = some 262508008266571878 := by decide +kernel
private theorem endpoint_13_51_p4 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 4 262508008266571878 = some 262508008266571878 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 2 2 262508008266571878 262508008266571878 262508008266571878 endpoint_13_51_w0 endpoint_13_51_w2
private theorem endpoint_13_51_w4 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 4 2 262508008266571878 = some 262508008266571878 := by decide +kernel
private theorem endpoint_13_51_p6 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 6 262508008266571878 = some 262508008266571878 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 4 2 262508008266571878 262508008266571878 262508008266571878 endpoint_13_51_p4 endpoint_13_51_w4
private theorem endpoint_13_51_w6 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 6 2 262508008266571878 = some 262508008266571878 := by decide +kernel
private theorem endpoint_13_51_p8 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 8 262508008266571878 = some 262508008266571878 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 6 2 262508008266571878 262508008266571878 262508008266571878 endpoint_13_51_p6 endpoint_13_51_w6
private theorem endpoint_13_51_w8 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 8 2 262508008266571878 = some 262508008266571878 := by decide +kernel
private theorem endpoint_13_51_p10 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 10 262508008266571878 = some 262508008266571878 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 8 2 262508008266571878 262508008266571878 262508008266571878 endpoint_13_51_p8 endpoint_13_51_w8
private theorem endpoint_13_51_w10 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 10 2 262508008266571878 = some 262508008266571878 := by decide +kernel
private theorem endpoint_13_51_p12 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 12 262508008266571878 = some 262508008266571878 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 10 2 262508008266571878 262508008266571878 262508008266571878 endpoint_13_51_p10 endpoint_13_51_w10
def endpoint_13_51 : CertifiedEndpoint :=
  ⟨⟨13, 51, 3420⟩, 262508008266571878, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_51_flag endpoint_13_51_sources 12 262508008266571878 262508008266571878 rfl endpoint_13_51_base endpoint_13_51_p12) (by decide)⟩
private def endpoint_13_52_flag : Flag := ⟨13, 52, 3377⟩
private def endpoint_13_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_52_base : receiptBase endpoint_13_52_flag endpoint_13_52_sources = some 263676971577140680 := by decide +kernel
private theorem endpoint_13_52_w0 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 2 263676971577140680 = some 263676971577140680 := by decide +kernel
private theorem endpoint_13_52_w2 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 2 2 263676971577140680 = some 263676971577140680 := by decide +kernel
private theorem endpoint_13_52_p4 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 4 263676971577140680 = some 263676971577140680 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 2 2 263676971577140680 263676971577140680 263676971577140680 endpoint_13_52_w0 endpoint_13_52_w2
private theorem endpoint_13_52_w4 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 4 2 263676971577140680 = some 263676971577140680 := by decide +kernel
private theorem endpoint_13_52_p6 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 6 263676971577140680 = some 263676971577140680 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 4 2 263676971577140680 263676971577140680 263676971577140680 endpoint_13_52_p4 endpoint_13_52_w4
private theorem endpoint_13_52_w6 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 6 2 263676971577140680 = some 263676971577140680 := by decide +kernel
private theorem endpoint_13_52_p8 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 8 263676971577140680 = some 263676971577140680 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 6 2 263676971577140680 263676971577140680 263676971577140680 endpoint_13_52_p6 endpoint_13_52_w6
private theorem endpoint_13_52_w8 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 8 2 263676971577140680 = some 263676971577140680 := by decide +kernel
private theorem endpoint_13_52_p10 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 10 263676971577140680 = some 263676971577140680 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 8 2 263676971577140680 263676971577140680 263676971577140680 endpoint_13_52_p8 endpoint_13_52_w8
private theorem endpoint_13_52_w10 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 10 2 263676971577140680 = some 263676971577140680 := by decide +kernel
private theorem endpoint_13_52_p12 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 12 263676971577140680 = some 263676971577140680 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 10 2 263676971577140680 263676971577140680 263676971577140680 endpoint_13_52_p10 endpoint_13_52_w10
def endpoint_13_52 : CertifiedEndpoint :=
  ⟨⟨13, 52, 3377⟩, 263676971577140680, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_52_flag endpoint_13_52_sources 12 263676971577140680 263676971577140680 rfl endpoint_13_52_base endpoint_13_52_p12) (by decide)⟩
private def endpoint_13_53_flag : Flag := ⟨13, 53, 3333⟩
private def endpoint_13_53_sources : Sources := ⟨contact00, contact35, contact36⟩
private theorem endpoint_13_53_base : receiptBase endpoint_13_53_flag endpoint_13_53_sources = some 263935650608715683 := by decide +kernel
private theorem endpoint_13_53_w0 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 2 263935650608715683 = some 263935650608715683 := by decide +kernel
private theorem endpoint_13_53_w2 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 2 2 263935650608715683 = some 263935650608715683 := by decide +kernel
private theorem endpoint_13_53_p4 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 4 263935650608715683 = some 263935650608715683 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 2 2 263935650608715683 263935650608715683 263935650608715683 endpoint_13_53_w0 endpoint_13_53_w2
private theorem endpoint_13_53_w4 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 4 2 263935650608715683 = some 263935650608715683 := by decide +kernel
private theorem endpoint_13_53_p6 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 6 263935650608715683 = some 263935650608715683 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 4 2 263935650608715683 263935650608715683 263935650608715683 endpoint_13_53_p4 endpoint_13_53_w4
private theorem endpoint_13_53_w6 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 6 2 263935650608715683 = some 263935650608715683 := by decide +kernel
private theorem endpoint_13_53_p8 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 8 263935650608715683 = some 263935650608715683 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 6 2 263935650608715683 263935650608715683 263935650608715683 endpoint_13_53_p6 endpoint_13_53_w6
private theorem endpoint_13_53_w8 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 8 2 263935650608715683 = some 263935650608715683 := by decide +kernel
private theorem endpoint_13_53_p10 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 10 263935650608715683 = some 263935650608715683 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 8 2 263935650608715683 263935650608715683 263935650608715683 endpoint_13_53_p8 endpoint_13_53_w8
private theorem endpoint_13_53_w10 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 10 2 263935650608715683 = some 263935650608715683 := by decide +kernel
private theorem endpoint_13_53_p12 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 12 263935650608715683 = some 263935650608715683 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 10 2 263935650608715683 263935650608715683 263935650608715683 endpoint_13_53_p10 endpoint_13_53_w10
def endpoint_13_53 : CertifiedEndpoint :=
  ⟨⟨13, 53, 3333⟩, 263935650608715683, .terminal ⟨contact00, contact35, contact36⟩ (finish_receipt_window endpoint_13_53_flag endpoint_13_53_sources 12 263935650608715683 263935650608715683 rfl endpoint_13_53_base endpoint_13_53_p12) (by decide)⟩
private def endpoint_13_54_flag : Flag := ⟨13, 54, 3287⟩
private def endpoint_13_54_sources : Sources := ⟨contact00, contact35, contact36⟩
private theorem endpoint_13_54_base : receiptBase endpoint_13_54_flag endpoint_13_54_sources = some 264620643403372462 := by decide +kernel
private theorem endpoint_13_54_w0 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 2 264620643403372462 = some 264620643403372462 := by decide +kernel
private theorem endpoint_13_54_w2 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 2 2 264620643403372462 = some 264620643403372462 := by decide +kernel
private theorem endpoint_13_54_p4 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 4 264620643403372462 = some 264620643403372462 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 2 2 264620643403372462 264620643403372462 264620643403372462 endpoint_13_54_w0 endpoint_13_54_w2
private theorem endpoint_13_54_w4 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 4 2 264620643403372462 = some 264620643403372462 := by decide +kernel
private theorem endpoint_13_54_p6 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 6 264620643403372462 = some 264620643403372462 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 4 2 264620643403372462 264620643403372462 264620643403372462 endpoint_13_54_p4 endpoint_13_54_w4
private theorem endpoint_13_54_w6 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 6 2 264620643403372462 = some 264620643403372462 := by decide +kernel
private theorem endpoint_13_54_p8 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 8 264620643403372462 = some 264620643403372462 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 6 2 264620643403372462 264620643403372462 264620643403372462 endpoint_13_54_p6 endpoint_13_54_w6
private theorem endpoint_13_54_w8 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 8 2 264620643403372462 = some 264620643403372462 := by decide +kernel
private theorem endpoint_13_54_p10 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 10 264620643403372462 = some 264620643403372462 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 8 2 264620643403372462 264620643403372462 264620643403372462 endpoint_13_54_p8 endpoint_13_54_w8
private theorem endpoint_13_54_w10 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 10 2 264620643403372462 = some 264620643403372462 := by decide +kernel
private theorem endpoint_13_54_p12 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 12 264620643403372462 = some 264620643403372462 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 10 2 264620643403372462 264620643403372462 264620643403372462 endpoint_13_54_p10 endpoint_13_54_w10
def endpoint_13_54 : CertifiedEndpoint :=
  ⟨⟨13, 54, 3287⟩, 264620643403372462, .terminal ⟨contact00, contact35, contact36⟩ (finish_receipt_window endpoint_13_54_flag endpoint_13_54_sources 12 264620643403372462 264620643403372462 rfl endpoint_13_54_base endpoint_13_54_p12) (by decide)⟩
private def endpoint_13_55_flag : Flag := ⟨13, 55, 3240⟩
private def endpoint_13_55_sources : Sources := ⟨contact00, contact35, contact36⟩
private theorem endpoint_13_55_base : receiptBase endpoint_13_55_flag endpoint_13_55_sources = some 265104877537261085 := by decide +kernel
private theorem endpoint_13_55_w0 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 2 265104877537261085 = some 265104877537261085 := by decide +kernel
private theorem endpoint_13_55_w2 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 2 2 265104877537261085 = some 265104877537261085 := by decide +kernel
private theorem endpoint_13_55_p4 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 4 265104877537261085 = some 265104877537261085 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 2 2 265104877537261085 265104877537261085 265104877537261085 endpoint_13_55_w0 endpoint_13_55_w2
private theorem endpoint_13_55_w4 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 4 2 265104877537261085 = some 265104877537261085 := by decide +kernel
private theorem endpoint_13_55_p6 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 6 265104877537261085 = some 265104877537261085 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 4 2 265104877537261085 265104877537261085 265104877537261085 endpoint_13_55_p4 endpoint_13_55_w4
private theorem endpoint_13_55_w6 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 6 2 265104877537261085 = some 265104877537261085 := by decide +kernel
private theorem endpoint_13_55_p8 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 8 265104877537261085 = some 265104877537261085 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 6 2 265104877537261085 265104877537261085 265104877537261085 endpoint_13_55_p6 endpoint_13_55_w6
private theorem endpoint_13_55_w8 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 8 2 265104877537261085 = some 265104877537261085 := by decide +kernel
private theorem endpoint_13_55_p10 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 10 265104877537261085 = some 265104877537261085 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 8 2 265104877537261085 265104877537261085 265104877537261085 endpoint_13_55_p8 endpoint_13_55_w8
private theorem endpoint_13_55_w10 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 10 2 265104877537261085 = some 265104877537261085 := by decide +kernel
private theorem endpoint_13_55_p12 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 12 265104877537261085 = some 265104877537261085 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 10 2 265104877537261085 265104877537261085 265104877537261085 endpoint_13_55_p10 endpoint_13_55_w10
def endpoint_13_55 : CertifiedEndpoint :=
  ⟨⟨13, 55, 3240⟩, 265104877537261085, .terminal ⟨contact00, contact35, contact36⟩ (finish_receipt_window endpoint_13_55_flag endpoint_13_55_sources 12 265104877537261085 265104877537261085 rfl endpoint_13_55_base endpoint_13_55_p12) (by decide)⟩
private def endpoint_13_56_flag : Flag := ⟨13, 56, 3191⟩
private def endpoint_13_56_sources : Sources := ⟨contact00, contact35, contact36⟩
private theorem endpoint_13_56_base : receiptBase endpoint_13_56_flag endpoint_13_56_sources = some 265302392070466599 := by decide +kernel
private theorem endpoint_13_56_w0 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 2 265302392070466599 = some 265302392070466599 := by decide +kernel
private theorem endpoint_13_56_w2 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 2 2 265302392070466599 = some 265302392070466599 := by decide +kernel
private theorem endpoint_13_56_p4 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 4 265302392070466599 = some 265302392070466599 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 2 2 265302392070466599 265302392070466599 265302392070466599 endpoint_13_56_w0 endpoint_13_56_w2
private theorem endpoint_13_56_w4 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 4 2 265302392070466599 = some 265302392070466599 := by decide +kernel
private theorem endpoint_13_56_p6 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 6 265302392070466599 = some 265302392070466599 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 4 2 265302392070466599 265302392070466599 265302392070466599 endpoint_13_56_p4 endpoint_13_56_w4
private theorem endpoint_13_56_w6 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 6 2 265302392070466599 = some 265302392070466599 := by decide +kernel
private theorem endpoint_13_56_p8 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 8 265302392070466599 = some 265302392070466599 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 6 2 265302392070466599 265302392070466599 265302392070466599 endpoint_13_56_p6 endpoint_13_56_w6
private theorem endpoint_13_56_w8 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 8 2 265302392070466599 = some 265302392070466599 := by decide +kernel
private theorem endpoint_13_56_p10 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 10 265302392070466599 = some 265302392070466599 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 8 2 265302392070466599 265302392070466599 265302392070466599 endpoint_13_56_p8 endpoint_13_56_w8
private theorem endpoint_13_56_w10 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 10 2 265302392070466599 = some 265302392070466599 := by decide +kernel
private theorem endpoint_13_56_p12 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 12 265302392070466599 = some 265302392070466599 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 10 2 265302392070466599 265302392070466599 265302392070466599 endpoint_13_56_p10 endpoint_13_56_w10
def endpoint_13_56 : CertifiedEndpoint :=
  ⟨⟨13, 56, 3191⟩, 265302392070466599, .terminal ⟨contact00, contact35, contact36⟩ (finish_receipt_window endpoint_13_56_flag endpoint_13_56_sources 12 265302392070466599 265302392070466599 rfl endpoint_13_56_base endpoint_13_56_p12) (by decide)⟩
private def endpoint_13_57_flag : Flag := ⟨13, 57, 3140⟩
private def endpoint_13_57_sources : Sources := ⟨contact00, contact35, contact36⟩
private theorem endpoint_13_57_base : receiptBase endpoint_13_57_flag endpoint_13_57_sources = some 265205447527452494 := by decide +kernel
private theorem endpoint_13_57_w0 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 2 265205447527452494 = some 265205447527452494 := by decide +kernel
private theorem endpoint_13_57_w2 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 2 2 265205447527452494 = some 265205447527452494 := by decide +kernel
private theorem endpoint_13_57_p4 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 4 265205447527452494 = some 265205447527452494 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 2 2 265205447527452494 265205447527452494 265205447527452494 endpoint_13_57_w0 endpoint_13_57_w2
private theorem endpoint_13_57_w4 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 4 2 265205447527452494 = some 265205447527452494 := by decide +kernel
private theorem endpoint_13_57_p6 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 6 265205447527452494 = some 265205447527452494 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 4 2 265205447527452494 265205447527452494 265205447527452494 endpoint_13_57_p4 endpoint_13_57_w4
private theorem endpoint_13_57_w6 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 6 2 265205447527452494 = some 265205447527452494 := by decide +kernel
private theorem endpoint_13_57_p8 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 8 265205447527452494 = some 265205447527452494 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 6 2 265205447527452494 265205447527452494 265205447527452494 endpoint_13_57_p6 endpoint_13_57_w6
private theorem endpoint_13_57_w8 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 8 2 265205447527452494 = some 265205447527452494 := by decide +kernel
private theorem endpoint_13_57_p10 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 10 265205447527452494 = some 265205447527452494 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 8 2 265205447527452494 265205447527452494 265205447527452494 endpoint_13_57_p8 endpoint_13_57_w8
private theorem endpoint_13_57_w10 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 10 2 265205447527452494 = some 265205447527452494 := by decide +kernel
private theorem endpoint_13_57_p12 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 12 265205447527452494 = some 265205447527452494 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 10 2 265205447527452494 265205447527452494 265205447527452494 endpoint_13_57_p10 endpoint_13_57_w10
def endpoint_13_57 : CertifiedEndpoint :=
  ⟨⟨13, 57, 3140⟩, 265205447527452494, .terminal ⟨contact00, contact35, contact36⟩ (finish_receipt_window endpoint_13_57_flag endpoint_13_57_sources 12 265205447527452494 265205447527452494 rfl endpoint_13_57_base endpoint_13_57_p12) (by decide)⟩
private def endpoint_13_58_flag : Flag := ⟨13, 58, 3088⟩
private def endpoint_13_58_sources : Sources := ⟨contact34, contact35, contact36⟩
private theorem endpoint_13_58_base : receiptBase endpoint_13_58_flag endpoint_13_58_sources = some 265231631882690930 := by decide +kernel
private theorem endpoint_13_58_w0 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 2 265231631882690930 = some 265231631882690930 := by decide +kernel
private theorem endpoint_13_58_w2 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 2 2 265231631882690930 = some 265231631882690930 := by decide +kernel
private theorem endpoint_13_58_p4 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 4 265231631882690930 = some 265231631882690930 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 2 2 265231631882690930 265231631882690930 265231631882690930 endpoint_13_58_w0 endpoint_13_58_w2
private theorem endpoint_13_58_w4 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 4 2 265231631882690930 = some 265231631882690930 := by decide +kernel
private theorem endpoint_13_58_p6 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 6 265231631882690930 = some 265231631882690930 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 4 2 265231631882690930 265231631882690930 265231631882690930 endpoint_13_58_p4 endpoint_13_58_w4
private theorem endpoint_13_58_w6 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 6 2 265231631882690930 = some 265231631882690930 := by decide +kernel
private theorem endpoint_13_58_p8 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 8 265231631882690930 = some 265231631882690930 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 6 2 265231631882690930 265231631882690930 265231631882690930 endpoint_13_58_p6 endpoint_13_58_w6
private theorem endpoint_13_58_w8 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 8 2 265231631882690930 = some 265231631882690930 := by decide +kernel
private theorem endpoint_13_58_p10 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 10 265231631882690930 = some 265231631882690930 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 8 2 265231631882690930 265231631882690930 265231631882690930 endpoint_13_58_p8 endpoint_13_58_w8
private theorem endpoint_13_58_w10 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 10 2 265231631882690930 = some 265231631882690930 := by decide +kernel
private theorem endpoint_13_58_p12 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 12 265231631882690930 = some 265231631882690930 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 10 2 265231631882690930 265231631882690930 265231631882690930 endpoint_13_58_p10 endpoint_13_58_w10
def endpoint_13_58 : CertifiedEndpoint :=
  ⟨⟨13, 58, 3088⟩, 265231631882690930, .terminal ⟨contact34, contact35, contact36⟩ (finish_receipt_window endpoint_13_58_flag endpoint_13_58_sources 12 265231631882690930 265231631882690930 rfl endpoint_13_58_base endpoint_13_58_p12) (by decide)⟩
private def endpoint_13_59_flag : Flag := ⟨13, 59, 3033⟩
private def endpoint_13_59_sources : Sources := ⟨contact18, contact35, contact37⟩
private theorem endpoint_13_59_base : receiptBase endpoint_13_59_flag endpoint_13_59_sources = some 265025147843114097 := by decide +kernel
private theorem endpoint_13_59_w0 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 2 265025147843114097 = some 265025147843114097 := by decide +kernel
private theorem endpoint_13_59_w2 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 2 2 265025147843114097 = some 265025147843114097 := by decide +kernel
private theorem endpoint_13_59_p4 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 4 265025147843114097 = some 265025147843114097 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 2 2 265025147843114097 265025147843114097 265025147843114097 endpoint_13_59_w0 endpoint_13_59_w2
private theorem endpoint_13_59_w4 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 4 2 265025147843114097 = some 265025147843114097 := by decide +kernel
private theorem endpoint_13_59_p6 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 6 265025147843114097 = some 265025147843114097 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 4 2 265025147843114097 265025147843114097 265025147843114097 endpoint_13_59_p4 endpoint_13_59_w4
private theorem endpoint_13_59_w6 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 6 2 265025147843114097 = some 265025147843114097 := by decide +kernel
private theorem endpoint_13_59_p8 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 8 265025147843114097 = some 265025147843114097 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 6 2 265025147843114097 265025147843114097 265025147843114097 endpoint_13_59_p6 endpoint_13_59_w6
private theorem endpoint_13_59_w8 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 8 2 265025147843114097 = some 265025147843114097 := by decide +kernel
private theorem endpoint_13_59_p10 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 10 265025147843114097 = some 265025147843114097 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 8 2 265025147843114097 265025147843114097 265025147843114097 endpoint_13_59_p8 endpoint_13_59_w8
private theorem endpoint_13_59_w10 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 10 2 265025147843114097 = some 265025147843114097 := by decide +kernel
private theorem endpoint_13_59_p12 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 12 265025147843114097 = some 265025147843114097 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 10 2 265025147843114097 265025147843114097 265025147843114097 endpoint_13_59_p10 endpoint_13_59_w10
def endpoint_13_59 : CertifiedEndpoint :=
  ⟨⟨13, 59, 3033⟩, 265025147843114097, .terminal ⟨contact18, contact35, contact37⟩ (finish_receipt_window endpoint_13_59_flag endpoint_13_59_sources 12 265025147843114097 265025147843114097 rfl endpoint_13_59_base endpoint_13_59_p12) (by decide)⟩
private def endpoint_13_60_flag : Flag := ⟨13, 60, 2977⟩
private def endpoint_13_60_sources : Sources := ⟨contact18, contact35, contact37⟩
private theorem endpoint_13_60_base : receiptBase endpoint_13_60_flag endpoint_13_60_sources = some 264079634240377310 := by decide +kernel
private theorem endpoint_13_60_w0 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 2 264079634240377310 = some 264079634240377310 := by decide +kernel
private theorem endpoint_13_60_w2 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 2 2 264079634240377310 = some 264079634240377310 := by decide +kernel
private theorem endpoint_13_60_p4 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 4 264079634240377310 = some 264079634240377310 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 2 2 264079634240377310 264079634240377310 264079634240377310 endpoint_13_60_w0 endpoint_13_60_w2
private theorem endpoint_13_60_w4 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 4 2 264079634240377310 = some 264079634240377310 := by decide +kernel
private theorem endpoint_13_60_p6 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 6 264079634240377310 = some 264079634240377310 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 4 2 264079634240377310 264079634240377310 264079634240377310 endpoint_13_60_p4 endpoint_13_60_w4
private theorem endpoint_13_60_w6 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 6 2 264079634240377310 = some 264079634240377310 := by decide +kernel
private theorem endpoint_13_60_p8 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 8 264079634240377310 = some 264079634240377310 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 6 2 264079634240377310 264079634240377310 264079634240377310 endpoint_13_60_p6 endpoint_13_60_w6
private theorem endpoint_13_60_w8 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 8 2 264079634240377310 = some 264079634240377310 := by decide +kernel
private theorem endpoint_13_60_p10 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 10 264079634240377310 = some 264079634240377310 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 8 2 264079634240377310 264079634240377310 264079634240377310 endpoint_13_60_p8 endpoint_13_60_w8
private theorem endpoint_13_60_w10 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 10 2 264079634240377310 = some 264079634240377310 := by decide +kernel
private theorem endpoint_13_60_p12 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 12 264079634240377310 = some 264079634240377310 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 10 2 264079634240377310 264079634240377310 264079634240377310 endpoint_13_60_p10 endpoint_13_60_w10
def endpoint_13_60 : CertifiedEndpoint :=
  ⟨⟨13, 60, 2977⟩, 264079634240377310, .terminal ⟨contact18, contact35, contact37⟩ (finish_receipt_window endpoint_13_60_flag endpoint_13_60_sources 12 264079634240377310 264079634240377310 rfl endpoint_13_60_base endpoint_13_60_p12) (by decide)⟩
private def endpoint_13_61_flag : Flag := ⟨13, 61, 2918⟩
private def endpoint_13_61_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_13_61_base : receiptBase endpoint_13_61_flag endpoint_13_61_sources = some 263807334013240779 := by decide +kernel
private theorem endpoint_13_61_w0 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 2 263807334013240779 = some 263807334013240779 := by decide +kernel
private theorem endpoint_13_61_w2 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 2 2 263807334013240779 = some 263807334013240779 := by decide +kernel
private theorem endpoint_13_61_p4 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 4 263807334013240779 = some 263807334013240779 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 2 2 263807334013240779 263807334013240779 263807334013240779 endpoint_13_61_w0 endpoint_13_61_w2
private theorem endpoint_13_61_w4 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 4 2 263807334013240779 = some 263807334013240779 := by decide +kernel
private theorem endpoint_13_61_p6 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 6 263807334013240779 = some 263807334013240779 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 4 2 263807334013240779 263807334013240779 263807334013240779 endpoint_13_61_p4 endpoint_13_61_w4
private theorem endpoint_13_61_w6 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 6 2 263807334013240779 = some 263807334013240779 := by decide +kernel
private theorem endpoint_13_61_p8 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 8 263807334013240779 = some 263807334013240779 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 6 2 263807334013240779 263807334013240779 263807334013240779 endpoint_13_61_p6 endpoint_13_61_w6
private theorem endpoint_13_61_w8 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 8 2 263807334013240779 = some 263807334013240779 := by decide +kernel
private theorem endpoint_13_61_p10 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 10 263807334013240779 = some 263807334013240779 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 8 2 263807334013240779 263807334013240779 263807334013240779 endpoint_13_61_p8 endpoint_13_61_w8
private theorem endpoint_13_61_w10 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 10 2 263807334013240779 = some 263807334013240779 := by decide +kernel
private theorem endpoint_13_61_p12 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 12 263807334013240779 = some 263807334013240779 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 10 2 263807334013240779 263807334013240779 263807334013240779 endpoint_13_61_p10 endpoint_13_61_w10
def endpoint_13_61 : CertifiedEndpoint :=
  ⟨⟨13, 61, 2918⟩, 263807334013240779, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_13_61_flag endpoint_13_61_sources 12 263807334013240779 263807334013240779 rfl endpoint_13_61_base endpoint_13_61_p12) (by decide)⟩
private def endpoint_13_62_flag : Flag := ⟨13, 62, 2856⟩
private def endpoint_13_62_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_62_base : receiptBase endpoint_13_62_flag endpoint_13_62_sources = some 262570550297658850 := by decide +kernel
private theorem endpoint_13_62_w0 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 2 262570550297658850 = some 262570550297658850 := by decide +kernel
private theorem endpoint_13_62_w2 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 2 2 262570550297658850 = some 262570550297658850 := by decide +kernel
private theorem endpoint_13_62_p4 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 4 262570550297658850 = some 262570550297658850 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 2 2 262570550297658850 262570550297658850 262570550297658850 endpoint_13_62_w0 endpoint_13_62_w2
private theorem endpoint_13_62_w4 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 4 2 262570550297658850 = some 262570550297658850 := by decide +kernel
private theorem endpoint_13_62_p6 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 6 262570550297658850 = some 262570550297658850 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 4 2 262570550297658850 262570550297658850 262570550297658850 endpoint_13_62_p4 endpoint_13_62_w4
private theorem endpoint_13_62_w6 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 6 2 262570550297658850 = some 262570550297658850 := by decide +kernel
private theorem endpoint_13_62_p8 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 8 262570550297658850 = some 262570550297658850 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 6 2 262570550297658850 262570550297658850 262570550297658850 endpoint_13_62_p6 endpoint_13_62_w6
private theorem endpoint_13_62_w8 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 8 2 262570550297658850 = some 262570550297658850 := by decide +kernel
private theorem endpoint_13_62_p10 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 10 262570550297658850 = some 262570550297658850 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 8 2 262570550297658850 262570550297658850 262570550297658850 endpoint_13_62_p8 endpoint_13_62_w8
private theorem endpoint_13_62_w10 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 10 2 262570550297658850 = some 262570550297658850 := by decide +kernel
private theorem endpoint_13_62_p12 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 12 262570550297658850 = some 262570550297658850 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 10 2 262570550297658850 262570550297658850 262570550297658850 endpoint_13_62_p10 endpoint_13_62_w10
def endpoint_13_62 : CertifiedEndpoint :=
  ⟨⟨13, 62, 2856⟩, 262570550297658850, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_62_flag endpoint_13_62_sources 12 262570550297658850 262570550297658850 rfl endpoint_13_62_base endpoint_13_62_p12) (by decide)⟩
private def endpoint_13_63_flag : Flag := ⟨13, 63, 2792⟩
private def endpoint_13_63_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_63_base : receiptBase endpoint_13_63_flag endpoint_13_63_sources = some 261891073140639589 := by decide +kernel
private theorem endpoint_13_63_w0 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 2 261891073140639589 = some 261891073140639589 := by decide +kernel
private theorem endpoint_13_63_w2 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 2 2 261891073140639589 = some 261891073140639589 := by decide +kernel
private theorem endpoint_13_63_p4 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 4 261891073140639589 = some 261891073140639589 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 2 2 261891073140639589 261891073140639589 261891073140639589 endpoint_13_63_w0 endpoint_13_63_w2
private theorem endpoint_13_63_w4 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 4 2 261891073140639589 = some 261891073140639589 := by decide +kernel
private theorem endpoint_13_63_p6 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 6 261891073140639589 = some 261891073140639589 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 4 2 261891073140639589 261891073140639589 261891073140639589 endpoint_13_63_p4 endpoint_13_63_w4
private theorem endpoint_13_63_w6 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 6 2 261891073140639589 = some 261891073140639589 := by decide +kernel
private theorem endpoint_13_63_p8 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 8 261891073140639589 = some 261891073140639589 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 6 2 261891073140639589 261891073140639589 261891073140639589 endpoint_13_63_p6 endpoint_13_63_w6
private theorem endpoint_13_63_w8 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 8 2 261891073140639589 = some 261891073140639589 := by decide +kernel
private theorem endpoint_13_63_p10 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 10 261891073140639589 = some 261891073140639589 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 8 2 261891073140639589 261891073140639589 261891073140639589 endpoint_13_63_p8 endpoint_13_63_w8
private theorem endpoint_13_63_w10 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 10 2 261891073140639589 = some 261891073140639589 := by decide +kernel
private theorem endpoint_13_63_p12 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 12 261891073140639589 = some 261891073140639589 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 10 2 261891073140639589 261891073140639589 261891073140639589 endpoint_13_63_p10 endpoint_13_63_w10
def endpoint_13_63 : CertifiedEndpoint :=
  ⟨⟨13, 63, 2792⟩, 261891073140639589, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_63_flag endpoint_13_63_sources 12 261891073140639589 261891073140639589 rfl endpoint_13_63_base endpoint_13_63_p12) (by decide)⟩
private def endpoint_13_64_flag : Flag := ⟨13, 64, 2726⟩
private def endpoint_13_64_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_64_base : receiptBase endpoint_13_64_flag endpoint_13_64_sources = some 259366024038944957 := by decide +kernel
private theorem endpoint_13_64_w0 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 2 259366024038944957 = some 259366024038944957 := by decide +kernel
private theorem endpoint_13_64_w2 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 2 2 259366024038944957 = some 259366024038944957 := by decide +kernel
private theorem endpoint_13_64_p4 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 4 259366024038944957 = some 259366024038944957 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 2 2 259366024038944957 259366024038944957 259366024038944957 endpoint_13_64_w0 endpoint_13_64_w2
private theorem endpoint_13_64_w4 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 4 2 259366024038944957 = some 259366024038944957 := by decide +kernel
private theorem endpoint_13_64_p6 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 6 259366024038944957 = some 259366024038944957 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 4 2 259366024038944957 259366024038944957 259366024038944957 endpoint_13_64_p4 endpoint_13_64_w4
private theorem endpoint_13_64_w6 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 6 2 259366024038944957 = some 259366024038944957 := by decide +kernel
private theorem endpoint_13_64_p8 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 8 259366024038944957 = some 259366024038944957 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 6 2 259366024038944957 259366024038944957 259366024038944957 endpoint_13_64_p6 endpoint_13_64_w6
private theorem endpoint_13_64_w8 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 8 2 259366024038944957 = some 259366024038944957 := by decide +kernel
private theorem endpoint_13_64_p10 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 10 259366024038944957 = some 259366024038944957 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 8 2 259366024038944957 259366024038944957 259366024038944957 endpoint_13_64_p8 endpoint_13_64_w8
private theorem endpoint_13_64_w10 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 10 2 259366024038944957 = some 259366024038944957 := by decide +kernel
private theorem endpoint_13_64_p12 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 12 259366024038944957 = some 259366024038944957 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 10 2 259366024038944957 259366024038944957 259366024038944957 endpoint_13_64_p10 endpoint_13_64_w10
def endpoint_13_64 : CertifiedEndpoint :=
  ⟨⟨13, 64, 2726⟩, 259366024038944957, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_64_flag endpoint_13_64_sources 12 259366024038944957 259366024038944957 rfl endpoint_13_64_base endpoint_13_64_p12) (by decide)⟩
private def endpoint_13_65_flag : Flag := ⟨13, 65, 2656⟩
private def endpoint_13_65_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_65_base : receiptBase endpoint_13_65_flag endpoint_13_65_sources = some 258741471649616670 := by decide +kernel
private theorem endpoint_13_65_w0 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 2 258741471649616670 = some 258741471649616670 := by decide +kernel
private theorem endpoint_13_65_w2 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 2 2 258741471649616670 = some 258741471649616670 := by decide +kernel
private theorem endpoint_13_65_p4 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 4 258741471649616670 = some 258741471649616670 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 2 2 258741471649616670 258741471649616670 258741471649616670 endpoint_13_65_w0 endpoint_13_65_w2
private theorem endpoint_13_65_w4 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 4 2 258741471649616670 = some 258741471649616670 := by decide +kernel
private theorem endpoint_13_65_p6 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 6 258741471649616670 = some 258741471649616670 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 4 2 258741471649616670 258741471649616670 258741471649616670 endpoint_13_65_p4 endpoint_13_65_w4
private theorem endpoint_13_65_w6 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 6 2 258741471649616670 = some 258741471649616670 := by decide +kernel
private theorem endpoint_13_65_p8 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 8 258741471649616670 = some 258741471649616670 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 6 2 258741471649616670 258741471649616670 258741471649616670 endpoint_13_65_p6 endpoint_13_65_w6
private theorem endpoint_13_65_w8 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 8 2 258741471649616670 = some 258741471649616670 := by decide +kernel
private theorem endpoint_13_65_p10 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 10 258741471649616670 = some 258741471649616670 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 8 2 258741471649616670 258741471649616670 258741471649616670 endpoint_13_65_p8 endpoint_13_65_w8
private theorem endpoint_13_65_w10 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 10 2 258741471649616670 = some 258741471649616670 := by decide +kernel
private theorem endpoint_13_65_p12 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 12 258741471649616670 = some 258741471649616670 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 10 2 258741471649616670 258741471649616670 258741471649616670 endpoint_13_65_p10 endpoint_13_65_w10
def endpoint_13_65 : CertifiedEndpoint :=
  ⟨⟨13, 65, 2656⟩, 258741471649616670, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_65_flag endpoint_13_65_sources 12 258741471649616670 258741471649616670 rfl endpoint_13_65_base endpoint_13_65_p12) (by decide)⟩
private def endpoint_13_66_flag : Flag := ⟨13, 66, 2585⟩
private def endpoint_13_66_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_66_base : receiptBase endpoint_13_66_flag endpoint_13_66_sources = some 263106676115708289 := by decide +kernel
private theorem endpoint_13_66_w0 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 2 263106676115708289 = some 263106676115708289 := by decide +kernel
private theorem endpoint_13_66_w2 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 2 2 263106676115708289 = some 263106676115708289 := by decide +kernel
private theorem endpoint_13_66_p4 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 4 263106676115708289 = some 263106676115708289 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 2 2 263106676115708289 263106676115708289 263106676115708289 endpoint_13_66_w0 endpoint_13_66_w2
private theorem endpoint_13_66_w4 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 4 2 263106676115708289 = some 263106676115708289 := by decide +kernel
private theorem endpoint_13_66_p6 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 6 263106676115708289 = some 263106676115708289 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 4 2 263106676115708289 263106676115708289 263106676115708289 endpoint_13_66_p4 endpoint_13_66_w4
private theorem endpoint_13_66_w6 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 6 2 263106676115708289 = some 263106676115708289 := by decide +kernel
private theorem endpoint_13_66_p8 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 8 263106676115708289 = some 263106676115708289 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 6 2 263106676115708289 263106676115708289 263106676115708289 endpoint_13_66_p6 endpoint_13_66_w6
private theorem endpoint_13_66_w8 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 8 2 263106676115708289 = some 263106676115708289 := by decide +kernel
private theorem endpoint_13_66_p10 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 10 263106676115708289 = some 263106676115708289 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 8 2 263106676115708289 263106676115708289 263106676115708289 endpoint_13_66_p8 endpoint_13_66_w8
private theorem endpoint_13_66_w10 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 10 2 263106676115708289 = some 263106676115708289 := by decide +kernel
private theorem endpoint_13_66_p12 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 12 263106676115708289 = some 263106676115708289 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 10 2 263106676115708289 263106676115708289 263106676115708289 endpoint_13_66_p10 endpoint_13_66_w10
def endpoint_13_66 : CertifiedEndpoint :=
  ⟨⟨13, 66, 2585⟩, 263106676115708289, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_66_flag endpoint_13_66_sources 12 263106676115708289 263106676115708289 rfl endpoint_13_66_base endpoint_13_66_p12) (by decide)⟩
private def endpoint_13_67_flag : Flag := ⟨13, 67, 2510⟩
private def endpoint_13_67_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_67_base : receiptBase endpoint_13_67_flag endpoint_13_67_sources = some 260036125930251651 := by decide +kernel
private theorem endpoint_13_67_w0 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 2 260036125930251651 = some 260036125930251651 := by decide +kernel
private theorem endpoint_13_67_w2 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 2 2 260036125930251651 = some 260036125930251651 := by decide +kernel
private theorem endpoint_13_67_p4 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 4 260036125930251651 = some 260036125930251651 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 2 2 260036125930251651 260036125930251651 260036125930251651 endpoint_13_67_w0 endpoint_13_67_w2
private theorem endpoint_13_67_w4 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 4 2 260036125930251651 = some 260036125930251651 := by decide +kernel
private theorem endpoint_13_67_p6 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 6 260036125930251651 = some 260036125930251651 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 4 2 260036125930251651 260036125930251651 260036125930251651 endpoint_13_67_p4 endpoint_13_67_w4
private theorem endpoint_13_67_w6 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 6 2 260036125930251651 = some 260036125930251651 := by decide +kernel
private theorem endpoint_13_67_p8 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 8 260036125930251651 = some 260036125930251651 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 6 2 260036125930251651 260036125930251651 260036125930251651 endpoint_13_67_p6 endpoint_13_67_w6
private theorem endpoint_13_67_w8 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 8 2 260036125930251651 = some 260036125930251651 := by decide +kernel
private theorem endpoint_13_67_p10 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 10 260036125930251651 = some 260036125930251651 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 8 2 260036125930251651 260036125930251651 260036125930251651 endpoint_13_67_p8 endpoint_13_67_w8
private theorem endpoint_13_67_w10 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 10 2 260036125930251651 = some 260036125930251651 := by decide +kernel
private theorem endpoint_13_67_p12 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 12 260036125930251651 = some 260036125930251651 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 10 2 260036125930251651 260036125930251651 260036125930251651 endpoint_13_67_p10 endpoint_13_67_w10
def endpoint_13_67 : CertifiedEndpoint :=
  ⟨⟨13, 67, 2510⟩, 260036125930251651, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_67_flag endpoint_13_67_sources 12 260036125930251651 260036125930251651 rfl endpoint_13_67_base endpoint_13_67_p12) (by decide)⟩
private def endpoint_13_68_flag : Flag := ⟨13, 68, 2433⟩
private def endpoint_13_68_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_68_base : receiptBase endpoint_13_68_flag endpoint_13_68_sources = some 255568004768412943 := by decide +kernel
private theorem endpoint_13_68_w0 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 2 255568004768412943 = some 255568004768412943 := by decide +kernel
private theorem endpoint_13_68_w2 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 2 2 255568004768412943 = some 255568004768412943 := by decide +kernel
private theorem endpoint_13_68_p4 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 4 255568004768412943 = some 255568004768412943 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 2 2 255568004768412943 255568004768412943 255568004768412943 endpoint_13_68_w0 endpoint_13_68_w2
private theorem endpoint_13_68_w4 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 4 2 255568004768412943 = some 255568004768412943 := by decide +kernel
private theorem endpoint_13_68_p6 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 6 255568004768412943 = some 255568004768412943 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 4 2 255568004768412943 255568004768412943 255568004768412943 endpoint_13_68_p4 endpoint_13_68_w4
private theorem endpoint_13_68_w6 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 6 2 255568004768412943 = some 255568004768412943 := by decide +kernel
private theorem endpoint_13_68_p8 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 8 255568004768412943 = some 255568004768412943 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 6 2 255568004768412943 255568004768412943 255568004768412943 endpoint_13_68_p6 endpoint_13_68_w6
private theorem endpoint_13_68_w8 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 8 2 255568004768412943 = some 255568004768412943 := by decide +kernel
private theorem endpoint_13_68_p10 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 10 255568004768412943 = some 255568004768412943 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 8 2 255568004768412943 255568004768412943 255568004768412943 endpoint_13_68_p8 endpoint_13_68_w8
private theorem endpoint_13_68_w10 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 10 2 255568004768412943 = some 255568004768412943 := by decide +kernel
private theorem endpoint_13_68_p12 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 12 255568004768412943 = some 255568004768412943 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 10 2 255568004768412943 255568004768412943 255568004768412943 endpoint_13_68_p10 endpoint_13_68_w10
def endpoint_13_68 : CertifiedEndpoint :=
  ⟨⟨13, 68, 2433⟩, 255568004768412943, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_68_flag endpoint_13_68_sources 12 255568004768412943 255568004768412943 rfl endpoint_13_68_base endpoint_13_68_p12) (by decide)⟩
private def endpoint_13_69_flag : Flag := ⟨13, 69, 2352⟩
private def endpoint_13_69_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_13_69_base : receiptBase endpoint_13_69_flag endpoint_13_69_sources = some 251901292881945131 := by decide +kernel
private theorem endpoint_13_69_w0 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 2 251901292881945131 = some 251901292881945131 := by decide +kernel
private theorem endpoint_13_69_w2 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 2 2 251901292881945131 = some 251901292881945131 := by decide +kernel
private theorem endpoint_13_69_p4 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 4 251901292881945131 = some 251901292881945131 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 2 2 251901292881945131 251901292881945131 251901292881945131 endpoint_13_69_w0 endpoint_13_69_w2
private theorem endpoint_13_69_w4 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 4 2 251901292881945131 = some 251901292881945131 := by decide +kernel
private theorem endpoint_13_69_p6 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 6 251901292881945131 = some 251901292881945131 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 4 2 251901292881945131 251901292881945131 251901292881945131 endpoint_13_69_p4 endpoint_13_69_w4
private theorem endpoint_13_69_w6 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 6 2 251901292881945131 = some 251901292881945131 := by decide +kernel
private theorem endpoint_13_69_p8 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 8 251901292881945131 = some 251901292881945131 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 6 2 251901292881945131 251901292881945131 251901292881945131 endpoint_13_69_p6 endpoint_13_69_w6
private theorem endpoint_13_69_w8 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 8 2 251901292881945131 = some 251901292881945131 := by decide +kernel
private theorem endpoint_13_69_p10 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 10 251901292881945131 = some 251901292881945131 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 8 2 251901292881945131 251901292881945131 251901292881945131 endpoint_13_69_p8 endpoint_13_69_w8
private theorem endpoint_13_69_w10 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 10 2 251901292881945131 = some 251901292881945131 := by decide +kernel
private theorem endpoint_13_69_p12 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 12 251901292881945131 = some 251901292881945131 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 10 2 251901292881945131 251901292881945131 251901292881945131 endpoint_13_69_p10 endpoint_13_69_w10
def endpoint_13_69 : CertifiedEndpoint :=
  ⟨⟨13, 69, 2352⟩, 251901292881945131, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_13_69_flag endpoint_13_69_sources 12 251901292881945131 251901292881945131 rfl endpoint_13_69_base endpoint_13_69_p12) (by decide)⟩
private def endpoint_13_70_flag : Flag := ⟨13, 70, 2269⟩
private def endpoint_13_70_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_13_70_base : receiptBase endpoint_13_70_flag endpoint_13_70_sources = some 246462037182034884 := by decide +kernel
private theorem endpoint_13_70_w0 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 2 246462037182034884 = some 246462037182034884 := by decide +kernel
private theorem endpoint_13_70_w2 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 2 2 246462037182034884 = some 246462037182034884 := by decide +kernel
private theorem endpoint_13_70_p4 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 4 246462037182034884 = some 246462037182034884 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 2 2 246462037182034884 246462037182034884 246462037182034884 endpoint_13_70_w0 endpoint_13_70_w2
private theorem endpoint_13_70_w4 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 4 2 246462037182034884 = some 246462037182034884 := by decide +kernel
private theorem endpoint_13_70_p6 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 6 246462037182034884 = some 246462037182034884 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 4 2 246462037182034884 246462037182034884 246462037182034884 endpoint_13_70_p4 endpoint_13_70_w4
private theorem endpoint_13_70_w6 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 6 2 246462037182034884 = some 246462037182034884 := by decide +kernel
private theorem endpoint_13_70_p8 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 8 246462037182034884 = some 246462037182034884 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 6 2 246462037182034884 246462037182034884 246462037182034884 endpoint_13_70_p6 endpoint_13_70_w6
private theorem endpoint_13_70_w8 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 8 2 246462037182034884 = some 246462037182034884 := by decide +kernel
private theorem endpoint_13_70_p10 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 10 246462037182034884 = some 246462037182034884 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 8 2 246462037182034884 246462037182034884 246462037182034884 endpoint_13_70_p8 endpoint_13_70_w8
private theorem endpoint_13_70_w10 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 10 2 246462037182034884 = some 246462037182034884 := by decide +kernel
private theorem endpoint_13_70_p12 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 12 246462037182034884 = some 246462037182034884 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 10 2 246462037182034884 246462037182034884 246462037182034884 endpoint_13_70_p10 endpoint_13_70_w10
def endpoint_13_70 : CertifiedEndpoint :=
  ⟨⟨13, 70, 2269⟩, 246462037182034884, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_13_70_flag endpoint_13_70_sources 12 246462037182034884 246462037182034884 rfl endpoint_13_70_base endpoint_13_70_p12) (by decide)⟩
private def endpoint_13_71_flag : Flag := ⟨13, 71, 2184⟩
private def endpoint_13_71_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_13_71_base : receiptBase endpoint_13_71_flag endpoint_13_71_sources = some 242004395409824301 := by decide +kernel
private theorem endpoint_13_71_w0 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 2 242004395409824301 = some 242004395409824301 := by decide +kernel
private theorem endpoint_13_71_w2 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 2 2 242004395409824301 = some 242004395409824301 := by decide +kernel
private theorem endpoint_13_71_p4 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 4 242004395409824301 = some 242004395409824301 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 2 2 242004395409824301 242004395409824301 242004395409824301 endpoint_13_71_w0 endpoint_13_71_w2
private theorem endpoint_13_71_w4 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 4 2 242004395409824301 = some 242004395409824301 := by decide +kernel
private theorem endpoint_13_71_p6 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 6 242004395409824301 = some 242004395409824301 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 4 2 242004395409824301 242004395409824301 242004395409824301 endpoint_13_71_p4 endpoint_13_71_w4
private theorem endpoint_13_71_w6 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 6 2 242004395409824301 = some 242004395409824301 := by decide +kernel
private theorem endpoint_13_71_p8 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 8 242004395409824301 = some 242004395409824301 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 6 2 242004395409824301 242004395409824301 242004395409824301 endpoint_13_71_p6 endpoint_13_71_w6
private theorem endpoint_13_71_w8 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 8 2 242004395409824301 = some 242004395409824301 := by decide +kernel
private theorem endpoint_13_71_p10 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 10 242004395409824301 = some 242004395409824301 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 8 2 242004395409824301 242004395409824301 242004395409824301 endpoint_13_71_p8 endpoint_13_71_w8
private theorem endpoint_13_71_w10 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 10 2 242004395409824301 = some 242004395409824301 := by decide +kernel
private theorem endpoint_13_71_p12 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 12 242004395409824301 = some 242004395409824301 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 10 2 242004395409824301 242004395409824301 242004395409824301 endpoint_13_71_p10 endpoint_13_71_w10
def endpoint_13_71 : CertifiedEndpoint :=
  ⟨⟨13, 71, 2184⟩, 242004395409824301, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_13_71_flag endpoint_13_71_sources 12 242004395409824301 242004395409824301 rfl endpoint_13_71_base endpoint_13_71_p12) (by decide)⟩
private def endpoint_13_72_flag : Flag := ⟨13, 72, 2095⟩
private def endpoint_13_72_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_13_72_base : receiptBase endpoint_13_72_flag endpoint_13_72_sources = some 235176608291859470 := by decide +kernel
private theorem endpoint_13_72_w0 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 2 235176608291859470 = some 235176608291859470 := by decide +kernel
private theorem endpoint_13_72_w2 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 2 2 235176608291859470 = some 235176608291859470 := by decide +kernel
private theorem endpoint_13_72_p4 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 4 235176608291859470 = some 235176608291859470 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 2 2 235176608291859470 235176608291859470 235176608291859470 endpoint_13_72_w0 endpoint_13_72_w2
private theorem endpoint_13_72_w4 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 4 2 235176608291859470 = some 235176608291859470 := by decide +kernel
private theorem endpoint_13_72_p6 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 6 235176608291859470 = some 235176608291859470 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 4 2 235176608291859470 235176608291859470 235176608291859470 endpoint_13_72_p4 endpoint_13_72_w4
private theorem endpoint_13_72_w6 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 6 2 235176608291859470 = some 235176608291859470 := by decide +kernel
private theorem endpoint_13_72_p8 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 8 235176608291859470 = some 235176608291859470 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 6 2 235176608291859470 235176608291859470 235176608291859470 endpoint_13_72_p6 endpoint_13_72_w6
private theorem endpoint_13_72_w8 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 8 2 235176608291859470 = some 235176608291859470 := by decide +kernel
private theorem endpoint_13_72_p10 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 10 235176608291859470 = some 235176608291859470 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 8 2 235176608291859470 235176608291859470 235176608291859470 endpoint_13_72_p8 endpoint_13_72_w8
private theorem endpoint_13_72_w10 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 10 2 235176608291859470 = some 235176608291859470 := by decide +kernel
private theorem endpoint_13_72_p12 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 12 235176608291859470 = some 235176608291859470 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 10 2 235176608291859470 235176608291859470 235176608291859470 endpoint_13_72_p10 endpoint_13_72_w10
def endpoint_13_72 : CertifiedEndpoint :=
  ⟨⟨13, 72, 2095⟩, 235176608291859470, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_13_72_flag endpoint_13_72_sources 12 235176608291859470 235176608291859470 rfl endpoint_13_72_base endpoint_13_72_p12) (by decide)⟩
private def endpoint_13_73_flag : Flag := ⟨13, 73, 2003⟩
private def endpoint_13_73_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_13_73_base : receiptBase endpoint_13_73_flag endpoint_13_73_sources = some 229484668422129814 := by decide +kernel
private theorem endpoint_13_73_w0 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 2 229484668422129814 = some 229484668422129814 := by decide +kernel
private theorem endpoint_13_73_w2 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 2 2 229484668422129814 = some 229484668422129814 := by decide +kernel
private theorem endpoint_13_73_p4 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 4 229484668422129814 = some 229484668422129814 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 2 2 229484668422129814 229484668422129814 229484668422129814 endpoint_13_73_w0 endpoint_13_73_w2
private theorem endpoint_13_73_w4 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 4 2 229484668422129814 = some 229484668422129814 := by decide +kernel
private theorem endpoint_13_73_p6 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 6 229484668422129814 = some 229484668422129814 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 4 2 229484668422129814 229484668422129814 229484668422129814 endpoint_13_73_p4 endpoint_13_73_w4
private theorem endpoint_13_73_w6 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 6 2 229484668422129814 = some 229484668422129814 := by decide +kernel
private theorem endpoint_13_73_p8 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 8 229484668422129814 = some 229484668422129814 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 6 2 229484668422129814 229484668422129814 229484668422129814 endpoint_13_73_p6 endpoint_13_73_w6
private theorem endpoint_13_73_w8 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 8 2 229484668422129814 = some 229484668422129814 := by decide +kernel
private theorem endpoint_13_73_p10 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 10 229484668422129814 = some 229484668422129814 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 8 2 229484668422129814 229484668422129814 229484668422129814 endpoint_13_73_p8 endpoint_13_73_w8
private theorem endpoint_13_73_w10 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 10 2 229484668422129814 = some 229484668422129814 := by decide +kernel
private theorem endpoint_13_73_p12 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 12 229484668422129814 = some 229484668422129814 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 10 2 229484668422129814 229484668422129814 229484668422129814 endpoint_13_73_p10 endpoint_13_73_w10
def endpoint_13_73 : CertifiedEndpoint :=
  ⟨⟨13, 73, 2003⟩, 229484668422129814, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_13_73_flag endpoint_13_73_sources 12 229484668422129814 229484668422129814 rfl endpoint_13_73_base endpoint_13_73_p12) (by decide)⟩
private def endpoint_13_74_flag : Flag := ⟨13, 74, 1909⟩
private def endpoint_13_74_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_13_74_base : receiptBase endpoint_13_74_flag endpoint_13_74_sources = some 221493880442394125 := by decide +kernel
private theorem endpoint_13_74_w0 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 2 221493880442394125 = some 221493880442394125 := by decide +kernel
private theorem endpoint_13_74_w2 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 2 2 221493880442394125 = some 221493880442394125 := by decide +kernel
private theorem endpoint_13_74_p4 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 4 221493880442394125 = some 221493880442394125 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 2 2 221493880442394125 221493880442394125 221493880442394125 endpoint_13_74_w0 endpoint_13_74_w2
private theorem endpoint_13_74_w4 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 4 2 221493880442394125 = some 221493880442394125 := by decide +kernel
private theorem endpoint_13_74_p6 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 6 221493880442394125 = some 221493880442394125 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 4 2 221493880442394125 221493880442394125 221493880442394125 endpoint_13_74_p4 endpoint_13_74_w4
private theorem endpoint_13_74_w6 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 6 2 221493880442394125 = some 221493880442394125 := by decide +kernel
private theorem endpoint_13_74_p8 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 8 221493880442394125 = some 221493880442394125 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 6 2 221493880442394125 221493880442394125 221493880442394125 endpoint_13_74_p6 endpoint_13_74_w6
private theorem endpoint_13_74_w8 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 8 2 221493880442394125 = some 221493880442394125 := by decide +kernel
private theorem endpoint_13_74_p10 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 10 221493880442394125 = some 221493880442394125 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 8 2 221493880442394125 221493880442394125 221493880442394125 endpoint_13_74_p8 endpoint_13_74_w8
private theorem endpoint_13_74_w10 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 10 2 221493880442394125 = some 221493880442394125 := by decide +kernel
private theorem endpoint_13_74_p12 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 12 221493880442394125 = some 221493880442394125 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 10 2 221493880442394125 221493880442394125 221493880442394125 endpoint_13_74_p10 endpoint_13_74_w10
def endpoint_13_74 : CertifiedEndpoint :=
  ⟨⟨13, 74, 1909⟩, 221493880442394125, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_13_74_flag endpoint_13_74_sources 12 221493880442394125 221493880442394125 rfl endpoint_13_74_base endpoint_13_74_p12) (by decide)⟩
private def endpoint_13_75_flag : Flag := ⟨13, 75, 1811⟩
private def endpoint_13_75_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_13_75_base : receiptBase endpoint_13_75_flag endpoint_13_75_sources = some 212776659866340697 := by decide +kernel
private theorem endpoint_13_75_w0 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 2 212776659866340697 = some 212776659866340697 := by decide +kernel
private theorem endpoint_13_75_w2 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 2 2 212776659866340697 = some 212776659866340697 := by decide +kernel
private theorem endpoint_13_75_p4 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 4 212776659866340697 = some 212776659866340697 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 2 2 212776659866340697 212776659866340697 212776659866340697 endpoint_13_75_w0 endpoint_13_75_w2
private theorem endpoint_13_75_w4 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 4 2 212776659866340697 = some 212776659866340697 := by decide +kernel
private theorem endpoint_13_75_p6 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 6 212776659866340697 = some 212776659866340697 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 4 2 212776659866340697 212776659866340697 212776659866340697 endpoint_13_75_p4 endpoint_13_75_w4
private theorem endpoint_13_75_w6 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 6 2 212776659866340697 = some 212776659866340697 := by decide +kernel
private theorem endpoint_13_75_p8 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 8 212776659866340697 = some 212776659866340697 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 6 2 212776659866340697 212776659866340697 212776659866340697 endpoint_13_75_p6 endpoint_13_75_w6
private theorem endpoint_13_75_w8 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 8 2 212776659866340697 = some 212776659866340697 := by decide +kernel
private theorem endpoint_13_75_p10 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 10 212776659866340697 = some 212776659866340697 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 8 2 212776659866340697 212776659866340697 212776659866340697 endpoint_13_75_p8 endpoint_13_75_w8
private theorem endpoint_13_75_w10 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 10 2 212776659866340697 = some 212776659866340697 := by decide +kernel
private theorem endpoint_13_75_p12 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 12 212776659866340697 = some 212776659866340697 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 10 2 212776659866340697 212776659866340697 212776659866340697 endpoint_13_75_p10 endpoint_13_75_w10
def endpoint_13_75 : CertifiedEndpoint :=
  ⟨⟨13, 75, 1811⟩, 212776659866340697, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_13_75_flag endpoint_13_75_sources 12 212776659866340697 212776659866340697 rfl endpoint_13_75_base endpoint_13_75_p12) (by decide)⟩
private def endpoint_13_76_flag : Flag := ⟨13, 76, 1710⟩
private def endpoint_13_76_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_13_76_base : receiptBase endpoint_13_76_flag endpoint_13_76_sources = some 206695227928584285 := by decide +kernel
private theorem endpoint_13_76_w0 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 2 206695227928584285 = some 206695227928584285 := by decide +kernel
private theorem endpoint_13_76_w2 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 2 2 206695227928584285 = some 206695227928584285 := by decide +kernel
private theorem endpoint_13_76_p4 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 4 206695227928584285 = some 206695227928584285 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 2 2 206695227928584285 206695227928584285 206695227928584285 endpoint_13_76_w0 endpoint_13_76_w2
private theorem endpoint_13_76_w4 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 4 2 206695227928584285 = some 206695227928584285 := by decide +kernel
private theorem endpoint_13_76_p6 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 6 206695227928584285 = some 206695227928584285 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 4 2 206695227928584285 206695227928584285 206695227928584285 endpoint_13_76_p4 endpoint_13_76_w4
private theorem endpoint_13_76_w6 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 6 2 206695227928584285 = some 206695227928584285 := by decide +kernel
private theorem endpoint_13_76_p8 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 8 206695227928584285 = some 206695227928584285 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 6 2 206695227928584285 206695227928584285 206695227928584285 endpoint_13_76_p6 endpoint_13_76_w6
private theorem endpoint_13_76_w8 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 8 2 206695227928584285 = some 206695227928584285 := by decide +kernel
private theorem endpoint_13_76_p10 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 10 206695227928584285 = some 206695227928584285 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 8 2 206695227928584285 206695227928584285 206695227928584285 endpoint_13_76_p8 endpoint_13_76_w8
private theorem endpoint_13_76_w10 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 10 2 206695227928584285 = some 206695227928584285 := by decide +kernel
private theorem endpoint_13_76_p12 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 12 206695227928584285 = some 206695227928584285 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 10 2 206695227928584285 206695227928584285 206695227928584285 endpoint_13_76_p10 endpoint_13_76_w10
def endpoint_13_76 : CertifiedEndpoint :=
  ⟨⟨13, 76, 1710⟩, 206695227928584285, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_13_76_flag endpoint_13_76_sources 12 206695227928584285 206695227928584285 rfl endpoint_13_76_base endpoint_13_76_p12) (by decide)⟩
private def endpoint_13_77_flag : Flag := ⟨13, 77, 1607⟩
private def endpoint_13_77_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_13_77_base : receiptBase endpoint_13_77_flag endpoint_13_77_sources = some 196610746990517919 := by decide +kernel
private theorem endpoint_13_77_w0 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 2 196610746990517919 = some 196610746990517919 := by decide +kernel
private theorem endpoint_13_77_w2 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 2 2 196610746990517919 = some 196610746990517919 := by decide +kernel
private theorem endpoint_13_77_p4 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 4 196610746990517919 = some 196610746990517919 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 2 2 196610746990517919 196610746990517919 196610746990517919 endpoint_13_77_w0 endpoint_13_77_w2
private theorem endpoint_13_77_w4 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 4 2 196610746990517919 = some 196610746990517919 := by decide +kernel
private theorem endpoint_13_77_p6 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 6 196610746990517919 = some 196610746990517919 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 4 2 196610746990517919 196610746990517919 196610746990517919 endpoint_13_77_p4 endpoint_13_77_w4
private theorem endpoint_13_77_w6 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 6 2 196610746990517919 = some 196610746990517919 := by decide +kernel
private theorem endpoint_13_77_p8 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 8 196610746990517919 = some 196610746990517919 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 6 2 196610746990517919 196610746990517919 196610746990517919 endpoint_13_77_p6 endpoint_13_77_w6
private theorem endpoint_13_77_w8 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 8 2 196610746990517919 = some 196610746990517919 := by decide +kernel
private theorem endpoint_13_77_p10 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 10 196610746990517919 = some 196610746990517919 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 8 2 196610746990517919 196610746990517919 196610746990517919 endpoint_13_77_p8 endpoint_13_77_w8
private theorem endpoint_13_77_w10 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 10 2 196610746990517919 = some 196610746990517919 := by decide +kernel
private theorem endpoint_13_77_p12 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 12 196610746990517919 = some 196610746990517919 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 10 2 196610746990517919 196610746990517919 196610746990517919 endpoint_13_77_p10 endpoint_13_77_w10
def endpoint_13_77 : CertifiedEndpoint :=
  ⟨⟨13, 77, 1607⟩, 196610746990517919, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_13_77_flag endpoint_13_77_sources 12 196610746990517919 196610746990517919 rfl endpoint_13_77_base endpoint_13_77_p12) (by decide)⟩
private def endpoint_13_78_flag : Flag := ⟨13, 78, 1500⟩
private def endpoint_13_78_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_13_78_base : receiptBase endpoint_13_78_flag endpoint_13_78_sources = some 186103882942922588 := by decide +kernel
private theorem endpoint_13_78_w0 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 2 186103882942922588 = some 186103882942922588 := by decide +kernel
private theorem endpoint_13_78_w2 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 2 2 186103882942922588 = some 186103882942922588 := by decide +kernel
private theorem endpoint_13_78_p4 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 4 186103882942922588 = some 186103882942922588 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 2 2 186103882942922588 186103882942922588 186103882942922588 endpoint_13_78_w0 endpoint_13_78_w2
private theorem endpoint_13_78_w4 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 4 2 186103882942922588 = some 186103882942922588 := by decide +kernel
private theorem endpoint_13_78_p6 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 6 186103882942922588 = some 186103882942922588 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 4 2 186103882942922588 186103882942922588 186103882942922588 endpoint_13_78_p4 endpoint_13_78_w4
private theorem endpoint_13_78_w6 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 6 2 186103882942922588 = some 186103882942922588 := by decide +kernel
private theorem endpoint_13_78_p8 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 8 186103882942922588 = some 186103882942922588 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 6 2 186103882942922588 186103882942922588 186103882942922588 endpoint_13_78_p6 endpoint_13_78_w6
private theorem endpoint_13_78_w8 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 8 2 186103882942922588 = some 186103882942922588 := by decide +kernel
private theorem endpoint_13_78_p10 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 10 186103882942922588 = some 186103882942922588 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 8 2 186103882942922588 186103882942922588 186103882942922588 endpoint_13_78_p8 endpoint_13_78_w8
private theorem endpoint_13_78_w10 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 10 2 186103882942922588 = some 186103882942922588 := by decide +kernel
private theorem endpoint_13_78_p12 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 12 186103882942922588 = some 186103882942922588 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 10 2 186103882942922588 186103882942922588 186103882942922588 endpoint_13_78_p10 endpoint_13_78_w10
def endpoint_13_78 : CertifiedEndpoint :=
  ⟨⟨13, 78, 1500⟩, 186103882942922588, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_13_78_flag endpoint_13_78_sources 12 186103882942922588 186103882942922588 rfl endpoint_13_78_base endpoint_13_78_p12) (by decide)⟩
private def endpoint_13_79_flag : Flag := ⟨13, 79, 1391⟩
private def endpoint_13_79_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_13_79_base : receiptBase endpoint_13_79_flag endpoint_13_79_sources = some 175708728334316842 := by decide +kernel
private theorem endpoint_13_79_w0 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 2 175708728334316842 = some 175708728334316842 := by decide +kernel
private theorem endpoint_13_79_w2 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 2 2 175708728334316842 = some 175708728334316842 := by decide +kernel
private theorem endpoint_13_79_p4 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 4 175708728334316842 = some 175708728334316842 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 2 2 175708728334316842 175708728334316842 175708728334316842 endpoint_13_79_w0 endpoint_13_79_w2
private theorem endpoint_13_79_w4 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 4 2 175708728334316842 = some 175708728334316842 := by decide +kernel
private theorem endpoint_13_79_p6 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 6 175708728334316842 = some 175708728334316842 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 4 2 175708728334316842 175708728334316842 175708728334316842 endpoint_13_79_p4 endpoint_13_79_w4
private theorem endpoint_13_79_w6 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 6 2 175708728334316842 = some 175708728334316842 := by decide +kernel
private theorem endpoint_13_79_p8 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 8 175708728334316842 = some 175708728334316842 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 6 2 175708728334316842 175708728334316842 175708728334316842 endpoint_13_79_p6 endpoint_13_79_w6
private theorem endpoint_13_79_w8 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 8 2 175708728334316842 = some 175708728334316842 := by decide +kernel
private theorem endpoint_13_79_p10 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 10 175708728334316842 = some 175708728334316842 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 8 2 175708728334316842 175708728334316842 175708728334316842 endpoint_13_79_p8 endpoint_13_79_w8
private theorem endpoint_13_79_w10 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 10 2 175708728334316842 = some 175708728334316842 := by decide +kernel
private theorem endpoint_13_79_p12 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 12 175708728334316842 = some 175708728334316842 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 10 2 175708728334316842 175708728334316842 175708728334316842 endpoint_13_79_p10 endpoint_13_79_w10
def endpoint_13_79 : CertifiedEndpoint :=
  ⟨⟨13, 79, 1391⟩, 175708728334316842, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_13_79_flag endpoint_13_79_sources 12 175708728334316842 175708728334316842 rfl endpoint_13_79_base endpoint_13_79_p12) (by decide)⟩
private def endpoint_13_80_flag : Flag := ⟨13, 80, 1278⟩
private def endpoint_13_80_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_13_80_base : receiptBase endpoint_13_80_flag endpoint_13_80_sources = some 163420556258065751 := by decide +kernel
private theorem endpoint_13_80_w0 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 2 163420556258065751 = some 163420556258065751 := by decide +kernel
private theorem endpoint_13_80_w2 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 2 2 163420556258065751 = some 163420556258065751 := by decide +kernel
private theorem endpoint_13_80_p4 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 4 163420556258065751 = some 163420556258065751 :=
  join_receipt_window endpoint_13_80_flag endpoint_13_80_sources 0 2 2 163420556258065751 163420556258065751 163420556258065751 endpoint_13_80_w0 endpoint_13_80_w2
private theorem endpoint_13_80_w4 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 4 2 163420556258065751 = some 163420556258065751 := by decide +kernel
private theorem endpoint_13_80_p6 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 6 163420556258065751 = some 163420556258065751 :=
  join_receipt_window endpoint_13_80_flag endpoint_13_80_sources 0 4 2 163420556258065751 163420556258065751 163420556258065751 endpoint_13_80_p4 endpoint_13_80_w4
private theorem endpoint_13_80_w6 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 6 2 163420556258065751 = some 163420556258065751 := by decide +kernel
private theorem endpoint_13_80_p8 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 8 163420556258065751 = some 163420556258065751 :=
  join_receipt_window endpoint_13_80_flag endpoint_13_80_sources 0 6 2 163420556258065751 163420556258065751 163420556258065751 endpoint_13_80_p6 endpoint_13_80_w6
private theorem endpoint_13_80_w8 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 8 2 163420556258065751 = some 163420556258065751 := by decide +kernel
private theorem endpoint_13_80_p10 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 10 163420556258065751 = some 163420556258065751 :=
  join_receipt_window endpoint_13_80_flag endpoint_13_80_sources 0 8 2 163420556258065751 163420556258065751 163420556258065751 endpoint_13_80_p8 endpoint_13_80_w8
private theorem endpoint_13_80_w10 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 10 2 163420556258065751 = some 163420556258065751 := by decide +kernel
private theorem endpoint_13_80_p12 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 12 163420556258065751 = some 163420556258065751 :=
  join_receipt_window endpoint_13_80_flag endpoint_13_80_sources 0 10 2 163420556258065751 163420556258065751 163420556258065751 endpoint_13_80_p10 endpoint_13_80_w10
def endpoint_13_80 : CertifiedEndpoint :=
  ⟨⟨13, 80, 1278⟩, 163420556258065751, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_13_80_flag endpoint_13_80_sources 12 163420556258065751 163420556258065751 rfl endpoint_13_80_base endpoint_13_80_p12) (by decide)⟩
private def endpoint_13_81_flag : Flag := ⟨13, 81, 1163⟩
private def endpoint_13_81_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_13_81_base : receiptBase endpoint_13_81_flag endpoint_13_81_sources = some 150554969163175380 := by decide +kernel
private theorem endpoint_13_81_w0 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 2 150554969163175380 = some 150554969163175380 := by decide +kernel
private theorem endpoint_13_81_w2 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 2 2 150554969163175380 = some 150554969163175380 := by decide +kernel
private theorem endpoint_13_81_p4 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 4 150554969163175380 = some 150554969163175380 :=
  join_receipt_window endpoint_13_81_flag endpoint_13_81_sources 0 2 2 150554969163175380 150554969163175380 150554969163175380 endpoint_13_81_w0 endpoint_13_81_w2
private theorem endpoint_13_81_w4 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 4 2 150554969163175380 = some 150554969163175380 := by decide +kernel
private theorem endpoint_13_81_p6 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 6 150554969163175380 = some 150554969163175380 :=
  join_receipt_window endpoint_13_81_flag endpoint_13_81_sources 0 4 2 150554969163175380 150554969163175380 150554969163175380 endpoint_13_81_p4 endpoint_13_81_w4
private theorem endpoint_13_81_w6 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 6 2 150554969163175380 = some 150554969163175380 := by decide +kernel
private theorem endpoint_13_81_p8 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 8 150554969163175380 = some 150554969163175380 :=
  join_receipt_window endpoint_13_81_flag endpoint_13_81_sources 0 6 2 150554969163175380 150554969163175380 150554969163175380 endpoint_13_81_p6 endpoint_13_81_w6
private theorem endpoint_13_81_w8 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 8 2 150554969163175380 = some 150554969163175380 := by decide +kernel
private theorem endpoint_13_81_p10 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 10 150554969163175380 = some 150554969163175380 :=
  join_receipt_window endpoint_13_81_flag endpoint_13_81_sources 0 8 2 150554969163175380 150554969163175380 150554969163175380 endpoint_13_81_p8 endpoint_13_81_w8
private theorem endpoint_13_81_w10 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 10 2 150554969163175380 = some 150554969163175380 := by decide +kernel
private theorem endpoint_13_81_p12 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 12 150554969163175380 = some 150554969163175380 :=
  join_receipt_window endpoint_13_81_flag endpoint_13_81_sources 0 10 2 150554969163175380 150554969163175380 150554969163175380 endpoint_13_81_p10 endpoint_13_81_w10
def endpoint_13_81 : CertifiedEndpoint :=
  ⟨⟨13, 81, 1163⟩, 150554969163175380, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_13_81_flag endpoint_13_81_sources 12 150554969163175380 150554969163175380 rfl endpoint_13_81_base endpoint_13_81_p12) (by decide)⟩
def endpoint_13_82 : CertifiedEndpoint :=
  ⟨⟨13, 82, 1044⟩, 242151123045013452, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_83 : CertifiedEndpoint :=
  ⟨⟨13, 83, 922⟩, 215308019791667829, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_84 : CertifiedEndpoint :=
  ⟨⟨13, 84, 797⟩, 186927460155619325, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_85 : CertifiedEndpoint :=
  ⟨⟨13, 85, 669⟩, 156980375072720826, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_86 : CertifiedEndpoint :=
  ⟨⟨13, 86, 539⟩, 125692865890423947, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_87 : CertifiedEndpoint :=
  ⟨⟨13, 87, 404⟩, 92270352309785387, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_88 : CertifiedEndpoint :=
  ⟨⟨13, 88, 267⟩, 57449276501454219, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_89 : CertifiedEndpoint :=
  ⟨⟨13, 89, 127⟩, 20945398989684600, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_14 : CertifiedEndpoint :=
  ⟨⟨14, 14, 4415⟩, 120545570328725107, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_15 : CertifiedEndpoint :=
  ⟨⟨14, 15, 4391⟩, 124887126344178136, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_16 : CertifiedEndpoint :=
  ⟨⟨14, 16, 4366⟩, 129144189604149986, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_17 : CertifiedEndpoint :=
  ⟨⟨14, 17, 4342⟩, 143518127329520911, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_18 : CertifiedEndpoint :=
  ⟨⟨14, 18, 4317⟩, 157684544205203287, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_19 : CertifiedEndpoint :=
  ⟨⟨14, 19, 4292⟩, 171673093463260165, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_20 : CertifiedEndpoint :=
  ⟨⟨14, 20, 4266⟩, 185440171470246102, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_21 : CertifiedEndpoint :=
  ⟨⟨14, 21, 4240⟩, 199022406658915345, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_22 : CertifiedEndpoint :=
  ⟨⟨14, 22, 4214⟩, 212419799029267894, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_23 : CertifiedEndpoint :=
  ⟨⟨14, 23, 4188⟩, 225632348581303749, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_24 : CertifiedEndpoint :=
  ⟨⟨14, 24, 4161⟩, 238602501280195075, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_25 : CertifiedEndpoint :=
  ⟨⟨14, 25, 4134⟩, 251380835960078511, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_26 : CertifiedEndpoint :=
  ⟨⟨14, 26, 4107⟩, 263967352620954057, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_14_27_flag : Flag := ⟨14, 27, 4079⟩
private def endpoint_14_27_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_27_base : receiptBase endpoint_14_27_flag endpoint_14_27_sources = some 191574528668998980 := by decide +kernel
private theorem endpoint_14_27_w0 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 0 2 191574528668998980 = some 191574528668998980 := by decide +kernel
private theorem endpoint_14_27_w2 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 2 2 191574528668998980 = some 191574528668998980 := by decide +kernel
private theorem endpoint_14_27_p4 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 0 4 191574528668998980 = some 191574528668998980 :=
  join_receipt_window endpoint_14_27_flag endpoint_14_27_sources 0 2 2 191574528668998980 191574528668998980 191574528668998980 endpoint_14_27_w0 endpoint_14_27_w2
private theorem endpoint_14_27_w4 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 4 2 191574528668998980 = some 191574528668998980 := by decide +kernel
private theorem endpoint_14_27_p6 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 0 6 191574528668998980 = some 191574528668998980 :=
  join_receipt_window endpoint_14_27_flag endpoint_14_27_sources 0 4 2 191574528668998980 191574528668998980 191574528668998980 endpoint_14_27_p4 endpoint_14_27_w4
private theorem endpoint_14_27_w6 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 6 2 191574528668998980 = some 191574528668998980 := by decide +kernel
private theorem endpoint_14_27_p8 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 0 8 191574528668998980 = some 191574528668998980 :=
  join_receipt_window endpoint_14_27_flag endpoint_14_27_sources 0 6 2 191574528668998980 191574528668998980 191574528668998980 endpoint_14_27_p6 endpoint_14_27_w6
private theorem endpoint_14_27_w8 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 8 2 191574528668998980 = some 191574528668998980 := by decide +kernel
private theorem endpoint_14_27_p10 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 0 10 191574528668998980 = some 191574528668998980 :=
  join_receipt_window endpoint_14_27_flag endpoint_14_27_sources 0 8 2 191574528668998980 191574528668998980 191574528668998980 endpoint_14_27_p8 endpoint_14_27_w8
private theorem endpoint_14_27_w10 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 10 2 191574528668998980 = some 191574528668998980 := by decide +kernel
private theorem endpoint_14_27_p12 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 0 12 191574528668998980 = some 191574528668998980 :=
  join_receipt_window endpoint_14_27_flag endpoint_14_27_sources 0 10 2 191574528668998980 191574528668998980 191574528668998980 endpoint_14_27_p10 endpoint_14_27_w10
private theorem endpoint_14_27_w12 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 12 1 191574528668998980 = some 191574528668998980 := by decide +kernel
private theorem endpoint_14_27_p13 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 0 13 191574528668998980 = some 191574528668998980 :=
  join_receipt_window endpoint_14_27_flag endpoint_14_27_sources 0 12 1 191574528668998980 191574528668998980 191574528668998980 endpoint_14_27_p12 endpoint_14_27_w12
def endpoint_14_27 : CertifiedEndpoint :=
  ⟨⟨14, 27, 4079⟩, 191574528668998980, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_27_flag endpoint_14_27_sources 13 191574528668998980 191574528668998980 rfl endpoint_14_27_base endpoint_14_27_p13) (by decide)⟩
private def endpoint_14_28_flag : Flag := ⟨14, 28, 4051⟩
private def endpoint_14_28_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_28_base : receiptBase endpoint_14_28_flag endpoint_14_28_sources = some 195969221824666505 := by decide +kernel
private theorem endpoint_14_28_w0 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 2 195969221824666505 = some 195969221824666505 := by decide +kernel
private theorem endpoint_14_28_w2 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 2 2 195969221824666505 = some 195969221824666505 := by decide +kernel
private theorem endpoint_14_28_p4 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 4 195969221824666505 = some 195969221824666505 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 2 2 195969221824666505 195969221824666505 195969221824666505 endpoint_14_28_w0 endpoint_14_28_w2
private theorem endpoint_14_28_w4 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 4 2 195969221824666505 = some 195969221824666505 := by decide +kernel
private theorem endpoint_14_28_p6 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 6 195969221824666505 = some 195969221824666505 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 4 2 195969221824666505 195969221824666505 195969221824666505 endpoint_14_28_p4 endpoint_14_28_w4
private theorem endpoint_14_28_w6 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 6 2 195969221824666505 = some 195969221824666505 := by decide +kernel
private theorem endpoint_14_28_p8 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 8 195969221824666505 = some 195969221824666505 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 6 2 195969221824666505 195969221824666505 195969221824666505 endpoint_14_28_p6 endpoint_14_28_w6
private theorem endpoint_14_28_w8 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 8 2 195969221824666505 = some 195969221824666505 := by decide +kernel
private theorem endpoint_14_28_p10 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 10 195969221824666505 = some 195969221824666505 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 8 2 195969221824666505 195969221824666505 195969221824666505 endpoint_14_28_p8 endpoint_14_28_w8
private theorem endpoint_14_28_w10 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 10 2 195969221824666505 = some 195969221824666505 := by decide +kernel
private theorem endpoint_14_28_p12 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 12 195969221824666505 = some 195969221824666505 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 10 2 195969221824666505 195969221824666505 195969221824666505 endpoint_14_28_p10 endpoint_14_28_w10
private theorem endpoint_14_28_w12 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 12 1 195969221824666505 = some 195969221824666505 := by decide +kernel
private theorem endpoint_14_28_p13 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 13 195969221824666505 = some 195969221824666505 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 12 1 195969221824666505 195969221824666505 195969221824666505 endpoint_14_28_p12 endpoint_14_28_w12
def endpoint_14_28 : CertifiedEndpoint :=
  ⟨⟨14, 28, 4051⟩, 195969221824666505, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_28_flag endpoint_14_28_sources 13 195969221824666505 195969221824666505 rfl endpoint_14_28_base endpoint_14_28_p13) (by decide)⟩
private def endpoint_14_29_flag : Flag := ⟨14, 29, 4022⟩
private def endpoint_14_29_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_29_base : receiptBase endpoint_14_29_flag endpoint_14_29_sources = some 200236466203242155 := by decide +kernel
private theorem endpoint_14_29_w0 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 2 200236466203242155 = some 200236466203242155 := by decide +kernel
private theorem endpoint_14_29_w2 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 2 2 200236466203242155 = some 200236466203242155 := by decide +kernel
private theorem endpoint_14_29_p4 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 4 200236466203242155 = some 200236466203242155 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 2 2 200236466203242155 200236466203242155 200236466203242155 endpoint_14_29_w0 endpoint_14_29_w2
private theorem endpoint_14_29_w4 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 4 2 200236466203242155 = some 200236466203242155 := by decide +kernel
private theorem endpoint_14_29_p6 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 6 200236466203242155 = some 200236466203242155 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 4 2 200236466203242155 200236466203242155 200236466203242155 endpoint_14_29_p4 endpoint_14_29_w4
private theorem endpoint_14_29_w6 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 6 2 200236466203242155 = some 200236466203242155 := by decide +kernel
private theorem endpoint_14_29_p8 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 8 200236466203242155 = some 200236466203242155 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 6 2 200236466203242155 200236466203242155 200236466203242155 endpoint_14_29_p6 endpoint_14_29_w6
private theorem endpoint_14_29_w8 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 8 2 200236466203242155 = some 200236466203242155 := by decide +kernel
private theorem endpoint_14_29_p10 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 10 200236466203242155 = some 200236466203242155 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 8 2 200236466203242155 200236466203242155 200236466203242155 endpoint_14_29_p8 endpoint_14_29_w8
private theorem endpoint_14_29_w10 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 10 2 200236466203242155 = some 200236466203242155 := by decide +kernel
private theorem endpoint_14_29_p12 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 12 200236466203242155 = some 200236466203242155 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 10 2 200236466203242155 200236466203242155 200236466203242155 endpoint_14_29_p10 endpoint_14_29_w10
private theorem endpoint_14_29_w12 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 12 1 200236466203242155 = some 200236466203242155 := by decide +kernel
private theorem endpoint_14_29_p13 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 13 200236466203242155 = some 200236466203242155 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 12 1 200236466203242155 200236466203242155 200236466203242155 endpoint_14_29_p12 endpoint_14_29_w12
def endpoint_14_29 : CertifiedEndpoint :=
  ⟨⟨14, 29, 4022⟩, 200236466203242155, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_29_flag endpoint_14_29_sources 13 200236466203242155 200236466203242155 rfl endpoint_14_29_base endpoint_14_29_p13) (by decide)⟩
private def endpoint_14_30_flag : Flag := ⟨14, 30, 3993⟩
private def endpoint_14_30_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_30_base : receiptBase endpoint_14_30_flag endpoint_14_30_sources = some 204422603110904733 := by decide +kernel
private theorem endpoint_14_30_w0 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 2 204422603110904733 = some 204422603110904733 := by decide +kernel
private theorem endpoint_14_30_w2 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 2 2 204422603110904733 = some 204422603110904733 := by decide +kernel
private theorem endpoint_14_30_p4 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 4 204422603110904733 = some 204422603110904733 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 2 2 204422603110904733 204422603110904733 204422603110904733 endpoint_14_30_w0 endpoint_14_30_w2
private theorem endpoint_14_30_w4 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 4 2 204422603110904733 = some 204422603110904733 := by decide +kernel
private theorem endpoint_14_30_p6 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 6 204422603110904733 = some 204422603110904733 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 4 2 204422603110904733 204422603110904733 204422603110904733 endpoint_14_30_p4 endpoint_14_30_w4
private theorem endpoint_14_30_w6 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 6 2 204422603110904733 = some 204422603110904733 := by decide +kernel
private theorem endpoint_14_30_p8 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 8 204422603110904733 = some 204422603110904733 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 6 2 204422603110904733 204422603110904733 204422603110904733 endpoint_14_30_p6 endpoint_14_30_w6
private theorem endpoint_14_30_w8 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 8 2 204422603110904733 = some 204422603110904733 := by decide +kernel
private theorem endpoint_14_30_p10 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 10 204422603110904733 = some 204422603110904733 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 8 2 204422603110904733 204422603110904733 204422603110904733 endpoint_14_30_p8 endpoint_14_30_w8
private theorem endpoint_14_30_w10 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 10 2 204422603110904733 = some 204422603110904733 := by decide +kernel
private theorem endpoint_14_30_p12 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 12 204422603110904733 = some 204422603110904733 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 10 2 204422603110904733 204422603110904733 204422603110904733 endpoint_14_30_p10 endpoint_14_30_w10
private theorem endpoint_14_30_w12 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 12 1 204422603110904733 = some 204422603110904733 := by decide +kernel
private theorem endpoint_14_30_p13 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 13 204422603110904733 = some 204422603110904733 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 12 1 204422603110904733 204422603110904733 204422603110904733 endpoint_14_30_p12 endpoint_14_30_w12
def endpoint_14_30 : CertifiedEndpoint :=
  ⟨⟨14, 30, 3993⟩, 204422603110904733, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_30_flag endpoint_14_30_sources 13 204422603110904733 204422603110904733 rfl endpoint_14_30_base endpoint_14_30_p13) (by decide)⟩
private def endpoint_14_31_flag : Flag := ⟨14, 31, 3964⟩
private def endpoint_14_31_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_31_base : receiptBase endpoint_14_31_flag endpoint_14_31_sources = some 208527632547654236 := by decide +kernel
private theorem endpoint_14_31_w0 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 2 208527632547654236 = some 208527632547654236 := by decide +kernel
private theorem endpoint_14_31_w2 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 2 2 208527632547654236 = some 208527632547654236 := by decide +kernel
private theorem endpoint_14_31_p4 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 4 208527632547654236 = some 208527632547654236 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 2 2 208527632547654236 208527632547654236 208527632547654236 endpoint_14_31_w0 endpoint_14_31_w2
private theorem endpoint_14_31_w4 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 4 2 208527632547654236 = some 208527632547654236 := by decide +kernel
private theorem endpoint_14_31_p6 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 6 208527632547654236 = some 208527632547654236 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 4 2 208527632547654236 208527632547654236 208527632547654236 endpoint_14_31_p4 endpoint_14_31_w4
private theorem endpoint_14_31_w6 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 6 2 208527632547654236 = some 208527632547654236 := by decide +kernel
private theorem endpoint_14_31_p8 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 8 208527632547654236 = some 208527632547654236 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 6 2 208527632547654236 208527632547654236 208527632547654236 endpoint_14_31_p6 endpoint_14_31_w6
private theorem endpoint_14_31_w8 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 8 2 208527632547654236 = some 208527632547654236 := by decide +kernel
private theorem endpoint_14_31_p10 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 10 208527632547654236 = some 208527632547654236 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 8 2 208527632547654236 208527632547654236 208527632547654236 endpoint_14_31_p8 endpoint_14_31_w8
private theorem endpoint_14_31_w10 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 10 2 208527632547654236 = some 208527632547654236 := by decide +kernel
private theorem endpoint_14_31_p12 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 12 208527632547654236 = some 208527632547654236 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 10 2 208527632547654236 208527632547654236 208527632547654236 endpoint_14_31_p10 endpoint_14_31_w10
private theorem endpoint_14_31_w12 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 12 1 208527632547654236 = some 208527632547654236 := by decide +kernel
private theorem endpoint_14_31_p13 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 13 208527632547654236 = some 208527632547654236 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 12 1 208527632547654236 208527632547654236 208527632547654236 endpoint_14_31_p12 endpoint_14_31_w12
def endpoint_14_31 : CertifiedEndpoint :=
  ⟨⟨14, 31, 3964⟩, 208527632547654236, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_31_flag endpoint_14_31_sources 13 208527632547654236 208527632547654236 rfl endpoint_14_31_base endpoint_14_31_p13) (by decide)⟩
private def endpoint_14_32_flag : Flag := ⟨14, 32, 3934⟩
private def endpoint_14_32_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_32_base : receiptBase endpoint_14_32_flag endpoint_14_32_sources = some 212498341408778773 := by decide +kernel
private theorem endpoint_14_32_w0 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 2 212498341408778773 = some 212498341408778773 := by decide +kernel
private theorem endpoint_14_32_w2 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 2 2 212498341408778773 = some 212498341408778773 := by decide +kernel
private theorem endpoint_14_32_p4 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 4 212498341408778773 = some 212498341408778773 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 2 2 212498341408778773 212498341408778773 212498341408778773 endpoint_14_32_w0 endpoint_14_32_w2
private theorem endpoint_14_32_w4 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 4 2 212498341408778773 = some 212498341408778773 := by decide +kernel
private theorem endpoint_14_32_p6 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 6 212498341408778773 = some 212498341408778773 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 4 2 212498341408778773 212498341408778773 212498341408778773 endpoint_14_32_p4 endpoint_14_32_w4
private theorem endpoint_14_32_w6 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 6 2 212498341408778773 = some 212498341408778773 := by decide +kernel
private theorem endpoint_14_32_p8 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 8 212498341408778773 = some 212498341408778773 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 6 2 212498341408778773 212498341408778773 212498341408778773 endpoint_14_32_p6 endpoint_14_32_w6
private theorem endpoint_14_32_w8 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 8 2 212498341408778773 = some 212498341408778773 := by decide +kernel
private theorem endpoint_14_32_p10 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 10 212498341408778773 = some 212498341408778773 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 8 2 212498341408778773 212498341408778773 212498341408778773 endpoint_14_32_p8 endpoint_14_32_w8
private theorem endpoint_14_32_w10 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 10 2 212498341408778773 = some 212498341408778773 := by decide +kernel
private theorem endpoint_14_32_p12 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 12 212498341408778773 = some 212498341408778773 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 10 2 212498341408778773 212498341408778773 212498341408778773 endpoint_14_32_p10 endpoint_14_32_w10
private theorem endpoint_14_32_w12 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 12 1 212498341408778773 = some 212498341408778773 := by decide +kernel
private theorem endpoint_14_32_p13 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 13 212498341408778773 = some 212498341408778773 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 12 1 212498341408778773 212498341408778773 212498341408778773 endpoint_14_32_p12 endpoint_14_32_w12
def endpoint_14_32 : CertifiedEndpoint :=
  ⟨⟨14, 32, 3934⟩, 212498341408778773, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_32_flag endpoint_14_32_sources 13 212498341408778773 212498341408778773 rfl endpoint_14_32_base endpoint_14_32_p13) (by decide)⟩
private def endpoint_14_33_flag : Flag := ⟨14, 33, 3903⟩
private def endpoint_14_33_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_33_base : receiptBase endpoint_14_33_flag endpoint_14_33_sources = some 216330606615158487 := by decide +kernel
private theorem endpoint_14_33_w0 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 2 216330606615158487 = some 216330606615158487 := by decide +kernel
private theorem endpoint_14_33_w2 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 2 2 216330606615158487 = some 216330606615158487 := by decide +kernel
private theorem endpoint_14_33_p4 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 4 216330606615158487 = some 216330606615158487 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 2 2 216330606615158487 216330606615158487 216330606615158487 endpoint_14_33_w0 endpoint_14_33_w2
private theorem endpoint_14_33_w4 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 4 2 216330606615158487 = some 216330606615158487 := by decide +kernel
private theorem endpoint_14_33_p6 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 6 216330606615158487 = some 216330606615158487 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 4 2 216330606615158487 216330606615158487 216330606615158487 endpoint_14_33_p4 endpoint_14_33_w4
private theorem endpoint_14_33_w6 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 6 2 216330606615158487 = some 216330606615158487 := by decide +kernel
private theorem endpoint_14_33_p8 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 8 216330606615158487 = some 216330606615158487 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 6 2 216330606615158487 216330606615158487 216330606615158487 endpoint_14_33_p6 endpoint_14_33_w6
private theorem endpoint_14_33_w8 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 8 2 216330606615158487 = some 216330606615158487 := by decide +kernel
private theorem endpoint_14_33_p10 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 10 216330606615158487 = some 216330606615158487 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 8 2 216330606615158487 216330606615158487 216330606615158487 endpoint_14_33_p8 endpoint_14_33_w8
private theorem endpoint_14_33_w10 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 10 2 216330606615158487 = some 216330606615158487 := by decide +kernel
private theorem endpoint_14_33_p12 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 12 216330606615158487 = some 216330606615158487 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 10 2 216330606615158487 216330606615158487 216330606615158487 endpoint_14_33_p10 endpoint_14_33_w10
private theorem endpoint_14_33_w12 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 12 1 216330606615158487 = some 216330606615158487 := by decide +kernel
private theorem endpoint_14_33_p13 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 13 216330606615158487 = some 216330606615158487 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 12 1 216330606615158487 216330606615158487 216330606615158487 endpoint_14_33_p12 endpoint_14_33_w12
def endpoint_14_33 : CertifiedEndpoint :=
  ⟨⟨14, 33, 3903⟩, 216330606615158487, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_33_flag endpoint_14_33_sources 13 216330606615158487 216330606615158487 rfl endpoint_14_33_base endpoint_14_33_p13) (by decide)⟩
private def endpoint_14_34_flag : Flag := ⟨14, 34, 3872⟩
private def endpoint_14_34_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_34_base : receiptBase endpoint_14_34_flag endpoint_14_34_sources = some 221430673865585090 := by decide +kernel
private theorem endpoint_14_34_w0 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 2 221430673865585090 = some 221430673865585090 := by decide +kernel
private theorem endpoint_14_34_w2 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 2 2 221430673865585090 = some 221430673865585090 := by decide +kernel
private theorem endpoint_14_34_p4 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 4 221430673865585090 = some 221430673865585090 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 2 2 221430673865585090 221430673865585090 221430673865585090 endpoint_14_34_w0 endpoint_14_34_w2
private theorem endpoint_14_34_w4 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 4 2 221430673865585090 = some 221430673865585090 := by decide +kernel
private theorem endpoint_14_34_p6 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 6 221430673865585090 = some 221430673865585090 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 4 2 221430673865585090 221430673865585090 221430673865585090 endpoint_14_34_p4 endpoint_14_34_w4
private theorem endpoint_14_34_w6 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 6 2 221430673865585090 = some 221430673865585090 := by decide +kernel
private theorem endpoint_14_34_p8 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 8 221430673865585090 = some 221430673865585090 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 6 2 221430673865585090 221430673865585090 221430673865585090 endpoint_14_34_p6 endpoint_14_34_w6
private theorem endpoint_14_34_w8 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 8 2 221430673865585090 = some 221430673865585090 := by decide +kernel
private theorem endpoint_14_34_p10 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 10 221430673865585090 = some 221430673865585090 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 8 2 221430673865585090 221430673865585090 221430673865585090 endpoint_14_34_p8 endpoint_14_34_w8
private theorem endpoint_14_34_w10 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 10 2 221430673865585090 = some 221430673865585090 := by decide +kernel
private theorem endpoint_14_34_p12 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 12 221430673865585090 = some 221430673865585090 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 10 2 221430673865585090 221430673865585090 221430673865585090 endpoint_14_34_p10 endpoint_14_34_w10
private theorem endpoint_14_34_w12 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 12 1 221430673865585090 = some 221430673865585090 := by decide +kernel
private theorem endpoint_14_34_p13 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 13 221430673865585090 = some 221430673865585090 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 12 1 221430673865585090 221430673865585090 221430673865585090 endpoint_14_34_p12 endpoint_14_34_w12
def endpoint_14_34 : CertifiedEndpoint :=
  ⟨⟨14, 34, 3872⟩, 221430673865585090, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_34_flag endpoint_14_34_sources 13 221430673865585090 221430673865585090 rfl endpoint_14_34_base endpoint_14_34_p13) (by decide)⟩
private def endpoint_14_35_flag : Flag := ⟨14, 35, 3841⟩
private def endpoint_14_35_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_35_base : receiptBase endpoint_14_35_flag endpoint_14_35_sources = some 225005128572815769 := by decide +kernel
private theorem endpoint_14_35_w0 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 2 225005128572815769 = some 225005128572815769 := by decide +kernel
private theorem endpoint_14_35_w2 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 2 2 225005128572815769 = some 225005128572815769 := by decide +kernel
private theorem endpoint_14_35_p4 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 4 225005128572815769 = some 225005128572815769 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 2 2 225005128572815769 225005128572815769 225005128572815769 endpoint_14_35_w0 endpoint_14_35_w2
private theorem endpoint_14_35_w4 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 4 2 225005128572815769 = some 225005128572815769 := by decide +kernel
private theorem endpoint_14_35_p6 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 6 225005128572815769 = some 225005128572815769 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 4 2 225005128572815769 225005128572815769 225005128572815769 endpoint_14_35_p4 endpoint_14_35_w4
private theorem endpoint_14_35_w6 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 6 2 225005128572815769 = some 225005128572815769 := by decide +kernel
private theorem endpoint_14_35_p8 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 8 225005128572815769 = some 225005128572815769 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 6 2 225005128572815769 225005128572815769 225005128572815769 endpoint_14_35_p6 endpoint_14_35_w6
private theorem endpoint_14_35_w8 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 8 2 225005128572815769 = some 225005128572815769 := by decide +kernel
private theorem endpoint_14_35_p10 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 10 225005128572815769 = some 225005128572815769 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 8 2 225005128572815769 225005128572815769 225005128572815769 endpoint_14_35_p8 endpoint_14_35_w8
private theorem endpoint_14_35_w10 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 10 2 225005128572815769 = some 225005128572815769 := by decide +kernel
private theorem endpoint_14_35_p12 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 12 225005128572815769 = some 225005128572815769 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 10 2 225005128572815769 225005128572815769 225005128572815769 endpoint_14_35_p10 endpoint_14_35_w10
private theorem endpoint_14_35_w12 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 12 1 225005128572815769 = some 225005128572815769 := by decide +kernel
private theorem endpoint_14_35_p13 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 13 225005128572815769 = some 225005128572815769 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 12 1 225005128572815769 225005128572815769 225005128572815769 endpoint_14_35_p12 endpoint_14_35_w12
def endpoint_14_35 : CertifiedEndpoint :=
  ⟨⟨14, 35, 3841⟩, 225005128572815769, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_35_flag endpoint_14_35_sources 13 225005128572815769 225005128572815769 rfl endpoint_14_35_base endpoint_14_35_p13) (by decide)⟩
private def endpoint_14_36_flag : Flag := ⟨14, 36, 3809⟩
private def endpoint_14_36_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_36_base : receiptBase endpoint_14_36_flag endpoint_14_36_sources = some 228434862489459828 := by decide +kernel
private theorem endpoint_14_36_w0 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 2 228434862489459828 = some 228434862489459828 := by decide +kernel
private theorem endpoint_14_36_w2 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 2 2 228434862489459828 = some 228434862489459828 := by decide +kernel
private theorem endpoint_14_36_p4 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 4 228434862489459828 = some 228434862489459828 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 2 2 228434862489459828 228434862489459828 228434862489459828 endpoint_14_36_w0 endpoint_14_36_w2
private theorem endpoint_14_36_w4 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 4 2 228434862489459828 = some 228434862489459828 := by decide +kernel
private theorem endpoint_14_36_p6 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 6 228434862489459828 = some 228434862489459828 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 4 2 228434862489459828 228434862489459828 228434862489459828 endpoint_14_36_p4 endpoint_14_36_w4
private theorem endpoint_14_36_w6 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 6 2 228434862489459828 = some 228434862489459828 := by decide +kernel
private theorem endpoint_14_36_p8 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 8 228434862489459828 = some 228434862489459828 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 6 2 228434862489459828 228434862489459828 228434862489459828 endpoint_14_36_p6 endpoint_14_36_w6
private theorem endpoint_14_36_w8 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 8 2 228434862489459828 = some 228434862489459828 := by decide +kernel
private theorem endpoint_14_36_p10 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 10 228434862489459828 = some 228434862489459828 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 8 2 228434862489459828 228434862489459828 228434862489459828 endpoint_14_36_p8 endpoint_14_36_w8
private theorem endpoint_14_36_w10 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 10 2 228434862489459828 = some 228434862489459828 := by decide +kernel
private theorem endpoint_14_36_p12 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 12 228434862489459828 = some 228434862489459828 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 10 2 228434862489459828 228434862489459828 228434862489459828 endpoint_14_36_p10 endpoint_14_36_w10
private theorem endpoint_14_36_w12 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 12 1 228434862489459828 = some 228434862489459828 := by decide +kernel
private theorem endpoint_14_36_p13 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 13 228434862489459828 = some 228434862489459828 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 12 1 228434862489459828 228434862489459828 228434862489459828 endpoint_14_36_p12 endpoint_14_36_w12
def endpoint_14_36 : CertifiedEndpoint :=
  ⟨⟨14, 36, 3809⟩, 228434862489459828, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_36_flag endpoint_14_36_sources 13 228434862489459828 228434862489459828 rfl endpoint_14_36_base endpoint_14_36_p13) (by decide)⟩
private def endpoint_14_37_flag : Flag := ⟨14, 37, 3777⟩
private def endpoint_14_37_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_37_base : receiptBase endpoint_14_37_flag endpoint_14_37_sources = some 231776282481917276 := by decide +kernel
private theorem endpoint_14_37_w0 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 2 231776282481917276 = some 231776282481917276 := by decide +kernel
private theorem endpoint_14_37_w2 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 2 2 231776282481917276 = some 231776282481917276 := by decide +kernel
private theorem endpoint_14_37_p4 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 4 231776282481917276 = some 231776282481917276 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 2 2 231776282481917276 231776282481917276 231776282481917276 endpoint_14_37_w0 endpoint_14_37_w2
private theorem endpoint_14_37_w4 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 4 2 231776282481917276 = some 231776282481917276 := by decide +kernel
private theorem endpoint_14_37_p6 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 6 231776282481917276 = some 231776282481917276 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 4 2 231776282481917276 231776282481917276 231776282481917276 endpoint_14_37_p4 endpoint_14_37_w4
private theorem endpoint_14_37_w6 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 6 2 231776282481917276 = some 231776282481917276 := by decide +kernel
private theorem endpoint_14_37_p8 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 8 231776282481917276 = some 231776282481917276 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 6 2 231776282481917276 231776282481917276 231776282481917276 endpoint_14_37_p6 endpoint_14_37_w6
private theorem endpoint_14_37_w8 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 8 2 231776282481917276 = some 231776282481917276 := by decide +kernel
private theorem endpoint_14_37_p10 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 10 231776282481917276 = some 231776282481917276 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 8 2 231776282481917276 231776282481917276 231776282481917276 endpoint_14_37_p8 endpoint_14_37_w8
private theorem endpoint_14_37_w10 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 10 2 231776282481917276 = some 231776282481917276 := by decide +kernel
private theorem endpoint_14_37_p12 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 12 231776282481917276 = some 231776282481917276 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 10 2 231776282481917276 231776282481917276 231776282481917276 endpoint_14_37_p10 endpoint_14_37_w10
private theorem endpoint_14_37_w12 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 12 1 231776282481917276 = some 231776282481917276 := by decide +kernel
private theorem endpoint_14_37_p13 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 13 231776282481917276 = some 231776282481917276 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 12 1 231776282481917276 231776282481917276 231776282481917276 endpoint_14_37_p12 endpoint_14_37_w12
def endpoint_14_37 : CertifiedEndpoint :=
  ⟨⟨14, 37, 3777⟩, 231776282481917276, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_37_flag endpoint_14_37_sources 13 231776282481917276 231776282481917276 rfl endpoint_14_37_base endpoint_14_37_p13) (by decide)⟩
private def endpoint_14_38_flag : Flag := ⟨14, 38, 3743⟩
private def endpoint_14_38_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_38_base : receiptBase endpoint_14_38_flag endpoint_14_38_sources = some 234905705965131900 := by decide +kernel
private theorem endpoint_14_38_w0 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 2 234905705965131900 = some 234905705965131900 := by decide +kernel
private theorem endpoint_14_38_w2 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 2 2 234905705965131900 = some 234905705965131900 := by decide +kernel
private theorem endpoint_14_38_p4 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 4 234905705965131900 = some 234905705965131900 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 2 2 234905705965131900 234905705965131900 234905705965131900 endpoint_14_38_w0 endpoint_14_38_w2
private theorem endpoint_14_38_w4 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 4 2 234905705965131900 = some 234905705965131900 := by decide +kernel
private theorem endpoint_14_38_p6 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 6 234905705965131900 = some 234905705965131900 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 4 2 234905705965131900 234905705965131900 234905705965131900 endpoint_14_38_p4 endpoint_14_38_w4
private theorem endpoint_14_38_w6 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 6 2 234905705965131900 = some 234905705965131900 := by decide +kernel
private theorem endpoint_14_38_p8 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 8 234905705965131900 = some 234905705965131900 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 6 2 234905705965131900 234905705965131900 234905705965131900 endpoint_14_38_p6 endpoint_14_38_w6
private theorem endpoint_14_38_w8 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 8 2 234905705965131900 = some 234905705965131900 := by decide +kernel
private theorem endpoint_14_38_p10 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 10 234905705965131900 = some 234905705965131900 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 8 2 234905705965131900 234905705965131900 234905705965131900 endpoint_14_38_p8 endpoint_14_38_w8
private theorem endpoint_14_38_w10 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 10 2 234905705965131900 = some 234905705965131900 := by decide +kernel
private theorem endpoint_14_38_p12 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 12 234905705965131900 = some 234905705965131900 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 10 2 234905705965131900 234905705965131900 234905705965131900 endpoint_14_38_p10 endpoint_14_38_w10
private theorem endpoint_14_38_w12 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 12 1 234905705965131900 = some 234905705965131900 := by decide +kernel
private theorem endpoint_14_38_p13 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 13 234905705965131900 = some 234905705965131900 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 12 1 234905705965131900 234905705965131900 234905705965131900 endpoint_14_38_p12 endpoint_14_38_w12
def endpoint_14_38 : CertifiedEndpoint :=
  ⟨⟨14, 38, 3743⟩, 234905705965131900, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_38_flag endpoint_14_38_sources 13 234905705965131900 234905705965131900 rfl endpoint_14_38_base endpoint_14_38_p13) (by decide)⟩
private def endpoint_14_39_flag : Flag := ⟨14, 39, 3710⟩
private def endpoint_14_39_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_39_base : receiptBase endpoint_14_39_flag endpoint_14_39_sources = some 238004580997091948 := by decide +kernel
private theorem endpoint_14_39_w0 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 2 238004580997091948 = some 238004580997091948 := by decide +kernel
private theorem endpoint_14_39_w2 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 2 2 238004580997091948 = some 238004580997091948 := by decide +kernel
private theorem endpoint_14_39_p4 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 4 238004580997091948 = some 238004580997091948 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 2 2 238004580997091948 238004580997091948 238004580997091948 endpoint_14_39_w0 endpoint_14_39_w2
private theorem endpoint_14_39_w4 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 4 2 238004580997091948 = some 238004580997091948 := by decide +kernel
private theorem endpoint_14_39_p6 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 6 238004580997091948 = some 238004580997091948 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 4 2 238004580997091948 238004580997091948 238004580997091948 endpoint_14_39_p4 endpoint_14_39_w4
private theorem endpoint_14_39_w6 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 6 2 238004580997091948 = some 238004580997091948 := by decide +kernel
private theorem endpoint_14_39_p8 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 8 238004580997091948 = some 238004580997091948 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 6 2 238004580997091948 238004580997091948 238004580997091948 endpoint_14_39_p6 endpoint_14_39_w6
private theorem endpoint_14_39_w8 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 8 2 238004580997091948 = some 238004580997091948 := by decide +kernel
private theorem endpoint_14_39_p10 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 10 238004580997091948 = some 238004580997091948 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 8 2 238004580997091948 238004580997091948 238004580997091948 endpoint_14_39_p8 endpoint_14_39_w8
private theorem endpoint_14_39_w10 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 10 2 238004580997091948 = some 238004580997091948 := by decide +kernel
private theorem endpoint_14_39_p12 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 12 238004580997091948 = some 238004580997091948 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 10 2 238004580997091948 238004580997091948 238004580997091948 endpoint_14_39_p10 endpoint_14_39_w10
private theorem endpoint_14_39_w12 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 12 1 238004580997091948 = some 238004580997091948 := by decide +kernel
private theorem endpoint_14_39_p13 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 13 238004580997091948 = some 238004580997091948 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 12 1 238004580997091948 238004580997091948 238004580997091948 endpoint_14_39_p12 endpoint_14_39_w12
def endpoint_14_39 : CertifiedEndpoint :=
  ⟨⟨14, 39, 3710⟩, 238004580997091948, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_39_flag endpoint_14_39_sources 13 238004580997091948 238004580997091948 rfl endpoint_14_39_base endpoint_14_39_p13) (by decide)⟩
private def endpoint_14_40_flag : Flag := ⟨14, 40, 3675⟩
private def endpoint_14_40_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_40_base : receiptBase endpoint_14_40_flag endpoint_14_40_sources = some 241533919629901686 := by decide +kernel
private theorem endpoint_14_40_w0 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 2 241533919629901686 = some 241533919629901686 := by decide +kernel
private theorem endpoint_14_40_w2 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 2 2 241533919629901686 = some 241533919629901686 := by decide +kernel
private theorem endpoint_14_40_p4 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 4 241533919629901686 = some 241533919629901686 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 2 2 241533919629901686 241533919629901686 241533919629901686 endpoint_14_40_w0 endpoint_14_40_w2
private theorem endpoint_14_40_w4 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 4 2 241533919629901686 = some 241533919629901686 := by decide +kernel
private theorem endpoint_14_40_p6 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 6 241533919629901686 = some 241533919629901686 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 4 2 241533919629901686 241533919629901686 241533919629901686 endpoint_14_40_p4 endpoint_14_40_w4
private theorem endpoint_14_40_w6 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 6 2 241533919629901686 = some 241533919629901686 := by decide +kernel
private theorem endpoint_14_40_p8 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 8 241533919629901686 = some 241533919629901686 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 6 2 241533919629901686 241533919629901686 241533919629901686 endpoint_14_40_p6 endpoint_14_40_w6
private theorem endpoint_14_40_w8 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 8 2 241533919629901686 = some 241533919629901686 := by decide +kernel
private theorem endpoint_14_40_p10 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 10 241533919629901686 = some 241533919629901686 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 8 2 241533919629901686 241533919629901686 241533919629901686 endpoint_14_40_p8 endpoint_14_40_w8
private theorem endpoint_14_40_w10 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 10 2 241533919629901686 = some 241533919629901686 := by decide +kernel
private theorem endpoint_14_40_p12 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 12 241533919629901686 = some 241533919629901686 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 10 2 241533919629901686 241533919629901686 241533919629901686 endpoint_14_40_p10 endpoint_14_40_w10
private theorem endpoint_14_40_w12 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 12 1 241533919629901686 = some 241533919629901686 := by decide +kernel
private theorem endpoint_14_40_p13 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 13 241533919629901686 = some 241533919629901686 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 12 1 241533919629901686 241533919629901686 241533919629901686 endpoint_14_40_p12 endpoint_14_40_w12
def endpoint_14_40 : CertifiedEndpoint :=
  ⟨⟨14, 40, 3675⟩, 241533919629901686, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_40_flag endpoint_14_40_sources 13 241533919629901686 241533919629901686 rfl endpoint_14_40_base endpoint_14_40_p13) (by decide)⟩
private def endpoint_14_41_flag : Flag := ⟨14, 41, 3640⟩
private def endpoint_14_41_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_41_base : receiptBase endpoint_14_41_flag endpoint_14_41_sources = some 244332941648624808 := by decide +kernel
private theorem endpoint_14_41_w0 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 2 244332941648624808 = some 244332941648624808 := by decide +kernel
private theorem endpoint_14_41_w2 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 2 2 244332941648624808 = some 244332941648624808 := by decide +kernel
private theorem endpoint_14_41_p4 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 4 244332941648624808 = some 244332941648624808 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 2 2 244332941648624808 244332941648624808 244332941648624808 endpoint_14_41_w0 endpoint_14_41_w2
private theorem endpoint_14_41_w4 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 4 2 244332941648624808 = some 244332941648624808 := by decide +kernel
private theorem endpoint_14_41_p6 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 6 244332941648624808 = some 244332941648624808 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 4 2 244332941648624808 244332941648624808 244332941648624808 endpoint_14_41_p4 endpoint_14_41_w4
private theorem endpoint_14_41_w6 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 6 2 244332941648624808 = some 244332941648624808 := by decide +kernel
private theorem endpoint_14_41_p8 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 8 244332941648624808 = some 244332941648624808 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 6 2 244332941648624808 244332941648624808 244332941648624808 endpoint_14_41_p6 endpoint_14_41_w6
private theorem endpoint_14_41_w8 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 8 2 244332941648624808 = some 244332941648624808 := by decide +kernel
private theorem endpoint_14_41_p10 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 10 244332941648624808 = some 244332941648624808 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 8 2 244332941648624808 244332941648624808 244332941648624808 endpoint_14_41_p8 endpoint_14_41_w8
private theorem endpoint_14_41_w10 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 10 2 244332941648624808 = some 244332941648624808 := by decide +kernel
private theorem endpoint_14_41_p12 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 12 244332941648624808 = some 244332941648624808 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 10 2 244332941648624808 244332941648624808 244332941648624808 endpoint_14_41_p10 endpoint_14_41_w10
private theorem endpoint_14_41_w12 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 12 1 244332941648624808 = some 244332941648624808 := by decide +kernel
private theorem endpoint_14_41_p13 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 13 244332941648624808 = some 244332941648624808 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 12 1 244332941648624808 244332941648624808 244332941648624808 endpoint_14_41_p12 endpoint_14_41_w12
def endpoint_14_41 : CertifiedEndpoint :=
  ⟨⟨14, 41, 3640⟩, 244332941648624808, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_41_flag endpoint_14_41_sources 13 244332941648624808 244332941648624808 rfl endpoint_14_41_base endpoint_14_41_p13) (by decide)⟩
private def endpoint_14_42_flag : Flag := ⟨14, 42, 3604⟩
private def endpoint_14_42_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_42_base : receiptBase endpoint_14_42_flag endpoint_14_42_sources = some 246967334585493506 := by decide +kernel
private theorem endpoint_14_42_w0 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 2 246967334585493506 = some 246967334585493506 := by decide +kernel
private theorem endpoint_14_42_w2 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 2 2 246967334585493506 = some 246967334585493506 := by decide +kernel
private theorem endpoint_14_42_p4 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 4 246967334585493506 = some 246967334585493506 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 2 2 246967334585493506 246967334585493506 246967334585493506 endpoint_14_42_w0 endpoint_14_42_w2
private theorem endpoint_14_42_w4 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 4 2 246967334585493506 = some 246967334585493506 := by decide +kernel
private theorem endpoint_14_42_p6 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 6 246967334585493506 = some 246967334585493506 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 4 2 246967334585493506 246967334585493506 246967334585493506 endpoint_14_42_p4 endpoint_14_42_w4
private theorem endpoint_14_42_w6 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 6 2 246967334585493506 = some 246967334585493506 := by decide +kernel
private theorem endpoint_14_42_p8 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 8 246967334585493506 = some 246967334585493506 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 6 2 246967334585493506 246967334585493506 246967334585493506 endpoint_14_42_p6 endpoint_14_42_w6
private theorem endpoint_14_42_w8 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 8 2 246967334585493506 = some 246967334585493506 := by decide +kernel
private theorem endpoint_14_42_p10 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 10 246967334585493506 = some 246967334585493506 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 8 2 246967334585493506 246967334585493506 246967334585493506 endpoint_14_42_p8 endpoint_14_42_w8
private theorem endpoint_14_42_w10 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 10 2 246967334585493506 = some 246967334585493506 := by decide +kernel
private theorem endpoint_14_42_p12 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 12 246967334585493506 = some 246967334585493506 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 10 2 246967334585493506 246967334585493506 246967334585493506 endpoint_14_42_p10 endpoint_14_42_w10
private theorem endpoint_14_42_w12 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 12 1 246967334585493506 = some 246967334585493506 := by decide +kernel
private theorem endpoint_14_42_p13 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 13 246967334585493506 = some 246967334585493506 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 12 1 246967334585493506 246967334585493506 246967334585493506 endpoint_14_42_p12 endpoint_14_42_w12
def endpoint_14_42 : CertifiedEndpoint :=
  ⟨⟨14, 42, 3604⟩, 246967334585493506, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_42_flag endpoint_14_42_sources 13 246967334585493506 246967334585493506 rfl endpoint_14_42_base endpoint_14_42_p13) (by decide)⟩
private def endpoint_14_43_flag : Flag := ⟨14, 43, 3568⟩
private def endpoint_14_43_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_43_base : receiptBase endpoint_14_43_flag endpoint_14_43_sources = some 249501887692699086 := by decide +kernel
private theorem endpoint_14_43_w0 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 2 249501887692699086 = some 249501887692699086 := by decide +kernel
private theorem endpoint_14_43_w2 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 2 2 249501887692699086 = some 249501887692699086 := by decide +kernel
private theorem endpoint_14_43_p4 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 4 249501887692699086 = some 249501887692699086 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 2 2 249501887692699086 249501887692699086 249501887692699086 endpoint_14_43_w0 endpoint_14_43_w2
private theorem endpoint_14_43_w4 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 4 2 249501887692699086 = some 249501887692699086 := by decide +kernel
private theorem endpoint_14_43_p6 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 6 249501887692699086 = some 249501887692699086 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 4 2 249501887692699086 249501887692699086 249501887692699086 endpoint_14_43_p4 endpoint_14_43_w4
private theorem endpoint_14_43_w6 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 6 2 249501887692699086 = some 249501887692699086 := by decide +kernel
private theorem endpoint_14_43_p8 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 8 249501887692699086 = some 249501887692699086 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 6 2 249501887692699086 249501887692699086 249501887692699086 endpoint_14_43_p6 endpoint_14_43_w6
private theorem endpoint_14_43_w8 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 8 2 249501887692699086 = some 249501887692699086 := by decide +kernel
private theorem endpoint_14_43_p10 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 10 249501887692699086 = some 249501887692699086 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 8 2 249501887692699086 249501887692699086 249501887692699086 endpoint_14_43_p8 endpoint_14_43_w8
private theorem endpoint_14_43_w10 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 10 2 249501887692699086 = some 249501887692699086 := by decide +kernel
private theorem endpoint_14_43_p12 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 12 249501887692699086 = some 249501887692699086 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 10 2 249501887692699086 249501887692699086 249501887692699086 endpoint_14_43_p10 endpoint_14_43_w10
private theorem endpoint_14_43_w12 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 12 1 249501887692699086 = some 249501887692699086 := by decide +kernel
private theorem endpoint_14_43_p13 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 13 249501887692699086 = some 249501887692699086 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 12 1 249501887692699086 249501887692699086 249501887692699086 endpoint_14_43_p12 endpoint_14_43_w12
def endpoint_14_43 : CertifiedEndpoint :=
  ⟨⟨14, 43, 3568⟩, 249501887692699086, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_43_flag endpoint_14_43_sources 13 249501887692699086 249501887692699086 rfl endpoint_14_43_base endpoint_14_43_p13) (by decide)⟩
private def endpoint_14_44_flag : Flag := ⟨14, 44, 3530⟩
private def endpoint_14_44_sources : Sources := ⟨contact23, contact03, contact25⟩
private theorem endpoint_14_44_base : receiptBase endpoint_14_44_flag endpoint_14_44_sources = some 253159754844750936 := by decide +kernel
private theorem endpoint_14_44_w0 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 2 253159754844750936 = some 253159754844750936 := by decide +kernel
private theorem endpoint_14_44_w2 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 2 2 253159754844750936 = some 253159754844750936 := by decide +kernel
private theorem endpoint_14_44_p4 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 4 253159754844750936 = some 253159754844750936 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 2 2 253159754844750936 253159754844750936 253159754844750936 endpoint_14_44_w0 endpoint_14_44_w2
private theorem endpoint_14_44_w4 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 4 2 253159754844750936 = some 253159754844750936 := by decide +kernel
private theorem endpoint_14_44_p6 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 6 253159754844750936 = some 253159754844750936 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 4 2 253159754844750936 253159754844750936 253159754844750936 endpoint_14_44_p4 endpoint_14_44_w4
private theorem endpoint_14_44_w6 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 6 2 253159754844750936 = some 253159754844750936 := by decide +kernel
private theorem endpoint_14_44_p8 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 8 253159754844750936 = some 253159754844750936 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 6 2 253159754844750936 253159754844750936 253159754844750936 endpoint_14_44_p6 endpoint_14_44_w6
private theorem endpoint_14_44_w8 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 8 2 253159754844750936 = some 253159754844750936 := by decide +kernel
private theorem endpoint_14_44_p10 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 10 253159754844750936 = some 253159754844750936 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 8 2 253159754844750936 253159754844750936 253159754844750936 endpoint_14_44_p8 endpoint_14_44_w8
private theorem endpoint_14_44_w10 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 10 2 253159754844750936 = some 253159754844750936 := by decide +kernel
private theorem endpoint_14_44_p12 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 12 253159754844750936 = some 253159754844750936 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 10 2 253159754844750936 253159754844750936 253159754844750936 endpoint_14_44_p10 endpoint_14_44_w10
private theorem endpoint_14_44_w12 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 12 1 253159754844750936 = some 253159754844750936 := by decide +kernel
private theorem endpoint_14_44_p13 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 13 253159754844750936 = some 253159754844750936 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 12 1 253159754844750936 253159754844750936 253159754844750936 endpoint_14_44_p12 endpoint_14_44_w12
def endpoint_14_44 : CertifiedEndpoint :=
  ⟨⟨14, 44, 3530⟩, 253159754844750936, .terminal ⟨contact23, contact03, contact25⟩ (finish_receipt_window endpoint_14_44_flag endpoint_14_44_sources 13 253159754844750936 253159754844750936 rfl endpoint_14_44_base endpoint_14_44_p13) (by decide)⟩
private def endpoint_14_45_flag : Flag := ⟨14, 45, 3492⟩
private def endpoint_14_45_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_45_base : receiptBase endpoint_14_45_flag endpoint_14_45_sources = some 256644783397771841 := by decide +kernel
private theorem endpoint_14_45_w0 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 2 256644783397771841 = some 256644783397771841 := by decide +kernel
private theorem endpoint_14_45_w2 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 2 2 256644783397771841 = some 256644783397771841 := by decide +kernel
private theorem endpoint_14_45_p4 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 4 256644783397771841 = some 256644783397771841 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 2 2 256644783397771841 256644783397771841 256644783397771841 endpoint_14_45_w0 endpoint_14_45_w2
private theorem endpoint_14_45_w4 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 4 2 256644783397771841 = some 256644783397771841 := by decide +kernel
private theorem endpoint_14_45_p6 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 6 256644783397771841 = some 256644783397771841 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 4 2 256644783397771841 256644783397771841 256644783397771841 endpoint_14_45_p4 endpoint_14_45_w4
private theorem endpoint_14_45_w6 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 6 2 256644783397771841 = some 256644783397771841 := by decide +kernel
private theorem endpoint_14_45_p8 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 8 256644783397771841 = some 256644783397771841 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 6 2 256644783397771841 256644783397771841 256644783397771841 endpoint_14_45_p6 endpoint_14_45_w6
private theorem endpoint_14_45_w8 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 8 2 256644783397771841 = some 256644783397771841 := by decide +kernel
private theorem endpoint_14_45_p10 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 10 256644783397771841 = some 256644783397771841 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 8 2 256644783397771841 256644783397771841 256644783397771841 endpoint_14_45_p8 endpoint_14_45_w8
private theorem endpoint_14_45_w10 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 10 2 256644783397771841 = some 256644783397771841 := by decide +kernel
private theorem endpoint_14_45_p12 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 12 256644783397771841 = some 256644783397771841 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 10 2 256644783397771841 256644783397771841 256644783397771841 endpoint_14_45_p10 endpoint_14_45_w10
private theorem endpoint_14_45_w12 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 12 1 256644783397771841 = some 256644783397771841 := by decide +kernel
private theorem endpoint_14_45_p13 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 13 256644783397771841 = some 256644783397771841 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 12 1 256644783397771841 256644783397771841 256644783397771841 endpoint_14_45_p12 endpoint_14_45_w12
def endpoint_14_45 : CertifiedEndpoint :=
  ⟨⟨14, 45, 3492⟩, 256644783397771841, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_45_flag endpoint_14_45_sources 13 256644783397771841 256644783397771841 rfl endpoint_14_45_base endpoint_14_45_p13) (by decide)⟩
private def endpoint_14_46_flag : Flag := ⟨14, 46, 3453⟩
private def endpoint_14_46_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_46_base : receiptBase endpoint_14_46_flag endpoint_14_46_sources = some 258593002937225141 := by decide +kernel
private theorem endpoint_14_46_w0 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 2 258593002937225141 = some 258593002937225141 := by decide +kernel
private theorem endpoint_14_46_w2 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 2 2 258593002937225141 = some 258593002937225141 := by decide +kernel
private theorem endpoint_14_46_p4 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 4 258593002937225141 = some 258593002937225141 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 2 2 258593002937225141 258593002937225141 258593002937225141 endpoint_14_46_w0 endpoint_14_46_w2
private theorem endpoint_14_46_w4 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 4 2 258593002937225141 = some 258593002937225141 := by decide +kernel
private theorem endpoint_14_46_p6 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 6 258593002937225141 = some 258593002937225141 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 4 2 258593002937225141 258593002937225141 258593002937225141 endpoint_14_46_p4 endpoint_14_46_w4
private theorem endpoint_14_46_w6 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 6 2 258593002937225141 = some 258593002937225141 := by decide +kernel
private theorem endpoint_14_46_p8 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 8 258593002937225141 = some 258593002937225141 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 6 2 258593002937225141 258593002937225141 258593002937225141 endpoint_14_46_p6 endpoint_14_46_w6
private theorem endpoint_14_46_w8 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 8 2 258593002937225141 = some 258593002937225141 := by decide +kernel
private theorem endpoint_14_46_p10 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 10 258593002937225141 = some 258593002937225141 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 8 2 258593002937225141 258593002937225141 258593002937225141 endpoint_14_46_p8 endpoint_14_46_w8
private theorem endpoint_14_46_w10 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 10 2 258593002937225141 = some 258593002937225141 := by decide +kernel
private theorem endpoint_14_46_p12 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 12 258593002937225141 = some 258593002937225141 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 10 2 258593002937225141 258593002937225141 258593002937225141 endpoint_14_46_p10 endpoint_14_46_w10
private theorem endpoint_14_46_w12 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 12 1 258593002937225141 = some 258593002937225141 := by decide +kernel
private theorem endpoint_14_46_p13 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 13 258593002937225141 = some 258593002937225141 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 12 1 258593002937225141 258593002937225141 258593002937225141 endpoint_14_46_p12 endpoint_14_46_w12
def endpoint_14_46 : CertifiedEndpoint :=
  ⟨⟨14, 46, 3453⟩, 258593002937225141, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_46_flag endpoint_14_46_sources 13 258593002937225141 258593002937225141 rfl endpoint_14_46_base endpoint_14_46_p13) (by decide)⟩
private def endpoint_14_47_flag : Flag := ⟨14, 47, 3413⟩
private def endpoint_14_47_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_47_base : receiptBase endpoint_14_47_flag endpoint_14_47_sources = some 260358273888655161 := by decide +kernel
private theorem endpoint_14_47_w0 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 2 260358273888655161 = some 260358273888655161 := by decide +kernel
private theorem endpoint_14_47_w2 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 2 2 260358273888655161 = some 260358273888655161 := by decide +kernel
private theorem endpoint_14_47_p4 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 4 260358273888655161 = some 260358273888655161 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 2 2 260358273888655161 260358273888655161 260358273888655161 endpoint_14_47_w0 endpoint_14_47_w2
private theorem endpoint_14_47_w4 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 4 2 260358273888655161 = some 260358273888655161 := by decide +kernel
private theorem endpoint_14_47_p6 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 6 260358273888655161 = some 260358273888655161 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 4 2 260358273888655161 260358273888655161 260358273888655161 endpoint_14_47_p4 endpoint_14_47_w4
private theorem endpoint_14_47_w6 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 6 2 260358273888655161 = some 260358273888655161 := by decide +kernel
private theorem endpoint_14_47_p8 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 8 260358273888655161 = some 260358273888655161 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 6 2 260358273888655161 260358273888655161 260358273888655161 endpoint_14_47_p6 endpoint_14_47_w6
private theorem endpoint_14_47_w8 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 8 2 260358273888655161 = some 260358273888655161 := by decide +kernel
private theorem endpoint_14_47_p10 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 10 260358273888655161 = some 260358273888655161 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 8 2 260358273888655161 260358273888655161 260358273888655161 endpoint_14_47_p8 endpoint_14_47_w8
private theorem endpoint_14_47_w10 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 10 2 260358273888655161 = some 260358273888655161 := by decide +kernel
private theorem endpoint_14_47_p12 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 12 260358273888655161 = some 260358273888655161 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 10 2 260358273888655161 260358273888655161 260358273888655161 endpoint_14_47_p10 endpoint_14_47_w10
private theorem endpoint_14_47_w12 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 12 1 260358273888655161 = some 260358273888655161 := by decide +kernel
private theorem endpoint_14_47_p13 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 13 260358273888655161 = some 260358273888655161 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 12 1 260358273888655161 260358273888655161 260358273888655161 endpoint_14_47_p12 endpoint_14_47_w12
def endpoint_14_47 : CertifiedEndpoint :=
  ⟨⟨14, 47, 3413⟩, 260358273888655161, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_47_flag endpoint_14_47_sources 13 260358273888655161 260358273888655161 rfl endpoint_14_47_base endpoint_14_47_p13) (by decide)⟩
private def endpoint_14_48_flag : Flag := ⟨14, 48, 3372⟩
private def endpoint_14_48_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_48_base : receiptBase endpoint_14_48_flag endpoint_14_48_sources = some 262771813101830551 := by decide +kernel
private theorem endpoint_14_48_w0 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 2 262771813101830551 = some 262771813101830551 := by decide +kernel
private theorem endpoint_14_48_w2 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 2 2 262771813101830551 = some 262771813101830551 := by decide +kernel
private theorem endpoint_14_48_p4 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 4 262771813101830551 = some 262771813101830551 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 2 2 262771813101830551 262771813101830551 262771813101830551 endpoint_14_48_w0 endpoint_14_48_w2
private theorem endpoint_14_48_w4 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 4 2 262771813101830551 = some 262771813101830551 := by decide +kernel
private theorem endpoint_14_48_p6 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 6 262771813101830551 = some 262771813101830551 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 4 2 262771813101830551 262771813101830551 262771813101830551 endpoint_14_48_p4 endpoint_14_48_w4
private theorem endpoint_14_48_w6 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 6 2 262771813101830551 = some 262771813101830551 := by decide +kernel
private theorem endpoint_14_48_p8 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 8 262771813101830551 = some 262771813101830551 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 6 2 262771813101830551 262771813101830551 262771813101830551 endpoint_14_48_p6 endpoint_14_48_w6
private theorem endpoint_14_48_w8 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 8 2 262771813101830551 = some 262771813101830551 := by decide +kernel
private theorem endpoint_14_48_p10 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 10 262771813101830551 = some 262771813101830551 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 8 2 262771813101830551 262771813101830551 262771813101830551 endpoint_14_48_p8 endpoint_14_48_w8
private theorem endpoint_14_48_w10 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 10 2 262771813101830551 = some 262771813101830551 := by decide +kernel
private theorem endpoint_14_48_p12 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 12 262771813101830551 = some 262771813101830551 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 10 2 262771813101830551 262771813101830551 262771813101830551 endpoint_14_48_p10 endpoint_14_48_w10
private theorem endpoint_14_48_w12 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 12 1 262771813101830551 = some 262771813101830551 := by decide +kernel
private theorem endpoint_14_48_p13 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 13 262771813101830551 = some 262771813101830551 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 12 1 262771813101830551 262771813101830551 262771813101830551 endpoint_14_48_p12 endpoint_14_48_w12
def endpoint_14_48 : CertifiedEndpoint :=
  ⟨⟨14, 48, 3372⟩, 262771813101830551, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_48_flag endpoint_14_48_sources 13 262771813101830551 262771813101830551 rfl endpoint_14_48_base endpoint_14_48_p13) (by decide)⟩
private def endpoint_14_49_flag : Flag := ⟨14, 49, 3329⟩
private def endpoint_14_49_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_14_49_base : receiptBase endpoint_14_49_flag endpoint_14_49_sources = some 259553939347230746 := by decide +kernel
private theorem endpoint_14_49_w0 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 2 259553939347230746 = some 259553939347230746 := by decide +kernel
private theorem endpoint_14_49_w2 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 2 2 259553939347230746 = some 259553939347230746 := by decide +kernel
private theorem endpoint_14_49_p4 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 4 259553939347230746 = some 259553939347230746 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 2 2 259553939347230746 259553939347230746 259553939347230746 endpoint_14_49_w0 endpoint_14_49_w2
private theorem endpoint_14_49_w4 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 4 2 259553939347230746 = some 259553939347230746 := by decide +kernel
private theorem endpoint_14_49_p6 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 6 259553939347230746 = some 259553939347230746 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 4 2 259553939347230746 259553939347230746 259553939347230746 endpoint_14_49_p4 endpoint_14_49_w4
private theorem endpoint_14_49_w6 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 6 2 259553939347230746 = some 259553939347230746 := by decide +kernel
private theorem endpoint_14_49_p8 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 8 259553939347230746 = some 259553939347230746 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 6 2 259553939347230746 259553939347230746 259553939347230746 endpoint_14_49_p6 endpoint_14_49_w6
private theorem endpoint_14_49_w8 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 8 2 259553939347230746 = some 259553939347230746 := by decide +kernel
private theorem endpoint_14_49_p10 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 10 259553939347230746 = some 259553939347230746 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 8 2 259553939347230746 259553939347230746 259553939347230746 endpoint_14_49_p8 endpoint_14_49_w8
private theorem endpoint_14_49_w10 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 10 2 259553939347230746 = some 259553939347230746 := by decide +kernel
private theorem endpoint_14_49_p12 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 12 259553939347230746 = some 259553939347230746 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 10 2 259553939347230746 259553939347230746 259553939347230746 endpoint_14_49_p10 endpoint_14_49_w10
private theorem endpoint_14_49_w12 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 12 1 259553939347230746 = some 259553939347230746 := by decide +kernel
private theorem endpoint_14_49_p13 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 13 259553939347230746 = some 259553939347230746 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 12 1 259553939347230746 259553939347230746 259553939347230746 endpoint_14_49_p12 endpoint_14_49_w12
def endpoint_14_49 : CertifiedEndpoint :=
  ⟨⟨14, 49, 3329⟩, 259553939347230746, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_14_49_flag endpoint_14_49_sources 13 259553939347230746 259553939347230746 rfl endpoint_14_49_base endpoint_14_49_p13) (by decide)⟩
private def endpoint_14_50_flag : Flag := ⟨14, 50, 3286⟩
private def endpoint_14_50_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_14_50_base : receiptBase endpoint_14_50_flag endpoint_14_50_sources = some 260793105709768494 := by decide +kernel
private theorem endpoint_14_50_w0 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 2 260793105709768494 = some 260793105709768494 := by decide +kernel
private theorem endpoint_14_50_w2 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 2 2 260793105709768494 = some 260793105709768494 := by decide +kernel
private theorem endpoint_14_50_p4 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 4 260793105709768494 = some 260793105709768494 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 2 2 260793105709768494 260793105709768494 260793105709768494 endpoint_14_50_w0 endpoint_14_50_w2
private theorem endpoint_14_50_w4 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 4 2 260793105709768494 = some 260793105709768494 := by decide +kernel
private theorem endpoint_14_50_p6 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 6 260793105709768494 = some 260793105709768494 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 4 2 260793105709768494 260793105709768494 260793105709768494 endpoint_14_50_p4 endpoint_14_50_w4
private theorem endpoint_14_50_w6 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 6 2 260793105709768494 = some 260793105709768494 := by decide +kernel
private theorem endpoint_14_50_p8 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 8 260793105709768494 = some 260793105709768494 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 6 2 260793105709768494 260793105709768494 260793105709768494 endpoint_14_50_p6 endpoint_14_50_w6
private theorem endpoint_14_50_w8 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 8 2 260793105709768494 = some 260793105709768494 := by decide +kernel
private theorem endpoint_14_50_p10 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 10 260793105709768494 = some 260793105709768494 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 8 2 260793105709768494 260793105709768494 260793105709768494 endpoint_14_50_p8 endpoint_14_50_w8
private theorem endpoint_14_50_w10 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 10 2 260793105709768494 = some 260793105709768494 := by decide +kernel
private theorem endpoint_14_50_p12 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 12 260793105709768494 = some 260793105709768494 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 10 2 260793105709768494 260793105709768494 260793105709768494 endpoint_14_50_p10 endpoint_14_50_w10
private theorem endpoint_14_50_w12 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 12 1 260793105709768494 = some 260793105709768494 := by decide +kernel
private theorem endpoint_14_50_p13 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 13 260793105709768494 = some 260793105709768494 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 12 1 260793105709768494 260793105709768494 260793105709768494 endpoint_14_50_p12 endpoint_14_50_w12
def endpoint_14_50 : CertifiedEndpoint :=
  ⟨⟨14, 50, 3286⟩, 260793105709768494, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_14_50_flag endpoint_14_50_sources 13 260793105709768494 260793105709768494 rfl endpoint_14_50_base endpoint_14_50_p13) (by decide)⟩
private def endpoint_14_51_flag : Flag := ⟨14, 51, 3241⟩
private def endpoint_14_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_14_51_base : receiptBase endpoint_14_51_flag endpoint_14_51_sources = some 261755791507819416 := by decide +kernel
private theorem endpoint_14_51_w0 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 2 261755791507819416 = some 261755791507819416 := by decide +kernel
private theorem endpoint_14_51_w2 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 2 2 261755791507819416 = some 261755791507819416 := by decide +kernel
private theorem endpoint_14_51_p4 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 4 261755791507819416 = some 261755791507819416 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 2 2 261755791507819416 261755791507819416 261755791507819416 endpoint_14_51_w0 endpoint_14_51_w2
private theorem endpoint_14_51_w4 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 4 2 261755791507819416 = some 261755791507819416 := by decide +kernel
private theorem endpoint_14_51_p6 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 6 261755791507819416 = some 261755791507819416 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 4 2 261755791507819416 261755791507819416 261755791507819416 endpoint_14_51_p4 endpoint_14_51_w4
private theorem endpoint_14_51_w6 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 6 2 261755791507819416 = some 261755791507819416 := by decide +kernel
private theorem endpoint_14_51_p8 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 8 261755791507819416 = some 261755791507819416 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 6 2 261755791507819416 261755791507819416 261755791507819416 endpoint_14_51_p6 endpoint_14_51_w6
private theorem endpoint_14_51_w8 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 8 2 261755791507819416 = some 261755791507819416 := by decide +kernel
private theorem endpoint_14_51_p10 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 10 261755791507819416 = some 261755791507819416 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 8 2 261755791507819416 261755791507819416 261755791507819416 endpoint_14_51_p8 endpoint_14_51_w8
private theorem endpoint_14_51_w10 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 10 2 261755791507819416 = some 261755791507819416 := by decide +kernel
private theorem endpoint_14_51_p12 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 12 261755791507819416 = some 261755791507819416 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 10 2 261755791507819416 261755791507819416 261755791507819416 endpoint_14_51_p10 endpoint_14_51_w10
private theorem endpoint_14_51_w12 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 12 1 261755791507819416 = some 261755791507819416 := by decide +kernel
private theorem endpoint_14_51_p13 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 13 261755791507819416 = some 261755791507819416 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 12 1 261755791507819416 261755791507819416 261755791507819416 endpoint_14_51_p12 endpoint_14_51_w12
def endpoint_14_51 : CertifiedEndpoint :=
  ⟨⟨14, 51, 3241⟩, 261755791507819416, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_14_51_flag endpoint_14_51_sources 13 261755791507819416 261755791507819416 rfl endpoint_14_51_base endpoint_14_51_p13) (by decide)⟩
private def endpoint_14_52_flag : Flag := ⟨14, 52, 3195⟩
private def endpoint_14_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_14_52_base : receiptBase endpoint_14_52_flag endpoint_14_52_sources = some 262514562874503086 := by decide +kernel
private theorem endpoint_14_52_w0 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 2 262514562874503086 = some 262514562874503086 := by decide +kernel
private theorem endpoint_14_52_w2 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 2 2 262514562874503086 = some 262514562874503086 := by decide +kernel
private theorem endpoint_14_52_p4 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 4 262514562874503086 = some 262514562874503086 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 2 2 262514562874503086 262514562874503086 262514562874503086 endpoint_14_52_w0 endpoint_14_52_w2
private theorem endpoint_14_52_w4 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 4 2 262514562874503086 = some 262514562874503086 := by decide +kernel
private theorem endpoint_14_52_p6 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 6 262514562874503086 = some 262514562874503086 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 4 2 262514562874503086 262514562874503086 262514562874503086 endpoint_14_52_p4 endpoint_14_52_w4
private theorem endpoint_14_52_w6 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 6 2 262514562874503086 = some 262514562874503086 := by decide +kernel
private theorem endpoint_14_52_p8 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 8 262514562874503086 = some 262514562874503086 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 6 2 262514562874503086 262514562874503086 262514562874503086 endpoint_14_52_p6 endpoint_14_52_w6
private theorem endpoint_14_52_w8 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 8 2 262514562874503086 = some 262514562874503086 := by decide +kernel
private theorem endpoint_14_52_p10 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 10 262514562874503086 = some 262514562874503086 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 8 2 262514562874503086 262514562874503086 262514562874503086 endpoint_14_52_p8 endpoint_14_52_w8
private theorem endpoint_14_52_w10 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 10 2 262514562874503086 = some 262514562874503086 := by decide +kernel
private theorem endpoint_14_52_p12 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 12 262514562874503086 = some 262514562874503086 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 10 2 262514562874503086 262514562874503086 262514562874503086 endpoint_14_52_p10 endpoint_14_52_w10
private theorem endpoint_14_52_w12 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 12 1 262514562874503086 = some 262514562874503086 := by decide +kernel
private theorem endpoint_14_52_p13 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 13 262514562874503086 = some 262514562874503086 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 12 1 262514562874503086 262514562874503086 262514562874503086 endpoint_14_52_p12 endpoint_14_52_w12
def endpoint_14_52 : CertifiedEndpoint :=
  ⟨⟨14, 52, 3195⟩, 262514562874503086, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_14_52_flag endpoint_14_52_sources 13 262514562874503086 262514562874503086 rfl endpoint_14_52_base endpoint_14_52_p13) (by decide)⟩
private def endpoint_14_53_flag : Flag := ⟨14, 53, 3147⟩
private def endpoint_14_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_14_53_base : receiptBase endpoint_14_53_flag endpoint_14_53_sources = some 262983312615024911 := by decide +kernel
private theorem endpoint_14_53_w0 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 2 262983312615024911 = some 262983312615024911 := by decide +kernel
private theorem endpoint_14_53_w2 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 2 2 262983312615024911 = some 262983312615024911 := by decide +kernel
private theorem endpoint_14_53_p4 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 4 262983312615024911 = some 262983312615024911 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 2 2 262983312615024911 262983312615024911 262983312615024911 endpoint_14_53_w0 endpoint_14_53_w2
private theorem endpoint_14_53_w4 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 4 2 262983312615024911 = some 262983312615024911 := by decide +kernel
private theorem endpoint_14_53_p6 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 6 262983312615024911 = some 262983312615024911 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 4 2 262983312615024911 262983312615024911 262983312615024911 endpoint_14_53_p4 endpoint_14_53_w4
private theorem endpoint_14_53_w6 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 6 2 262983312615024911 = some 262983312615024911 := by decide +kernel
private theorem endpoint_14_53_p8 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 8 262983312615024911 = some 262983312615024911 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 6 2 262983312615024911 262983312615024911 262983312615024911 endpoint_14_53_p6 endpoint_14_53_w6
private theorem endpoint_14_53_w8 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 8 2 262983312615024911 = some 262983312615024911 := by decide +kernel
private theorem endpoint_14_53_p10 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 10 262983312615024911 = some 262983312615024911 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 8 2 262983312615024911 262983312615024911 262983312615024911 endpoint_14_53_p8 endpoint_14_53_w8
private theorem endpoint_14_53_w10 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 10 2 262983312615024911 = some 262983312615024911 := by decide +kernel
private theorem endpoint_14_53_p12 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 12 262983312615024911 = some 262983312615024911 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 10 2 262983312615024911 262983312615024911 262983312615024911 endpoint_14_53_p10 endpoint_14_53_w10
private theorem endpoint_14_53_w12 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 12 1 262983312615024911 = some 262983312615024911 := by decide +kernel
private theorem endpoint_14_53_p13 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 13 262983312615024911 = some 262983312615024911 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 12 1 262983312615024911 262983312615024911 262983312615024911 endpoint_14_53_p12 endpoint_14_53_w12
def endpoint_14_53 : CertifiedEndpoint :=
  ⟨⟨14, 53, 3147⟩, 262983312615024911, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_14_53_flag endpoint_14_53_sources 13 262983312615024911 262983312615024911 rfl endpoint_14_53_base endpoint_14_53_p13) (by decide)⟩
private def endpoint_14_54_flag : Flag := ⟨14, 54, 3098⟩
private def endpoint_14_54_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_54_base : receiptBase endpoint_14_54_flag endpoint_14_54_sources = some 263785227352675110 := by decide +kernel
private theorem endpoint_14_54_w0 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 2 263785227352675110 = some 263785227352675110 := by decide +kernel
private theorem endpoint_14_54_w2 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 2 2 263785227352675110 = some 263785227352675110 := by decide +kernel
private theorem endpoint_14_54_p4 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 4 263785227352675110 = some 263785227352675110 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 2 2 263785227352675110 263785227352675110 263785227352675110 endpoint_14_54_w0 endpoint_14_54_w2
private theorem endpoint_14_54_w4 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 4 2 263785227352675110 = some 263785227352675110 := by decide +kernel
private theorem endpoint_14_54_p6 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 6 263785227352675110 = some 263785227352675110 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 4 2 263785227352675110 263785227352675110 263785227352675110 endpoint_14_54_p4 endpoint_14_54_w4
private theorem endpoint_14_54_w6 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 6 2 263785227352675110 = some 263785227352675110 := by decide +kernel
private theorem endpoint_14_54_p8 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 8 263785227352675110 = some 263785227352675110 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 6 2 263785227352675110 263785227352675110 263785227352675110 endpoint_14_54_p6 endpoint_14_54_w6
private theorem endpoint_14_54_w8 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 8 2 263785227352675110 = some 263785227352675110 := by decide +kernel
private theorem endpoint_14_54_p10 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 10 263785227352675110 = some 263785227352675110 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 8 2 263785227352675110 263785227352675110 263785227352675110 endpoint_14_54_p8 endpoint_14_54_w8
private theorem endpoint_14_54_w10 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 10 2 263785227352675110 = some 263785227352675110 := by decide +kernel
private theorem endpoint_14_54_p12 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 12 263785227352675110 = some 263785227352675110 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 10 2 263785227352675110 263785227352675110 263785227352675110 endpoint_14_54_p10 endpoint_14_54_w10
private theorem endpoint_14_54_w12 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 12 1 263785227352675110 = some 263785227352675110 := by decide +kernel
private theorem endpoint_14_54_p13 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 13 263785227352675110 = some 263785227352675110 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 12 1 263785227352675110 263785227352675110 263785227352675110 endpoint_14_54_p12 endpoint_14_54_w12
def endpoint_14_54 : CertifiedEndpoint :=
  ⟨⟨14, 54, 3098⟩, 263785227352675110, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_54_flag endpoint_14_54_sources 13 263785227352675110 263785227352675110 rfl endpoint_14_54_base endpoint_14_54_p13) (by decide)⟩
private def endpoint_14_55_flag : Flag := ⟨14, 55, 3048⟩
private def endpoint_14_55_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_55_base : receiptBase endpoint_14_55_flag endpoint_14_55_sources = some 263824707963644834 := by decide +kernel
private theorem endpoint_14_55_w0 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 2 263824707963644834 = some 263824707963644834 := by decide +kernel
private theorem endpoint_14_55_w2 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 2 2 263824707963644834 = some 263824707963644834 := by decide +kernel
private theorem endpoint_14_55_p4 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 4 263824707963644834 = some 263824707963644834 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 2 2 263824707963644834 263824707963644834 263824707963644834 endpoint_14_55_w0 endpoint_14_55_w2
private theorem endpoint_14_55_w4 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 4 2 263824707963644834 = some 263824707963644834 := by decide +kernel
private theorem endpoint_14_55_p6 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 6 263824707963644834 = some 263824707963644834 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 4 2 263824707963644834 263824707963644834 263824707963644834 endpoint_14_55_p4 endpoint_14_55_w4
private theorem endpoint_14_55_w6 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 6 2 263824707963644834 = some 263824707963644834 := by decide +kernel
private theorem endpoint_14_55_p8 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 8 263824707963644834 = some 263824707963644834 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 6 2 263824707963644834 263824707963644834 263824707963644834 endpoint_14_55_p6 endpoint_14_55_w6
private theorem endpoint_14_55_w8 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 8 2 263824707963644834 = some 263824707963644834 := by decide +kernel
private theorem endpoint_14_55_p10 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 10 263824707963644834 = some 263824707963644834 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 8 2 263824707963644834 263824707963644834 263824707963644834 endpoint_14_55_p8 endpoint_14_55_w8
private theorem endpoint_14_55_w10 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 10 2 263824707963644834 = some 263824707963644834 := by decide +kernel
private theorem endpoint_14_55_p12 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 12 263824707963644834 = some 263824707963644834 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 10 2 263824707963644834 263824707963644834 263824707963644834 endpoint_14_55_p10 endpoint_14_55_w10
private theorem endpoint_14_55_w12 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 12 1 263824707963644834 = some 263824707963644834 := by decide +kernel
private theorem endpoint_14_55_p13 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 13 263824707963644834 = some 263824707963644834 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 12 1 263824707963644834 263824707963644834 263824707963644834 endpoint_14_55_p12 endpoint_14_55_w12
def endpoint_14_55 : CertifiedEndpoint :=
  ⟨⟨14, 55, 3048⟩, 263824707963644834, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_55_flag endpoint_14_55_sources 13 263824707963644834 263824707963644834 rfl endpoint_14_55_base endpoint_14_55_p13) (by decide)⟩
private def endpoint_14_56_flag : Flag := ⟨14, 56, 2996⟩
private def endpoint_14_56_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_56_base : receiptBase endpoint_14_56_flag endpoint_14_56_sources = some 263554372395065968 := by decide +kernel
private theorem endpoint_14_56_w0 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 2 263554372395065968 = some 263554372395065968 := by decide +kernel
private theorem endpoint_14_56_w2 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 2 2 263554372395065968 = some 263554372395065968 := by decide +kernel
private theorem endpoint_14_56_p4 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 4 263554372395065968 = some 263554372395065968 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 2 2 263554372395065968 263554372395065968 263554372395065968 endpoint_14_56_w0 endpoint_14_56_w2
private theorem endpoint_14_56_w4 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 4 2 263554372395065968 = some 263554372395065968 := by decide +kernel
private theorem endpoint_14_56_p6 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 6 263554372395065968 = some 263554372395065968 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 4 2 263554372395065968 263554372395065968 263554372395065968 endpoint_14_56_p4 endpoint_14_56_w4
private theorem endpoint_14_56_w6 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 6 2 263554372395065968 = some 263554372395065968 := by decide +kernel
private theorem endpoint_14_56_p8 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 8 263554372395065968 = some 263554372395065968 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 6 2 263554372395065968 263554372395065968 263554372395065968 endpoint_14_56_p6 endpoint_14_56_w6
private theorem endpoint_14_56_w8 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 8 2 263554372395065968 = some 263554372395065968 := by decide +kernel
private theorem endpoint_14_56_p10 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 10 263554372395065968 = some 263554372395065968 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 8 2 263554372395065968 263554372395065968 263554372395065968 endpoint_14_56_p8 endpoint_14_56_w8
private theorem endpoint_14_56_w10 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 10 2 263554372395065968 = some 263554372395065968 := by decide +kernel
private theorem endpoint_14_56_p12 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 12 263554372395065968 = some 263554372395065968 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 10 2 263554372395065968 263554372395065968 263554372395065968 endpoint_14_56_p10 endpoint_14_56_w10
private theorem endpoint_14_56_w12 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 12 1 263554372395065968 = some 263554372395065968 := by decide +kernel
private theorem endpoint_14_56_p13 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 13 263554372395065968 = some 263554372395065968 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 12 1 263554372395065968 263554372395065968 263554372395065968 endpoint_14_56_p12 endpoint_14_56_w12
def endpoint_14_56 : CertifiedEndpoint :=
  ⟨⟨14, 56, 2996⟩, 263554372395065968, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_56_flag endpoint_14_56_sources 13 263554372395065968 263554372395065968 rfl endpoint_14_56_base endpoint_14_56_p13) (by decide)⟩
private def endpoint_14_57_flag : Flag := ⟨14, 57, 2942⟩
private def endpoint_14_57_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_14_57_base : receiptBase endpoint_14_57_flag endpoint_14_57_sources = some 263498379702823261 := by decide +kernel
private theorem endpoint_14_57_w0 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 2 263498379702823261 = some 263498379702823261 := by decide +kernel
private theorem endpoint_14_57_w2 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 2 2 263498379702823261 = some 263498379702823261 := by decide +kernel
private theorem endpoint_14_57_p4 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 4 263498379702823261 = some 263498379702823261 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 2 2 263498379702823261 263498379702823261 263498379702823261 endpoint_14_57_w0 endpoint_14_57_w2
private theorem endpoint_14_57_w4 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 4 2 263498379702823261 = some 263498379702823261 := by decide +kernel
private theorem endpoint_14_57_p6 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 6 263498379702823261 = some 263498379702823261 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 4 2 263498379702823261 263498379702823261 263498379702823261 endpoint_14_57_p4 endpoint_14_57_w4
private theorem endpoint_14_57_w6 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 6 2 263498379702823261 = some 263498379702823261 := by decide +kernel
private theorem endpoint_14_57_p8 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 8 263498379702823261 = some 263498379702823261 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 6 2 263498379702823261 263498379702823261 263498379702823261 endpoint_14_57_p6 endpoint_14_57_w6
private theorem endpoint_14_57_w8 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 8 2 263498379702823261 = some 263498379702823261 := by decide +kernel
private theorem endpoint_14_57_p10 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 10 263498379702823261 = some 263498379702823261 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 8 2 263498379702823261 263498379702823261 263498379702823261 endpoint_14_57_p8 endpoint_14_57_w8
private theorem endpoint_14_57_w10 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 10 2 263498379702823261 = some 263498379702823261 := by decide +kernel
private theorem endpoint_14_57_p12 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 12 263498379702823261 = some 263498379702823261 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 10 2 263498379702823261 263498379702823261 263498379702823261 endpoint_14_57_p10 endpoint_14_57_w10
private theorem endpoint_14_57_w12 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 12 1 263498379702823261 = some 263498379702823261 := by decide +kernel
private theorem endpoint_14_57_p13 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 13 263498379702823261 = some 263498379702823261 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 12 1 263498379702823261 263498379702823261 263498379702823261 endpoint_14_57_p12 endpoint_14_57_w12
def endpoint_14_57 : CertifiedEndpoint :=
  ⟨⟨14, 57, 2942⟩, 263498379702823261, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_14_57_flag endpoint_14_57_sources 13 263498379702823261 263498379702823261 rfl endpoint_14_57_base endpoint_14_57_p13) (by decide)⟩
private def endpoint_14_58_flag : Flag := ⟨14, 58, 2886⟩
private def endpoint_14_58_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_58_base : receiptBase endpoint_14_58_flag endpoint_14_58_sources = some 262843726770748457 := by decide +kernel
private theorem endpoint_14_58_w0 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 2 262843726770748457 = some 262843726770748457 := by decide +kernel
private theorem endpoint_14_58_w2 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 2 2 262843726770748457 = some 262843726770748457 := by decide +kernel
private theorem endpoint_14_58_p4 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 4 262843726770748457 = some 262843726770748457 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 2 2 262843726770748457 262843726770748457 262843726770748457 endpoint_14_58_w0 endpoint_14_58_w2
private theorem endpoint_14_58_w4 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 4 2 262843726770748457 = some 262843726770748457 := by decide +kernel
private theorem endpoint_14_58_p6 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 6 262843726770748457 = some 262843726770748457 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 4 2 262843726770748457 262843726770748457 262843726770748457 endpoint_14_58_p4 endpoint_14_58_w4
private theorem endpoint_14_58_w6 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 6 2 262843726770748457 = some 262843726770748457 := by decide +kernel
private theorem endpoint_14_58_p8 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 8 262843726770748457 = some 262843726770748457 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 6 2 262843726770748457 262843726770748457 262843726770748457 endpoint_14_58_p6 endpoint_14_58_w6
private theorem endpoint_14_58_w8 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 8 2 262843726770748457 = some 262843726770748457 := by decide +kernel
private theorem endpoint_14_58_p10 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 10 262843726770748457 = some 262843726770748457 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 8 2 262843726770748457 262843726770748457 262843726770748457 endpoint_14_58_p8 endpoint_14_58_w8
private theorem endpoint_14_58_w10 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 10 2 262843726770748457 = some 262843726770748457 := by decide +kernel
private theorem endpoint_14_58_p12 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 12 262843726770748457 = some 262843726770748457 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 10 2 262843726770748457 262843726770748457 262843726770748457 endpoint_14_58_p10 endpoint_14_58_w10
private theorem endpoint_14_58_w12 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 12 1 262843726770748457 = some 262843726770748457 := by decide +kernel
private theorem endpoint_14_58_p13 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 13 262843726770748457 = some 262843726770748457 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 12 1 262843726770748457 262843726770748457 262843726770748457 endpoint_14_58_p12 endpoint_14_58_w12
def endpoint_14_58 : CertifiedEndpoint :=
  ⟨⟨14, 58, 2886⟩, 262843726770748457, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_58_flag endpoint_14_58_sources 13 262843726770748457 262843726770748457 rfl endpoint_14_58_base endpoint_14_58_p13) (by decide)⟩
private def endpoint_14_59_flag : Flag := ⟨14, 59, 2828⟩
private def endpoint_14_59_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_14_59_base : receiptBase endpoint_14_59_flag endpoint_14_59_sources = some 263484493245240045 := by decide +kernel
private theorem endpoint_14_59_w0 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 2 263484493245240045 = some 263484493245240045 := by decide +kernel
private theorem endpoint_14_59_w2 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 2 2 263484493245240045 = some 263484493245240045 := by decide +kernel
private theorem endpoint_14_59_p4 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 4 263484493245240045 = some 263484493245240045 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 2 2 263484493245240045 263484493245240045 263484493245240045 endpoint_14_59_w0 endpoint_14_59_w2
private theorem endpoint_14_59_w4 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 4 2 263484493245240045 = some 263484493245240045 := by decide +kernel
private theorem endpoint_14_59_p6 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 6 263484493245240045 = some 263484493245240045 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 4 2 263484493245240045 263484493245240045 263484493245240045 endpoint_14_59_p4 endpoint_14_59_w4
private theorem endpoint_14_59_w6 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 6 2 263484493245240045 = some 263484493245240045 := by decide +kernel
private theorem endpoint_14_59_p8 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 8 263484493245240045 = some 263484493245240045 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 6 2 263484493245240045 263484493245240045 263484493245240045 endpoint_14_59_p6 endpoint_14_59_w6
private theorem endpoint_14_59_w8 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 8 2 263484493245240045 = some 263484493245240045 := by decide +kernel
private theorem endpoint_14_59_p10 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 10 263484493245240045 = some 263484493245240045 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 8 2 263484493245240045 263484493245240045 263484493245240045 endpoint_14_59_p8 endpoint_14_59_w8
private theorem endpoint_14_59_w10 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 10 2 263484493245240045 = some 263484493245240045 := by decide +kernel
private theorem endpoint_14_59_p12 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 12 263484493245240045 = some 263484493245240045 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 10 2 263484493245240045 263484493245240045 263484493245240045 endpoint_14_59_p10 endpoint_14_59_w10
private theorem endpoint_14_59_w12 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 12 1 263484493245240045 = some 263484493245240045 := by decide +kernel
private theorem endpoint_14_59_p13 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 13 263484493245240045 = some 263484493245240045 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 12 1 263484493245240045 263484493245240045 263484493245240045 endpoint_14_59_p12 endpoint_14_59_w12
def endpoint_14_59 : CertifiedEndpoint :=
  ⟨⟨14, 59, 2828⟩, 263484493245240045, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_14_59_flag endpoint_14_59_sources 13 263484493245240045 263484493245240045 rfl endpoint_14_59_base endpoint_14_59_p13) (by decide)⟩
private def endpoint_14_60_flag : Flag := ⟨14, 60, 2768⟩
private def endpoint_14_60_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_60_base : receiptBase endpoint_14_60_flag endpoint_14_60_sources = some 261636389043160640 := by decide +kernel
private theorem endpoint_14_60_w0 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 2 261636389043160640 = some 261636389043160640 := by decide +kernel
private theorem endpoint_14_60_w2 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 2 2 261636389043160640 = some 261636389043160640 := by decide +kernel
private theorem endpoint_14_60_p4 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 4 261636389043160640 = some 261636389043160640 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 2 2 261636389043160640 261636389043160640 261636389043160640 endpoint_14_60_w0 endpoint_14_60_w2
private theorem endpoint_14_60_w4 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 4 2 261636389043160640 = some 261636389043160640 := by decide +kernel
private theorem endpoint_14_60_p6 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 6 261636389043160640 = some 261636389043160640 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 4 2 261636389043160640 261636389043160640 261636389043160640 endpoint_14_60_p4 endpoint_14_60_w4
private theorem endpoint_14_60_w6 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 6 2 261636389043160640 = some 261636389043160640 := by decide +kernel
private theorem endpoint_14_60_p8 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 8 261636389043160640 = some 261636389043160640 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 6 2 261636389043160640 261636389043160640 261636389043160640 endpoint_14_60_p6 endpoint_14_60_w6
private theorem endpoint_14_60_w8 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 8 2 261636389043160640 = some 261636389043160640 := by decide +kernel
private theorem endpoint_14_60_p10 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 10 261636389043160640 = some 261636389043160640 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 8 2 261636389043160640 261636389043160640 261636389043160640 endpoint_14_60_p8 endpoint_14_60_w8
private theorem endpoint_14_60_w10 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 10 2 261636389043160640 = some 261636389043160640 := by decide +kernel
private theorem endpoint_14_60_p12 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 12 261636389043160640 = some 261636389043160640 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 10 2 261636389043160640 261636389043160640 261636389043160640 endpoint_14_60_p10 endpoint_14_60_w10
private theorem endpoint_14_60_w12 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 12 1 261636389043160640 = some 261636389043160640 := by decide +kernel
private theorem endpoint_14_60_p13 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 13 261636389043160640 = some 261636389043160640 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 12 1 261636389043160640 261636389043160640 261636389043160640 endpoint_14_60_p12 endpoint_14_60_w12
def endpoint_14_60 : CertifiedEndpoint :=
  ⟨⟨14, 60, 2768⟩, 261636389043160640, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_60_flag endpoint_14_60_sources 13 261636389043160640 261636389043160640 rfl endpoint_14_60_base endpoint_14_60_p13) (by decide)⟩
private def endpoint_14_61_flag : Flag := ⟨14, 61, 2707⟩
private def endpoint_14_61_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_61_base : receiptBase endpoint_14_61_flag endpoint_14_61_sources = some 259704228413582404 := by decide +kernel
private theorem endpoint_14_61_w0 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 2 259704228413582404 = some 259704228413582404 := by decide +kernel
private theorem endpoint_14_61_w2 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 2 2 259704228413582404 = some 259704228413582404 := by decide +kernel
private theorem endpoint_14_61_p4 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 4 259704228413582404 = some 259704228413582404 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 2 2 259704228413582404 259704228413582404 259704228413582404 endpoint_14_61_w0 endpoint_14_61_w2
private theorem endpoint_14_61_w4 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 4 2 259704228413582404 = some 259704228413582404 := by decide +kernel
private theorem endpoint_14_61_p6 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 6 259704228413582404 = some 259704228413582404 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 4 2 259704228413582404 259704228413582404 259704228413582404 endpoint_14_61_p4 endpoint_14_61_w4
private theorem endpoint_14_61_w6 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 6 2 259704228413582404 = some 259704228413582404 := by decide +kernel
private theorem endpoint_14_61_p8 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 8 259704228413582404 = some 259704228413582404 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 6 2 259704228413582404 259704228413582404 259704228413582404 endpoint_14_61_p6 endpoint_14_61_w6
private theorem endpoint_14_61_w8 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 8 2 259704228413582404 = some 259704228413582404 := by decide +kernel
private theorem endpoint_14_61_p10 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 10 259704228413582404 = some 259704228413582404 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 8 2 259704228413582404 259704228413582404 259704228413582404 endpoint_14_61_p8 endpoint_14_61_w8
private theorem endpoint_14_61_w10 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 10 2 259704228413582404 = some 259704228413582404 := by decide +kernel
private theorem endpoint_14_61_p12 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 12 259704228413582404 = some 259704228413582404 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 10 2 259704228413582404 259704228413582404 259704228413582404 endpoint_14_61_p10 endpoint_14_61_w10
private theorem endpoint_14_61_w12 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 12 1 259704228413582404 = some 259704228413582404 := by decide +kernel
private theorem endpoint_14_61_p13 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 13 259704228413582404 = some 259704228413582404 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 12 1 259704228413582404 259704228413582404 259704228413582404 endpoint_14_61_p12 endpoint_14_61_w12
def endpoint_14_61 : CertifiedEndpoint :=
  ⟨⟨14, 61, 2707⟩, 259704228413582404, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_61_flag endpoint_14_61_sources 13 259704228413582404 259704228413582404 rfl endpoint_14_61_base endpoint_14_61_p13) (by decide)⟩
private def endpoint_14_62_flag : Flag := ⟨14, 62, 2642⟩
private def endpoint_14_62_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_62_base : receiptBase endpoint_14_62_flag endpoint_14_62_sources = some 262768818956978611 := by decide +kernel
private theorem endpoint_14_62_w0 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 2 262768818956978611 = some 262768818956978611 := by decide +kernel
private theorem endpoint_14_62_w2 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 2 2 262768818956978611 = some 262768818956978611 := by decide +kernel
private theorem endpoint_14_62_p4 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 4 262768818956978611 = some 262768818956978611 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 2 2 262768818956978611 262768818956978611 262768818956978611 endpoint_14_62_w0 endpoint_14_62_w2
private theorem endpoint_14_62_w4 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 4 2 262768818956978611 = some 262768818956978611 := by decide +kernel
private theorem endpoint_14_62_p6 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 6 262768818956978611 = some 262768818956978611 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 4 2 262768818956978611 262768818956978611 262768818956978611 endpoint_14_62_p4 endpoint_14_62_w4
private theorem endpoint_14_62_w6 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 6 2 262768818956978611 = some 262768818956978611 := by decide +kernel
private theorem endpoint_14_62_p8 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 8 262768818956978611 = some 262768818956978611 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 6 2 262768818956978611 262768818956978611 262768818956978611 endpoint_14_62_p6 endpoint_14_62_w6
private theorem endpoint_14_62_w8 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 8 2 262768818956978611 = some 262768818956978611 := by decide +kernel
private theorem endpoint_14_62_p10 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 10 262768818956978611 = some 262768818956978611 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 8 2 262768818956978611 262768818956978611 262768818956978611 endpoint_14_62_p8 endpoint_14_62_w8
private theorem endpoint_14_62_w10 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 10 2 262768818956978611 = some 262768818956978611 := by decide +kernel
private theorem endpoint_14_62_p12 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 12 262768818956978611 = some 262768818956978611 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 10 2 262768818956978611 262768818956978611 262768818956978611 endpoint_14_62_p10 endpoint_14_62_w10
private theorem endpoint_14_62_w12 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 12 1 262768818956978611 = some 262768818956978611 := by decide +kernel
private theorem endpoint_14_62_p13 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 13 262768818956978611 = some 262768818956978611 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 12 1 262768818956978611 262768818956978611 262768818956978611 endpoint_14_62_p12 endpoint_14_62_w12
def endpoint_14_62 : CertifiedEndpoint :=
  ⟨⟨14, 62, 2642⟩, 262768818956978611, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_62_flag endpoint_14_62_sources 13 262768818956978611 262768818956978611 rfl endpoint_14_62_base endpoint_14_62_p13) (by decide)⟩
private def endpoint_14_63_flag : Flag := ⟨14, 63, 2576⟩
private def endpoint_14_63_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_63_base : receiptBase endpoint_14_63_flag endpoint_14_63_sources = some 259164778885974119 := by decide +kernel
private theorem endpoint_14_63_w0 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 2 259164778885974119 = some 259164778885974119 := by decide +kernel
private theorem endpoint_14_63_w2 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 2 2 259164778885974119 = some 259164778885974119 := by decide +kernel
private theorem endpoint_14_63_p4 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 4 259164778885974119 = some 259164778885974119 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 2 2 259164778885974119 259164778885974119 259164778885974119 endpoint_14_63_w0 endpoint_14_63_w2
private theorem endpoint_14_63_w4 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 4 2 259164778885974119 = some 259164778885974119 := by decide +kernel
private theorem endpoint_14_63_p6 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 6 259164778885974119 = some 259164778885974119 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 4 2 259164778885974119 259164778885974119 259164778885974119 endpoint_14_63_p4 endpoint_14_63_w4
private theorem endpoint_14_63_w6 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 6 2 259164778885974119 = some 259164778885974119 := by decide +kernel
private theorem endpoint_14_63_p8 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 8 259164778885974119 = some 259164778885974119 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 6 2 259164778885974119 259164778885974119 259164778885974119 endpoint_14_63_p6 endpoint_14_63_w6
private theorem endpoint_14_63_w8 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 8 2 259164778885974119 = some 259164778885974119 := by decide +kernel
private theorem endpoint_14_63_p10 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 10 259164778885974119 = some 259164778885974119 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 8 2 259164778885974119 259164778885974119 259164778885974119 endpoint_14_63_p8 endpoint_14_63_w8
private theorem endpoint_14_63_w10 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 10 2 259164778885974119 = some 259164778885974119 := by decide +kernel
private theorem endpoint_14_63_p12 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 12 259164778885974119 = some 259164778885974119 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 10 2 259164778885974119 259164778885974119 259164778885974119 endpoint_14_63_p10 endpoint_14_63_w10
private theorem endpoint_14_63_w12 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 12 1 259164778885974119 = some 259164778885974119 := by decide +kernel
private theorem endpoint_14_63_p13 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 13 259164778885974119 = some 259164778885974119 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 12 1 259164778885974119 259164778885974119 259164778885974119 endpoint_14_63_p12 endpoint_14_63_w12
def endpoint_14_63 : CertifiedEndpoint :=
  ⟨⟨14, 63, 2576⟩, 259164778885974119, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_63_flag endpoint_14_63_sources 13 259164778885974119 259164778885974119 rfl endpoint_14_63_base endpoint_14_63_p13) (by decide)⟩
private def endpoint_14_64_flag : Flag := ⟨14, 64, 2507⟩
private def endpoint_14_64_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_64_base : receiptBase endpoint_14_64_flag endpoint_14_64_sources = some 262040716691970406 := by decide +kernel
private theorem endpoint_14_64_w0 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 2 262040716691970406 = some 262040716691970406 := by decide +kernel
private theorem endpoint_14_64_w2 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 2 2 262040716691970406 = some 262040716691970406 := by decide +kernel
private theorem endpoint_14_64_p4 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 4 262040716691970406 = some 262040716691970406 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 2 2 262040716691970406 262040716691970406 262040716691970406 endpoint_14_64_w0 endpoint_14_64_w2
private theorem endpoint_14_64_w4 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 4 2 262040716691970406 = some 262040716691970406 := by decide +kernel
private theorem endpoint_14_64_p6 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 6 262040716691970406 = some 262040716691970406 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 4 2 262040716691970406 262040716691970406 262040716691970406 endpoint_14_64_p4 endpoint_14_64_w4
private theorem endpoint_14_64_w6 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 6 2 262040716691970406 = some 262040716691970406 := by decide +kernel
private theorem endpoint_14_64_p8 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 8 262040716691970406 = some 262040716691970406 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 6 2 262040716691970406 262040716691970406 262040716691970406 endpoint_14_64_p6 endpoint_14_64_w6
private theorem endpoint_14_64_w8 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 8 2 262040716691970406 = some 262040716691970406 := by decide +kernel
private theorem endpoint_14_64_p10 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 10 262040716691970406 = some 262040716691970406 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 8 2 262040716691970406 262040716691970406 262040716691970406 endpoint_14_64_p8 endpoint_14_64_w8
private theorem endpoint_14_64_w10 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 10 2 262040716691970406 = some 262040716691970406 := by decide +kernel
private theorem endpoint_14_64_p12 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 12 262040716691970406 = some 262040716691970406 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 10 2 262040716691970406 262040716691970406 262040716691970406 endpoint_14_64_p10 endpoint_14_64_w10
private theorem endpoint_14_64_w12 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 12 1 262040716691970406 = some 262040716691970406 := by decide +kernel
private theorem endpoint_14_64_p13 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 13 262040716691970406 = some 262040716691970406 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 12 1 262040716691970406 262040716691970406 262040716691970406 endpoint_14_64_p12 endpoint_14_64_w12
def endpoint_14_64 : CertifiedEndpoint :=
  ⟨⟨14, 64, 2507⟩, 262040716691970406, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_64_flag endpoint_14_64_sources 13 262040716691970406 262040716691970406 rfl endpoint_14_64_base endpoint_14_64_p13) (by decide)⟩
private def endpoint_14_65_flag : Flag := ⟨14, 65, 2436⟩
private def endpoint_14_65_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_65_base : receiptBase endpoint_14_65_flag endpoint_14_65_sources = some 258304168237290401 := by decide +kernel
private theorem endpoint_14_65_w0 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 2 258304168237290401 = some 258304168237290401 := by decide +kernel
private theorem endpoint_14_65_w2 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 2 2 258304168237290401 = some 258304168237290401 := by decide +kernel
private theorem endpoint_14_65_p4 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 4 258304168237290401 = some 258304168237290401 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 2 2 258304168237290401 258304168237290401 258304168237290401 endpoint_14_65_w0 endpoint_14_65_w2
private theorem endpoint_14_65_w4 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 4 2 258304168237290401 = some 258304168237290401 := by decide +kernel
private theorem endpoint_14_65_p6 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 6 258304168237290401 = some 258304168237290401 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 4 2 258304168237290401 258304168237290401 258304168237290401 endpoint_14_65_p4 endpoint_14_65_w4
private theorem endpoint_14_65_w6 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 6 2 258304168237290401 = some 258304168237290401 := by decide +kernel
private theorem endpoint_14_65_p8 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 8 258304168237290401 = some 258304168237290401 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 6 2 258304168237290401 258304168237290401 258304168237290401 endpoint_14_65_p6 endpoint_14_65_w6
private theorem endpoint_14_65_w8 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 8 2 258304168237290401 = some 258304168237290401 := by decide +kernel
private theorem endpoint_14_65_p10 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 10 258304168237290401 = some 258304168237290401 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 8 2 258304168237290401 258304168237290401 258304168237290401 endpoint_14_65_p8 endpoint_14_65_w8
private theorem endpoint_14_65_w10 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 10 2 258304168237290401 = some 258304168237290401 := by decide +kernel
private theorem endpoint_14_65_p12 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 12 258304168237290401 = some 258304168237290401 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 10 2 258304168237290401 258304168237290401 258304168237290401 endpoint_14_65_p10 endpoint_14_65_w10
private theorem endpoint_14_65_w12 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 12 1 258304168237290401 = some 258304168237290401 := by decide +kernel
private theorem endpoint_14_65_p13 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 13 258304168237290401 = some 258304168237290401 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 12 1 258304168237290401 258304168237290401 258304168237290401 endpoint_14_65_p12 endpoint_14_65_w12
def endpoint_14_65 : CertifiedEndpoint :=
  ⟨⟨14, 65, 2436⟩, 258304168237290401, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_65_flag endpoint_14_65_sources 13 258304168237290401 258304168237290401 rfl endpoint_14_65_base endpoint_14_65_p13) (by decide)⟩
private def endpoint_14_66_flag : Flag := ⟨14, 66, 2362⟩
private def endpoint_14_66_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_14_66_base : receiptBase endpoint_14_66_flag endpoint_14_66_sources = some 255340286772216569 := by decide +kernel
private theorem endpoint_14_66_w0 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 2 255340286772216569 = some 255340286772216569 := by decide +kernel
private theorem endpoint_14_66_w2 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 2 2 255340286772216569 = some 255340286772216569 := by decide +kernel
private theorem endpoint_14_66_p4 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 4 255340286772216569 = some 255340286772216569 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 2 2 255340286772216569 255340286772216569 255340286772216569 endpoint_14_66_w0 endpoint_14_66_w2
private theorem endpoint_14_66_w4 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 4 2 255340286772216569 = some 255340286772216569 := by decide +kernel
private theorem endpoint_14_66_p6 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 6 255340286772216569 = some 255340286772216569 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 4 2 255340286772216569 255340286772216569 255340286772216569 endpoint_14_66_p4 endpoint_14_66_w4
private theorem endpoint_14_66_w6 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 6 2 255340286772216569 = some 255340286772216569 := by decide +kernel
private theorem endpoint_14_66_p8 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 8 255340286772216569 = some 255340286772216569 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 6 2 255340286772216569 255340286772216569 255340286772216569 endpoint_14_66_p6 endpoint_14_66_w6
private theorem endpoint_14_66_w8 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 8 2 255340286772216569 = some 255340286772216569 := by decide +kernel
private theorem endpoint_14_66_p10 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 10 255340286772216569 = some 255340286772216569 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 8 2 255340286772216569 255340286772216569 255340286772216569 endpoint_14_66_p8 endpoint_14_66_w8
private theorem endpoint_14_66_w10 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 10 2 255340286772216569 = some 255340286772216569 := by decide +kernel
private theorem endpoint_14_66_p12 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 12 255340286772216569 = some 255340286772216569 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 10 2 255340286772216569 255340286772216569 255340286772216569 endpoint_14_66_p10 endpoint_14_66_w10
private theorem endpoint_14_66_w12 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 12 1 255340286772216569 = some 255340286772216569 := by decide +kernel
private theorem endpoint_14_66_p13 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 13 255340286772216569 = some 255340286772216569 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 12 1 255340286772216569 255340286772216569 255340286772216569 endpoint_14_66_p12 endpoint_14_66_w12
def endpoint_14_66 : CertifiedEndpoint :=
  ⟨⟨14, 66, 2362⟩, 255340286772216569, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_14_66_flag endpoint_14_66_sources 13 255340286772216569 255340286772216569 rfl endpoint_14_66_base endpoint_14_66_p13) (by decide)⟩
private def endpoint_14_67_flag : Flag := ⟨14, 67, 2285⟩
private def endpoint_14_67_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_14_67_base : receiptBase endpoint_14_67_flag endpoint_14_67_sources = some 250518982406598082 := by decide +kernel
private theorem endpoint_14_67_w0 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 2 250518982406598082 = some 250518982406598082 := by decide +kernel
private theorem endpoint_14_67_w2 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 2 2 250518982406598082 = some 250518982406598082 := by decide +kernel
private theorem endpoint_14_67_p4 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 4 250518982406598082 = some 250518982406598082 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 2 2 250518982406598082 250518982406598082 250518982406598082 endpoint_14_67_w0 endpoint_14_67_w2
private theorem endpoint_14_67_w4 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 4 2 250518982406598082 = some 250518982406598082 := by decide +kernel
private theorem endpoint_14_67_p6 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 6 250518982406598082 = some 250518982406598082 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 4 2 250518982406598082 250518982406598082 250518982406598082 endpoint_14_67_p4 endpoint_14_67_w4
private theorem endpoint_14_67_w6 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 6 2 250518982406598082 = some 250518982406598082 := by decide +kernel
private theorem endpoint_14_67_p8 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 8 250518982406598082 = some 250518982406598082 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 6 2 250518982406598082 250518982406598082 250518982406598082 endpoint_14_67_p6 endpoint_14_67_w6
private theorem endpoint_14_67_w8 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 8 2 250518982406598082 = some 250518982406598082 := by decide +kernel
private theorem endpoint_14_67_p10 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 10 250518982406598082 = some 250518982406598082 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 8 2 250518982406598082 250518982406598082 250518982406598082 endpoint_14_67_p8 endpoint_14_67_w8
private theorem endpoint_14_67_w10 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 10 2 250518982406598082 = some 250518982406598082 := by decide +kernel
private theorem endpoint_14_67_p12 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 12 250518982406598082 = some 250518982406598082 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 10 2 250518982406598082 250518982406598082 250518982406598082 endpoint_14_67_p10 endpoint_14_67_w10
private theorem endpoint_14_67_w12 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 12 1 250518982406598082 = some 250518982406598082 := by decide +kernel
private theorem endpoint_14_67_p13 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 13 250518982406598082 = some 250518982406598082 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 12 1 250518982406598082 250518982406598082 250518982406598082 endpoint_14_67_p12 endpoint_14_67_w12
def endpoint_14_67 : CertifiedEndpoint :=
  ⟨⟨14, 67, 2285⟩, 250518982406598082, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_14_67_flag endpoint_14_67_sources 13 250518982406598082 250518982406598082 rfl endpoint_14_67_base endpoint_14_67_p13) (by decide)⟩
private def endpoint_14_68_flag : Flag := ⟨14, 68, 2206⟩
private def endpoint_14_68_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_14_68_base : receiptBase endpoint_14_68_flag endpoint_14_68_sources = some 245398178337487454 := by decide +kernel
private theorem endpoint_14_68_w0 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 2 245398178337487454 = some 245398178337487454 := by decide +kernel
private theorem endpoint_14_68_w2 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 2 2 245398178337487454 = some 245398178337487454 := by decide +kernel
private theorem endpoint_14_68_p4 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 4 245398178337487454 = some 245398178337487454 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 2 2 245398178337487454 245398178337487454 245398178337487454 endpoint_14_68_w0 endpoint_14_68_w2
private theorem endpoint_14_68_w4 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 4 2 245398178337487454 = some 245398178337487454 := by decide +kernel
private theorem endpoint_14_68_p6 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 6 245398178337487454 = some 245398178337487454 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 4 2 245398178337487454 245398178337487454 245398178337487454 endpoint_14_68_p4 endpoint_14_68_w4
private theorem endpoint_14_68_w6 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 6 2 245398178337487454 = some 245398178337487454 := by decide +kernel
private theorem endpoint_14_68_p8 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 8 245398178337487454 = some 245398178337487454 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 6 2 245398178337487454 245398178337487454 245398178337487454 endpoint_14_68_p6 endpoint_14_68_w6
private theorem endpoint_14_68_w8 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 8 2 245398178337487454 = some 245398178337487454 := by decide +kernel
private theorem endpoint_14_68_p10 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 10 245398178337487454 = some 245398178337487454 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 8 2 245398178337487454 245398178337487454 245398178337487454 endpoint_14_68_p8 endpoint_14_68_w8
private theorem endpoint_14_68_w10 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 10 2 245398178337487454 = some 245398178337487454 := by decide +kernel
private theorem endpoint_14_68_p12 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 12 245398178337487454 = some 245398178337487454 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 10 2 245398178337487454 245398178337487454 245398178337487454 endpoint_14_68_p10 endpoint_14_68_w10
private theorem endpoint_14_68_w12 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 12 1 245398178337487454 = some 245398178337487454 := by decide +kernel
private theorem endpoint_14_68_p13 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 13 245398178337487454 = some 245398178337487454 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 12 1 245398178337487454 245398178337487454 245398178337487454 endpoint_14_68_p12 endpoint_14_68_w12
def endpoint_14_68 : CertifiedEndpoint :=
  ⟨⟨14, 68, 2206⟩, 245398178337487454, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_14_68_flag endpoint_14_68_sources 13 245398178337487454 245398178337487454 rfl endpoint_14_68_base endpoint_14_68_p13) (by decide)⟩
private def endpoint_14_69_flag : Flag := ⟨14, 69, 2124⟩
private def endpoint_14_69_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_14_69_base : receiptBase endpoint_14_69_flag endpoint_14_69_sources = some 240972600596809263 := by decide +kernel
private theorem endpoint_14_69_w0 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 2 240972600596809263 = some 240972600596809263 := by decide +kernel
private theorem endpoint_14_69_w2 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 2 2 240972600596809263 = some 240972600596809263 := by decide +kernel
private theorem endpoint_14_69_p4 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 4 240972600596809263 = some 240972600596809263 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 2 2 240972600596809263 240972600596809263 240972600596809263 endpoint_14_69_w0 endpoint_14_69_w2
private theorem endpoint_14_69_w4 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 4 2 240972600596809263 = some 240972600596809263 := by decide +kernel
private theorem endpoint_14_69_p6 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 6 240972600596809263 = some 240972600596809263 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 4 2 240972600596809263 240972600596809263 240972600596809263 endpoint_14_69_p4 endpoint_14_69_w4
private theorem endpoint_14_69_w6 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 6 2 240972600596809263 = some 240972600596809263 := by decide +kernel
private theorem endpoint_14_69_p8 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 8 240972600596809263 = some 240972600596809263 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 6 2 240972600596809263 240972600596809263 240972600596809263 endpoint_14_69_p6 endpoint_14_69_w6
private theorem endpoint_14_69_w8 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 8 2 240972600596809263 = some 240972600596809263 := by decide +kernel
private theorem endpoint_14_69_p10 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 10 240972600596809263 = some 240972600596809263 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 8 2 240972600596809263 240972600596809263 240972600596809263 endpoint_14_69_p8 endpoint_14_69_w8
private theorem endpoint_14_69_w10 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 10 2 240972600596809263 = some 240972600596809263 := by decide +kernel
private theorem endpoint_14_69_p12 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 12 240972600596809263 = some 240972600596809263 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 10 2 240972600596809263 240972600596809263 240972600596809263 endpoint_14_69_p10 endpoint_14_69_w10
private theorem endpoint_14_69_w12 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 12 1 240972600596809263 = some 240972600596809263 := by decide +kernel
private theorem endpoint_14_69_p13 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 13 240972600596809263 = some 240972600596809263 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 12 1 240972600596809263 240972600596809263 240972600596809263 endpoint_14_69_p12 endpoint_14_69_w12
def endpoint_14_69 : CertifiedEndpoint :=
  ⟨⟨14, 69, 2124⟩, 240972600596809263, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_14_69_flag endpoint_14_69_sources 13 240972600596809263 240972600596809263 rfl endpoint_14_69_base endpoint_14_69_p13) (by decide)⟩
private def endpoint_14_70_flag : Flag := ⟨14, 70, 2039⟩
private def endpoint_14_70_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_14_70_base : receiptBase endpoint_14_70_flag endpoint_14_70_sources = some 236122399478873090 := by decide +kernel
private theorem endpoint_14_70_w0 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 2 236122399478873090 = some 236122399478873090 := by decide +kernel
private theorem endpoint_14_70_w2 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 2 2 236122399478873090 = some 236122399478873090 := by decide +kernel
private theorem endpoint_14_70_p4 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 4 236122399478873090 = some 236122399478873090 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 2 2 236122399478873090 236122399478873090 236122399478873090 endpoint_14_70_w0 endpoint_14_70_w2
private theorem endpoint_14_70_w4 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 4 2 236122399478873090 = some 236122399478873090 := by decide +kernel
private theorem endpoint_14_70_p6 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 6 236122399478873090 = some 236122399478873090 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 4 2 236122399478873090 236122399478873090 236122399478873090 endpoint_14_70_p4 endpoint_14_70_w4
private theorem endpoint_14_70_w6 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 6 2 236122399478873090 = some 236122399478873090 := by decide +kernel
private theorem endpoint_14_70_p8 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 8 236122399478873090 = some 236122399478873090 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 6 2 236122399478873090 236122399478873090 236122399478873090 endpoint_14_70_p6 endpoint_14_70_w6
private theorem endpoint_14_70_w8 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 8 2 236122399478873090 = some 236122399478873090 := by decide +kernel
private theorem endpoint_14_70_p10 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 10 236122399478873090 = some 236122399478873090 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 8 2 236122399478873090 236122399478873090 236122399478873090 endpoint_14_70_p8 endpoint_14_70_w8
private theorem endpoint_14_70_w10 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 10 2 236122399478873090 = some 236122399478873090 := by decide +kernel
private theorem endpoint_14_70_p12 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 12 236122399478873090 = some 236122399478873090 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 10 2 236122399478873090 236122399478873090 236122399478873090 endpoint_14_70_p10 endpoint_14_70_w10
private theorem endpoint_14_70_w12 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 12 1 236122399478873090 = some 236122399478873090 := by decide +kernel
private theorem endpoint_14_70_p13 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 13 236122399478873090 = some 236122399478873090 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 12 1 236122399478873090 236122399478873090 236122399478873090 endpoint_14_70_p12 endpoint_14_70_w12
def endpoint_14_70 : CertifiedEndpoint :=
  ⟨⟨14, 70, 2039⟩, 236122399478873090, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_14_70_flag endpoint_14_70_sources 13 236122399478873090 236122399478873090 rfl endpoint_14_70_base endpoint_14_70_p13) (by decide)⟩
private def endpoint_14_71_flag : Flag := ⟨14, 71, 1951⟩
private def endpoint_14_71_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_14_71_base : receiptBase endpoint_14_71_flag endpoint_14_71_sources = some 230633215944200945 := by decide +kernel
private theorem endpoint_14_71_w0 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 2 230633215944200945 = some 230633215944200945 := by decide +kernel
private theorem endpoint_14_71_w2 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 2 2 230633215944200945 = some 230633215944200945 := by decide +kernel
private theorem endpoint_14_71_p4 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 4 230633215944200945 = some 230633215944200945 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 2 2 230633215944200945 230633215944200945 230633215944200945 endpoint_14_71_w0 endpoint_14_71_w2
private theorem endpoint_14_71_w4 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 4 2 230633215944200945 = some 230633215944200945 := by decide +kernel
private theorem endpoint_14_71_p6 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 6 230633215944200945 = some 230633215944200945 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 4 2 230633215944200945 230633215944200945 230633215944200945 endpoint_14_71_p4 endpoint_14_71_w4
private theorem endpoint_14_71_w6 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 6 2 230633215944200945 = some 230633215944200945 := by decide +kernel
private theorem endpoint_14_71_p8 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 8 230633215944200945 = some 230633215944200945 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 6 2 230633215944200945 230633215944200945 230633215944200945 endpoint_14_71_p6 endpoint_14_71_w6
private theorem endpoint_14_71_w8 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 8 2 230633215944200945 = some 230633215944200945 := by decide +kernel
private theorem endpoint_14_71_p10 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 10 230633215944200945 = some 230633215944200945 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 8 2 230633215944200945 230633215944200945 230633215944200945 endpoint_14_71_p8 endpoint_14_71_w8
private theorem endpoint_14_71_w10 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 10 2 230633215944200945 = some 230633215944200945 := by decide +kernel
private theorem endpoint_14_71_p12 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 12 230633215944200945 = some 230633215944200945 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 10 2 230633215944200945 230633215944200945 230633215944200945 endpoint_14_71_p10 endpoint_14_71_w10
private theorem endpoint_14_71_w12 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 12 1 230633215944200945 = some 230633215944200945 := by decide +kernel
private theorem endpoint_14_71_p13 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 13 230633215944200945 = some 230633215944200945 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 12 1 230633215944200945 230633215944200945 230633215944200945 endpoint_14_71_p12 endpoint_14_71_w12
def endpoint_14_71 : CertifiedEndpoint :=
  ⟨⟨14, 71, 1951⟩, 230633215944200945, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_14_71_flag endpoint_14_71_sources 13 230633215944200945 230633215944200945 rfl endpoint_14_71_base endpoint_14_71_p13) (by decide)⟩

def endpointBlock09 : List CertifiedEndpoint := [
  endpoint_13_24, endpoint_13_25, endpoint_13_26, endpoint_13_27, endpoint_13_28, endpoint_13_29, endpoint_13_30,
  endpoint_13_31, endpoint_13_32, endpoint_13_33, endpoint_13_34, endpoint_13_35, endpoint_13_36, endpoint_13_37,
  endpoint_13_38, endpoint_13_39, endpoint_13_40, endpoint_13_41, endpoint_13_42, endpoint_13_43, endpoint_13_44,
  endpoint_13_45, endpoint_13_46, endpoint_13_47, endpoint_13_48, endpoint_13_49, endpoint_13_50, endpoint_13_51,
  endpoint_13_52, endpoint_13_53, endpoint_13_54, endpoint_13_55, endpoint_13_56, endpoint_13_57, endpoint_13_58,
  endpoint_13_59, endpoint_13_60, endpoint_13_61, endpoint_13_62, endpoint_13_63, endpoint_13_64, endpoint_13_65,
  endpoint_13_66, endpoint_13_67, endpoint_13_68, endpoint_13_69, endpoint_13_70, endpoint_13_71, endpoint_13_72,
  endpoint_13_73, endpoint_13_74, endpoint_13_75, endpoint_13_76, endpoint_13_77, endpoint_13_78, endpoint_13_79,
  endpoint_13_80, endpoint_13_81, endpoint_13_82, endpoint_13_83, endpoint_13_84, endpoint_13_85, endpoint_13_86,
  endpoint_13_87, endpoint_13_88, endpoint_13_89, endpoint_14_14, endpoint_14_15, endpoint_14_16, endpoint_14_17,
  endpoint_14_18, endpoint_14_19, endpoint_14_20, endpoint_14_21, endpoint_14_22, endpoint_14_23, endpoint_14_24,
  endpoint_14_25, endpoint_14_26, endpoint_14_27, endpoint_14_28, endpoint_14_29, endpoint_14_30, endpoint_14_31,
  endpoint_14_32, endpoint_14_33, endpoint_14_34, endpoint_14_35, endpoint_14_36, endpoint_14_37, endpoint_14_38,
  endpoint_14_39, endpoint_14_40, endpoint_14_41, endpoint_14_42, endpoint_14_43, endpoint_14_44, endpoint_14_45,
  endpoint_14_46, endpoint_14_47, endpoint_14_48, endpoint_14_49, endpoint_14_50, endpoint_14_51, endpoint_14_52,
  endpoint_14_53, endpoint_14_54, endpoint_14_55, endpoint_14_56, endpoint_14_57, endpoint_14_58, endpoint_14_59,
  endpoint_14_60, endpoint_14_61, endpoint_14_62, endpoint_14_63, endpoint_14_64, endpoint_14_65, endpoint_14_66,
  endpoint_14_67, endpoint_14_68, endpoint_14_69, endpoint_14_70, endpoint_14_71
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
