import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def endpoint_9_92 : CertifiedEndpoint :=
  ⟨⟨9, 92, 392⟩, 65728350203400396, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_93 : CertifiedEndpoint :=
  ⟨⟨9, 93, 243⟩, 37551370727901924, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_10 : CertifiedEndpoint :=
  ⟨⟨10, 10, 4873⟩, 69962113986840053, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_11 : CertifiedEndpoint :=
  ⟨⟨10, 11, 4852⟩, 73526735275628572, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_12 : CertifiedEndpoint :=
  ⟨⟨10, 12, 4830⟩, 77041825716325330, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_13 : CertifiedEndpoint :=
  ⟨⟨10, 13, 4809⟩, 88490253654638034, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_14 : CertifiedEndpoint :=
  ⟨⟨10, 14, 4787⟩, 99812148649125177, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_15 : CertifiedEndpoint :=
  ⟨⟨10, 15, 4765⟩, 111023488407325770, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_16 : CertifiedEndpoint :=
  ⟨⟨10, 16, 4742⟩, 122098468089586442, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_17 : CertifiedEndpoint :=
  ⟨⟨10, 17, 4720⟩, 133086240592185345, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_18 : CertifiedEndpoint :=
  ⟨⟨10, 18, 4697⟩, 143932739452787147, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_19 : CertifiedEndpoint :=
  ⟨⟨10, 19, 4674⟩, 154663769511045219, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_20 : CertifiedEndpoint :=
  ⟨⟨10, 20, 4651⟩, 165279330766959561, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_21 : CertifiedEndpoint :=
  ⟨⟨10, 21, 4627⟩, 175741334465733852, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_22 : CertifiedEndpoint :=
  ⟨⟨10, 22, 4603⟩, 186082955796107233, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_23 : CertifiedEndpoint :=
  ⟨⟨10, 23, 4579⟩, 196304194758079704, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_24 : CertifiedEndpoint :=
  ⟨⟨10, 24, 4555⟩, 206405051351651265, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_25 : CertifiedEndpoint :=
  ⟨⟨10, 25, 4531⟩, 216385525576821916, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_26 : CertifiedEndpoint :=
  ⟨⟨10, 26, 4506⟩, 226195244763652386, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_27 : CertifiedEndpoint :=
  ⟨⟨10, 27, 4481⟩, 235879668016024766, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_28 : CertifiedEndpoint :=
  ⟨⟨10, 28, 4455⟩, 245383509097942605, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_29 : CertifiedEndpoint :=
  ⟨⟨10, 29, 4429⟩, 254757140679345174, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_30 : CertifiedEndpoint :=
  ⟨⟨10, 30, 4403⟩, 264000562760232473, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_10_31_flag : Flag := ⟨10, 31, 4377⟩
private def endpoint_10_31_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_31_base : receiptBase endpoint_10_31_flag endpoint_10_31_sources = some 184756770543717053 := by decide +kernel
private theorem endpoint_10_31_w0 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 0 2 184756770543717053 = some 184756770543717053 := by decide +kernel
private theorem endpoint_10_31_w2 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 2 2 184756770543717053 = some 184756770543717053 := by decide +kernel
private theorem endpoint_10_31_p4 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 0 4 184756770543717053 = some 184756770543717053 :=
  join_receipt_window endpoint_10_31_flag endpoint_10_31_sources 0 2 2 184756770543717053 184756770543717053 184756770543717053 endpoint_10_31_w0 endpoint_10_31_w2
private theorem endpoint_10_31_w4 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 4 2 184756770543717053 = some 184756770543717053 := by decide +kernel
private theorem endpoint_10_31_p6 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 0 6 184756770543717053 = some 184756770543717053 :=
  join_receipt_window endpoint_10_31_flag endpoint_10_31_sources 0 4 2 184756770543717053 184756770543717053 184756770543717053 endpoint_10_31_p4 endpoint_10_31_w4
private theorem endpoint_10_31_w6 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 6 2 184756770543717053 = some 184756770543717053 := by decide +kernel
private theorem endpoint_10_31_p8 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 0 8 184756770543717053 = some 184756770543717053 :=
  join_receipt_window endpoint_10_31_flag endpoint_10_31_sources 0 6 2 184756770543717053 184756770543717053 184756770543717053 endpoint_10_31_p6 endpoint_10_31_w6
private theorem endpoint_10_31_w8 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 8 1 184756770543717053 = some 184756770543717053 := by decide +kernel
private theorem endpoint_10_31_p9 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 0 9 184756770543717053 = some 184756770543717053 :=
  join_receipt_window endpoint_10_31_flag endpoint_10_31_sources 0 8 1 184756770543717053 184756770543717053 184756770543717053 endpoint_10_31_p8 endpoint_10_31_w8
def endpoint_10_31 : CertifiedEndpoint :=
  ⟨⟨10, 31, 4377⟩, 184756770543717053, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_31_flag endpoint_10_31_sources 9 184756770543717053 184756770543717053 rfl endpoint_10_31_base endpoint_10_31_p9) (by decide)⟩
private def endpoint_10_32_flag : Flag := ⟨10, 32, 4350⟩
private def endpoint_10_32_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_32_base : receiptBase endpoint_10_32_flag endpoint_10_32_sources = some 188425589045625026 := by decide +kernel
private theorem endpoint_10_32_w0 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 0 2 188425589045625026 = some 188425589045625026 := by decide +kernel
private theorem endpoint_10_32_w2 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 2 2 188425589045625026 = some 188425589045625026 := by decide +kernel
private theorem endpoint_10_32_p4 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 0 4 188425589045625026 = some 188425589045625026 :=
  join_receipt_window endpoint_10_32_flag endpoint_10_32_sources 0 2 2 188425589045625026 188425589045625026 188425589045625026 endpoint_10_32_w0 endpoint_10_32_w2
private theorem endpoint_10_32_w4 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 4 2 188425589045625026 = some 188425589045625026 := by decide +kernel
private theorem endpoint_10_32_p6 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 0 6 188425589045625026 = some 188425589045625026 :=
  join_receipt_window endpoint_10_32_flag endpoint_10_32_sources 0 4 2 188425589045625026 188425589045625026 188425589045625026 endpoint_10_32_p4 endpoint_10_32_w4
private theorem endpoint_10_32_w6 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 6 2 188425589045625026 = some 188425589045625026 := by decide +kernel
private theorem endpoint_10_32_p8 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 0 8 188425589045625026 = some 188425589045625026 :=
  join_receipt_window endpoint_10_32_flag endpoint_10_32_sources 0 6 2 188425589045625026 188425589045625026 188425589045625026 endpoint_10_32_p6 endpoint_10_32_w6
private theorem endpoint_10_32_w8 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 8 1 188425589045625026 = some 188425589045625026 := by decide +kernel
private theorem endpoint_10_32_p9 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 0 9 188425589045625026 = some 188425589045625026 :=
  join_receipt_window endpoint_10_32_flag endpoint_10_32_sources 0 8 1 188425589045625026 188425589045625026 188425589045625026 endpoint_10_32_p8 endpoint_10_32_w8
def endpoint_10_32 : CertifiedEndpoint :=
  ⟨⟨10, 32, 4350⟩, 188425589045625026, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_32_flag endpoint_10_32_sources 9 188425589045625026 188425589045625026 rfl endpoint_10_32_base endpoint_10_32_p9) (by decide)⟩
private def endpoint_10_33_flag : Flag := ⟨10, 33, 4323⟩
private def endpoint_10_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_33_base : receiptBase endpoint_10_33_flag endpoint_10_33_sources = some 192034798287824088 := by decide +kernel
private theorem endpoint_10_33_w0 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 2 192034798287824088 = some 192034798287824088 := by decide +kernel
private theorem endpoint_10_33_w2 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 2 2 192034798287824088 = some 192034798287824088 := by decide +kernel
private theorem endpoint_10_33_p4 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 4 192034798287824088 = some 192034798287824088 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 2 2 192034798287824088 192034798287824088 192034798287824088 endpoint_10_33_w0 endpoint_10_33_w2
private theorem endpoint_10_33_w4 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 4 2 192034798287824088 = some 192034798287824088 := by decide +kernel
private theorem endpoint_10_33_p6 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 6 192034798287824088 = some 192034798287824088 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 4 2 192034798287824088 192034798287824088 192034798287824088 endpoint_10_33_p4 endpoint_10_33_w4
private theorem endpoint_10_33_w6 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 6 2 192034798287824088 = some 192034798287824088 := by decide +kernel
private theorem endpoint_10_33_p8 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 8 192034798287824088 = some 192034798287824088 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 6 2 192034798287824088 192034798287824088 192034798287824088 endpoint_10_33_p6 endpoint_10_33_w6
private theorem endpoint_10_33_w8 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 8 1 192034798287824088 = some 192034798287824088 := by decide +kernel
private theorem endpoint_10_33_p9 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 9 192034798287824088 = some 192034798287824088 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 8 1 192034798287824088 192034798287824088 192034798287824088 endpoint_10_33_p8 endpoint_10_33_w8
def endpoint_10_33 : CertifiedEndpoint :=
  ⟨⟨10, 33, 4323⟩, 192034798287824088, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_33_flag endpoint_10_33_sources 9 192034798287824088 192034798287824088 rfl endpoint_10_33_base endpoint_10_33_p9) (by decide)⟩
private def endpoint_10_34_flag : Flag := ⟨10, 34, 4296⟩
private def endpoint_10_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_34_base : receiptBase endpoint_10_34_flag endpoint_10_34_sources = some 195584398270314239 := by decide +kernel
private theorem endpoint_10_34_w0 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 2 195584398270314239 = some 195584398270314239 := by decide +kernel
private theorem endpoint_10_34_w2 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 2 2 195584398270314239 = some 195584398270314239 := by decide +kernel
private theorem endpoint_10_34_p4 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 4 195584398270314239 = some 195584398270314239 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 2 2 195584398270314239 195584398270314239 195584398270314239 endpoint_10_34_w0 endpoint_10_34_w2
private theorem endpoint_10_34_w4 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 4 2 195584398270314239 = some 195584398270314239 := by decide +kernel
private theorem endpoint_10_34_p6 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 6 195584398270314239 = some 195584398270314239 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 4 2 195584398270314239 195584398270314239 195584398270314239 endpoint_10_34_p4 endpoint_10_34_w4
private theorem endpoint_10_34_w6 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 6 2 195584398270314239 = some 195584398270314239 := by decide +kernel
private theorem endpoint_10_34_p8 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 8 195584398270314239 = some 195584398270314239 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 6 2 195584398270314239 195584398270314239 195584398270314239 endpoint_10_34_p6 endpoint_10_34_w6
private theorem endpoint_10_34_w8 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 8 1 195584398270314239 = some 195584398270314239 := by decide +kernel
private theorem endpoint_10_34_p9 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 9 195584398270314239 = some 195584398270314239 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 8 1 195584398270314239 195584398270314239 195584398270314239 endpoint_10_34_p8 endpoint_10_34_w8
def endpoint_10_34 : CertifiedEndpoint :=
  ⟨⟨10, 34, 4296⟩, 195584398270314239, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_34_flag endpoint_10_34_sources 9 195584398270314239 195584398270314239 rfl endpoint_10_34_base endpoint_10_34_p9) (by decide)⟩
private def endpoint_10_35_flag : Flag := ⟨10, 35, 4268⟩
private def endpoint_10_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_35_base : receiptBase endpoint_10_35_flag endpoint_10_35_sources = some 199028372929530278 := by decide +kernel
private theorem endpoint_10_35_w0 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 2 199028372929530278 = some 199028372929530278 := by decide +kernel
private theorem endpoint_10_35_w2 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 2 2 199028372929530278 = some 199028372929530278 := by decide +kernel
private theorem endpoint_10_35_p4 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 4 199028372929530278 = some 199028372929530278 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 2 2 199028372929530278 199028372929530278 199028372929530278 endpoint_10_35_w0 endpoint_10_35_w2
private theorem endpoint_10_35_w4 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 4 2 199028372929530278 = some 199028372929530278 := by decide +kernel
private theorem endpoint_10_35_p6 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 6 199028372929530278 = some 199028372929530278 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 4 2 199028372929530278 199028372929530278 199028372929530278 endpoint_10_35_p4 endpoint_10_35_w4
private theorem endpoint_10_35_w6 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 6 2 199028372929530278 = some 199028372929530278 := by decide +kernel
private theorem endpoint_10_35_p8 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 8 199028372929530278 = some 199028372929530278 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 6 2 199028372929530278 199028372929530278 199028372929530278 endpoint_10_35_p6 endpoint_10_35_w6
private theorem endpoint_10_35_w8 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 8 1 199028372929530278 = some 199028372929530278 := by decide +kernel
private theorem endpoint_10_35_p9 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 9 199028372929530278 = some 199028372929530278 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 8 1 199028372929530278 199028372929530278 199028372929530278 endpoint_10_35_p8 endpoint_10_35_w8
def endpoint_10_35 : CertifiedEndpoint :=
  ⟨⟨10, 35, 4268⟩, 199028372929530278, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_35_flag endpoint_10_35_sources 9 199028372929530278 199028372929530278 rfl endpoint_10_35_base endpoint_10_35_p9) (by decide)⟩
private def endpoint_10_36_flag : Flag := ⟨10, 36, 4240⟩
private def endpoint_10_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_36_base : receiptBase endpoint_10_36_flag endpoint_10_36_sources = some 202410570883215446 := by decide +kernel
private theorem endpoint_10_36_w0 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 2 202410570883215446 = some 202410570883215446 := by decide +kernel
private theorem endpoint_10_36_w2 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 2 2 202410570883215446 = some 202410570883215446 := by decide +kernel
private theorem endpoint_10_36_p4 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 4 202410570883215446 = some 202410570883215446 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 2 2 202410570883215446 202410570883215446 202410570883215446 endpoint_10_36_w0 endpoint_10_36_w2
private theorem endpoint_10_36_w4 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 4 2 202410570883215446 = some 202410570883215446 := by decide +kernel
private theorem endpoint_10_36_p6 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 6 202410570883215446 = some 202410570883215446 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 4 2 202410570883215446 202410570883215446 202410570883215446 endpoint_10_36_p4 endpoint_10_36_w4
private theorem endpoint_10_36_w6 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 6 2 202410570883215446 = some 202410570883215446 := by decide +kernel
private theorem endpoint_10_36_p8 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 8 202410570883215446 = some 202410570883215446 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 6 2 202410570883215446 202410570883215446 202410570883215446 endpoint_10_36_p6 endpoint_10_36_w6
private theorem endpoint_10_36_w8 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 8 1 202410570883215446 = some 202410570883215446 := by decide +kernel
private theorem endpoint_10_36_p9 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 9 202410570883215446 = some 202410570883215446 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 8 1 202410570883215446 202410570883215446 202410570883215446 endpoint_10_36_p8 endpoint_10_36_w8
def endpoint_10_36 : CertifiedEndpoint :=
  ⟨⟨10, 36, 4240⟩, 202410570883215446, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_36_flag endpoint_10_36_sources 9 202410570883215446 202410570883215446 rfl endpoint_10_36_base endpoint_10_36_p9) (by decide)⟩
private def endpoint_10_37_flag : Flag := ⟨10, 37, 4211⟩
private def endpoint_10_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_37_base : receiptBase endpoint_10_37_flag endpoint_10_37_sources = some 205682808621982583 := by decide +kernel
private theorem endpoint_10_37_w0 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 2 205682808621982583 = some 205682808621982583 := by decide +kernel
private theorem endpoint_10_37_w2 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 2 2 205682808621982583 = some 205682808621982583 := by decide +kernel
private theorem endpoint_10_37_p4 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 4 205682808621982583 = some 205682808621982583 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 2 2 205682808621982583 205682808621982583 205682808621982583 endpoint_10_37_w0 endpoint_10_37_w2
private theorem endpoint_10_37_w4 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 4 2 205682808621982583 = some 205682808621982583 := by decide +kernel
private theorem endpoint_10_37_p6 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 6 205682808621982583 = some 205682808621982583 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 4 2 205682808621982583 205682808621982583 205682808621982583 endpoint_10_37_p4 endpoint_10_37_w4
private theorem endpoint_10_37_w6 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 6 2 205682808621982583 = some 205682808621982583 := by decide +kernel
private theorem endpoint_10_37_p8 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 8 205682808621982583 = some 205682808621982583 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 6 2 205682808621982583 205682808621982583 205682808621982583 endpoint_10_37_p6 endpoint_10_37_w6
private theorem endpoint_10_37_w8 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 8 1 205682808621982583 = some 205682808621982583 := by decide +kernel
private theorem endpoint_10_37_p9 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 9 205682808621982583 = some 205682808621982583 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 8 1 205682808621982583 205682808621982583 205682808621982583 endpoint_10_37_p8 endpoint_10_37_w8
def endpoint_10_37 : CertifiedEndpoint :=
  ⟨⟨10, 37, 4211⟩, 205682808621982583, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_37_flag endpoint_10_37_sources 9 205682808621982583 205682808621982583 rfl endpoint_10_37_base endpoint_10_37_p9) (by decide)⟩
private def endpoint_10_38_flag : Flag := ⟨10, 38, 4182⟩
private def endpoint_10_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_38_base : receiptBase endpoint_10_38_flag endpoint_10_38_sources = some 208891102209396890 := by decide +kernel
private theorem endpoint_10_38_w0 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 2 208891102209396890 = some 208891102209396890 := by decide +kernel
private theorem endpoint_10_38_w2 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 2 2 208891102209396890 = some 208891102209396890 := by decide +kernel
private theorem endpoint_10_38_p4 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 4 208891102209396890 = some 208891102209396890 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 2 2 208891102209396890 208891102209396890 208891102209396890 endpoint_10_38_w0 endpoint_10_38_w2
private theorem endpoint_10_38_w4 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 4 2 208891102209396890 = some 208891102209396890 := by decide +kernel
private theorem endpoint_10_38_p6 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 6 208891102209396890 = some 208891102209396890 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 4 2 208891102209396890 208891102209396890 208891102209396890 endpoint_10_38_p4 endpoint_10_38_w4
private theorem endpoint_10_38_w6 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 6 2 208891102209396890 = some 208891102209396890 := by decide +kernel
private theorem endpoint_10_38_p8 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 8 208891102209396890 = some 208891102209396890 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 6 2 208891102209396890 208891102209396890 208891102209396890 endpoint_10_38_p6 endpoint_10_38_w6
private theorem endpoint_10_38_w8 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 8 1 208891102209396890 = some 208891102209396890 := by decide +kernel
private theorem endpoint_10_38_p9 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 9 208891102209396890 = some 208891102209396890 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 8 1 208891102209396890 208891102209396890 208891102209396890 endpoint_10_38_p8 endpoint_10_38_w8
def endpoint_10_38 : CertifiedEndpoint :=
  ⟨⟨10, 38, 4182⟩, 208891102209396890, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_38_flag endpoint_10_38_sources 9 208891102209396890 208891102209396890 rfl endpoint_10_38_base endpoint_10_38_p9) (by decide)⟩
private def endpoint_10_39_flag : Flag := ⟨10, 39, 4152⟩
private def endpoint_10_39_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_39_base : receiptBase endpoint_10_39_flag endpoint_10_39_sources = some 211985100690249246 := by decide +kernel
private theorem endpoint_10_39_w0 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 2 211985100690249246 = some 211985100690249246 := by decide +kernel
private theorem endpoint_10_39_w2 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 2 2 211985100690249246 = some 211985100690249246 := by decide +kernel
private theorem endpoint_10_39_p4 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 4 211985100690249246 = some 211985100690249246 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 2 2 211985100690249246 211985100690249246 211985100690249246 endpoint_10_39_w0 endpoint_10_39_w2
private theorem endpoint_10_39_w4 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 4 2 211985100690249246 = some 211985100690249246 := by decide +kernel
private theorem endpoint_10_39_p6 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 6 211985100690249246 = some 211985100690249246 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 4 2 211985100690249246 211985100690249246 211985100690249246 endpoint_10_39_p4 endpoint_10_39_w4
private theorem endpoint_10_39_w6 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 6 2 211985100690249246 = some 211985100690249246 := by decide +kernel
private theorem endpoint_10_39_p8 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 8 211985100690249246 = some 211985100690249246 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 6 2 211985100690249246 211985100690249246 211985100690249246 endpoint_10_39_p6 endpoint_10_39_w6
private theorem endpoint_10_39_w8 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 8 1 211985100690249246 = some 211985100690249246 := by decide +kernel
private theorem endpoint_10_39_p9 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 9 211985100690249246 = some 211985100690249246 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 8 1 211985100690249246 211985100690249246 211985100690249246 endpoint_10_39_p8 endpoint_10_39_w8
def endpoint_10_39 : CertifiedEndpoint :=
  ⟨⟨10, 39, 4152⟩, 211985100690249246, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_39_flag endpoint_10_39_sources 9 211985100690249246 211985100690249246 rfl endpoint_10_39_base endpoint_10_39_p9) (by decide)⟩
private def endpoint_10_40_flag : Flag := ⟨10, 40, 4122⟩
private def endpoint_10_40_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_40_base : receiptBase endpoint_10_40_flag endpoint_10_40_sources = some 215012987573926811 := by decide +kernel
private theorem endpoint_10_40_w0 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 2 215012987573926811 = some 215012987573926811 := by decide +kernel
private theorem endpoint_10_40_w2 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 2 2 215012987573926811 = some 215012987573926811 := by decide +kernel
private theorem endpoint_10_40_p4 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 4 215012987573926811 = some 215012987573926811 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 2 2 215012987573926811 215012987573926811 215012987573926811 endpoint_10_40_w0 endpoint_10_40_w2
private theorem endpoint_10_40_w4 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 4 2 215012987573926811 = some 215012987573926811 := by decide +kernel
private theorem endpoint_10_40_p6 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 6 215012987573926811 = some 215012987573926811 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 4 2 215012987573926811 215012987573926811 215012987573926811 endpoint_10_40_p4 endpoint_10_40_w4
private theorem endpoint_10_40_w6 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 6 2 215012987573926811 = some 215012987573926811 := by decide +kernel
private theorem endpoint_10_40_p8 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 8 215012987573926811 = some 215012987573926811 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 6 2 215012987573926811 215012987573926811 215012987573926811 endpoint_10_40_p6 endpoint_10_40_w6
private theorem endpoint_10_40_w8 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 8 1 215012987573926811 = some 215012987573926811 := by decide +kernel
private theorem endpoint_10_40_p9 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 9 215012987573926811 = some 215012987573926811 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 8 1 215012987573926811 215012987573926811 215012987573926811 endpoint_10_40_p8 endpoint_10_40_w8
def endpoint_10_40 : CertifiedEndpoint :=
  ⟨⟨10, 40, 4122⟩, 215012987573926811, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_40_flag endpoint_10_40_sources 9 215012987573926811 215012987573926811 rfl endpoint_10_40_base endpoint_10_40_p9) (by decide)⟩
private def endpoint_10_41_flag : Flag := ⟨10, 41, 4092⟩
private def endpoint_10_41_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_41_base : receiptBase endpoint_10_41_flag endpoint_10_41_sources = some 217974762860429586 := by decide +kernel
private theorem endpoint_10_41_w0 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 2 217974762860429586 = some 217974762860429586 := by decide +kernel
private theorem endpoint_10_41_w2 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 2 2 217974762860429586 = some 217974762860429586 := by decide +kernel
private theorem endpoint_10_41_p4 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 4 217974762860429586 = some 217974762860429586 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 2 2 217974762860429586 217974762860429586 217974762860429586 endpoint_10_41_w0 endpoint_10_41_w2
private theorem endpoint_10_41_w4 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 4 2 217974762860429586 = some 217974762860429586 := by decide +kernel
private theorem endpoint_10_41_p6 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 6 217974762860429586 = some 217974762860429586 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 4 2 217974762860429586 217974762860429586 217974762860429586 endpoint_10_41_p4 endpoint_10_41_w4
private theorem endpoint_10_41_w6 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 6 2 217974762860429586 = some 217974762860429586 := by decide +kernel
private theorem endpoint_10_41_p8 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 8 217974762860429586 = some 217974762860429586 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 6 2 217974762860429586 217974762860429586 217974762860429586 endpoint_10_41_p6 endpoint_10_41_w6
private theorem endpoint_10_41_w8 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 8 1 217974762860429586 = some 217974762860429586 := by decide +kernel
private theorem endpoint_10_41_p9 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 9 217974762860429586 = some 217974762860429586 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 8 1 217974762860429586 217974762860429586 217974762860429586 endpoint_10_41_p8 endpoint_10_41_w8
def endpoint_10_41 : CertifiedEndpoint :=
  ⟨⟨10, 41, 4092⟩, 217974762860429586, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_41_flag endpoint_10_41_sources 9 217974762860429586 217974762860429586 rfl endpoint_10_41_base endpoint_10_41_p9) (by decide)⟩
private def endpoint_10_42_flag : Flag := ⟨10, 42, 4061⟩
private def endpoint_10_42_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_42_base : receiptBase endpoint_10_42_flag endpoint_10_42_sources = some 220816824425815511 := by decide +kernel
private theorem endpoint_10_42_w0 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 2 220816824425815511 = some 220816824425815511 := by decide +kernel
private theorem endpoint_10_42_w2 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 2 2 220816824425815511 = some 220816824425815511 := by decide +kernel
private theorem endpoint_10_42_p4 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 4 220816824425815511 = some 220816824425815511 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 2 2 220816824425815511 220816824425815511 220816824425815511 endpoint_10_42_w0 endpoint_10_42_w2
private theorem endpoint_10_42_w4 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 4 2 220816824425815511 = some 220816824425815511 := by decide +kernel
private theorem endpoint_10_42_p6 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 6 220816824425815511 = some 220816824425815511 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 4 2 220816824425815511 220816824425815511 220816824425815511 endpoint_10_42_p4 endpoint_10_42_w4
private theorem endpoint_10_42_w6 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 6 2 220816824425815511 = some 220816824425815511 := by decide +kernel
private theorem endpoint_10_42_p8 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 8 220816824425815511 = some 220816824425815511 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 6 2 220816824425815511 220816824425815511 220816824425815511 endpoint_10_42_p6 endpoint_10_42_w6
private theorem endpoint_10_42_w8 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 8 1 220816824425815511 = some 220816824425815511 := by decide +kernel
private theorem endpoint_10_42_p9 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 9 220816824425815511 = some 220816824425815511 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 8 1 220816824425815511 220816824425815511 220816824425815511 endpoint_10_42_p8 endpoint_10_42_w8
def endpoint_10_42 : CertifiedEndpoint :=
  ⟨⟨10, 42, 4061⟩, 220816824425815511, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_42_flag endpoint_10_42_sources 9 220816824425815511 220816824425815511 rfl endpoint_10_42_base endpoint_10_42_p9) (by decide)⟩
private def endpoint_10_43_flag : Flag := ⟨10, 43, 4029⟩
private def endpoint_10_43_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_43_base : receiptBase endpoint_10_43_flag endpoint_10_43_sources = some 224115481873015151 := by decide +kernel
private theorem endpoint_10_43_w0 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 2 224115481873015151 = some 224115481873015151 := by decide +kernel
private theorem endpoint_10_43_w2 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 2 2 224115481873015151 = some 224115481873015151 := by decide +kernel
private theorem endpoint_10_43_p4 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 4 224115481873015151 = some 224115481873015151 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 2 2 224115481873015151 224115481873015151 224115481873015151 endpoint_10_43_w0 endpoint_10_43_w2
private theorem endpoint_10_43_w4 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 4 2 224115481873015151 = some 224115481873015151 := by decide +kernel
private theorem endpoint_10_43_p6 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 6 224115481873015151 = some 224115481873015151 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 4 2 224115481873015151 224115481873015151 224115481873015151 endpoint_10_43_p4 endpoint_10_43_w4
private theorem endpoint_10_43_w6 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 6 2 224115481873015151 = some 224115481873015151 := by decide +kernel
private theorem endpoint_10_43_p8 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 8 224115481873015151 = some 224115481873015151 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 6 2 224115481873015151 224115481873015151 224115481873015151 endpoint_10_43_p6 endpoint_10_43_w6
private theorem endpoint_10_43_w8 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 8 1 224115481873015151 = some 224115481873015151 := by decide +kernel
private theorem endpoint_10_43_p9 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 9 224115481873015151 = some 224115481873015151 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 8 1 224115481873015151 224115481873015151 224115481873015151 endpoint_10_43_p8 endpoint_10_43_w8
def endpoint_10_43 : CertifiedEndpoint :=
  ⟨⟨10, 43, 4029⟩, 224115481873015151, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_43_flag endpoint_10_43_sources 9 224115481873015151 224115481873015151 rfl endpoint_10_43_base endpoint_10_43_p9) (by decide)⟩
private def endpoint_10_44_flag : Flag := ⟨10, 44, 3997⟩
private def endpoint_10_44_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_44_base : receiptBase endpoint_10_44_flag endpoint_10_44_sources = some 226731843670302499 := by decide +kernel
private theorem endpoint_10_44_w0 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 2 226731843670302499 = some 226731843670302499 := by decide +kernel
private theorem endpoint_10_44_w2 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 2 2 226731843670302499 = some 226731843670302499 := by decide +kernel
private theorem endpoint_10_44_p4 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 4 226731843670302499 = some 226731843670302499 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 2 2 226731843670302499 226731843670302499 226731843670302499 endpoint_10_44_w0 endpoint_10_44_w2
private theorem endpoint_10_44_w4 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 4 2 226731843670302499 = some 226731843670302499 := by decide +kernel
private theorem endpoint_10_44_p6 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 6 226731843670302499 = some 226731843670302499 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 4 2 226731843670302499 226731843670302499 226731843670302499 endpoint_10_44_p4 endpoint_10_44_w4
private theorem endpoint_10_44_w6 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 6 2 226731843670302499 = some 226731843670302499 := by decide +kernel
private theorem endpoint_10_44_p8 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 8 226731843670302499 = some 226731843670302499 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 6 2 226731843670302499 226731843670302499 226731843670302499 endpoint_10_44_p6 endpoint_10_44_w6
private theorem endpoint_10_44_w8 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 8 1 226731843670302499 = some 226731843670302499 := by decide +kernel
private theorem endpoint_10_44_p9 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 9 226731843670302499 = some 226731843670302499 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 8 1 226731843670302499 226731843670302499 226731843670302499 endpoint_10_44_p8 endpoint_10_44_w8
def endpoint_10_44 : CertifiedEndpoint :=
  ⟨⟨10, 44, 3997⟩, 226731843670302499, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_44_flag endpoint_10_44_sources 9 226731843670302499 226731843670302499 rfl endpoint_10_44_base endpoint_10_44_p9) (by decide)⟩
private def endpoint_10_45_flag : Flag := ⟨10, 45, 3964⟩
private def endpoint_10_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_45_base : receiptBase endpoint_10_45_flag endpoint_10_45_sources = some 229220988992342498 := by decide +kernel
private theorem endpoint_10_45_w0 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 2 229220988992342498 = some 229220988992342498 := by decide +kernel
private theorem endpoint_10_45_w2 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 2 2 229220988992342498 = some 229220988992342498 := by decide +kernel
private theorem endpoint_10_45_p4 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 4 229220988992342498 = some 229220988992342498 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 2 2 229220988992342498 229220988992342498 229220988992342498 endpoint_10_45_w0 endpoint_10_45_w2
private theorem endpoint_10_45_w4 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 4 2 229220988992342498 = some 229220988992342498 := by decide +kernel
private theorem endpoint_10_45_p6 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 6 229220988992342498 = some 229220988992342498 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 4 2 229220988992342498 229220988992342498 229220988992342498 endpoint_10_45_p4 endpoint_10_45_w4
private theorem endpoint_10_45_w6 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 6 2 229220988992342498 = some 229220988992342498 := by decide +kernel
private theorem endpoint_10_45_p8 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 8 229220988992342498 = some 229220988992342498 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 6 2 229220988992342498 229220988992342498 229220988992342498 endpoint_10_45_p6 endpoint_10_45_w6
private theorem endpoint_10_45_w8 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 8 1 229220988992342498 = some 229220988992342498 := by decide +kernel
private theorem endpoint_10_45_p9 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 9 229220988992342498 = some 229220988992342498 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 8 1 229220988992342498 229220988992342498 229220988992342498 endpoint_10_45_p8 endpoint_10_45_w8
def endpoint_10_45 : CertifiedEndpoint :=
  ⟨⟨10, 45, 3964⟩, 229220988992342498, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_45_flag endpoint_10_45_sources 9 229220988992342498 229220988992342498 rfl endpoint_10_45_base endpoint_10_45_p9) (by decide)⟩
private def endpoint_10_46_flag : Flag := ⟨10, 46, 3930⟩
private def endpoint_10_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_46_base : receiptBase endpoint_10_46_flag endpoint_10_46_sources = some 231579680166938753 := by decide +kernel
private theorem endpoint_10_46_w0 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 2 231579680166938753 = some 231579680166938753 := by decide +kernel
private theorem endpoint_10_46_w2 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 2 2 231579680166938753 = some 231579680166938753 := by decide +kernel
private theorem endpoint_10_46_p4 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 4 231579680166938753 = some 231579680166938753 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 2 2 231579680166938753 231579680166938753 231579680166938753 endpoint_10_46_w0 endpoint_10_46_w2
private theorem endpoint_10_46_w4 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 4 2 231579680166938753 = some 231579680166938753 := by decide +kernel
private theorem endpoint_10_46_p6 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 6 231579680166938753 = some 231579680166938753 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 4 2 231579680166938753 231579680166938753 231579680166938753 endpoint_10_46_p4 endpoint_10_46_w4
private theorem endpoint_10_46_w6 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 6 2 231579680166938753 = some 231579680166938753 := by decide +kernel
private theorem endpoint_10_46_p8 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 8 231579680166938753 = some 231579680166938753 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 6 2 231579680166938753 231579680166938753 231579680166938753 endpoint_10_46_p6 endpoint_10_46_w6
private theorem endpoint_10_46_w8 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 8 1 231579680166938753 = some 231579680166938753 := by decide +kernel
private theorem endpoint_10_46_p9 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 9 231579680166938753 = some 231579680166938753 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 8 1 231579680166938753 231579680166938753 231579680166938753 endpoint_10_46_p8 endpoint_10_46_w8
def endpoint_10_46 : CertifiedEndpoint :=
  ⟨⟨10, 46, 3930⟩, 231579680166938753, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_46_flag endpoint_10_46_sources 9 231579680166938753 231579680166938753 rfl endpoint_10_46_base endpoint_10_46_p9) (by decide)⟩
private def endpoint_10_47_flag : Flag := ⟨10, 47, 3896⟩
private def endpoint_10_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_47_base : receiptBase endpoint_10_47_flag endpoint_10_47_sources = some 233863904881017939 := by decide +kernel
private theorem endpoint_10_47_w0 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 2 233863904881017939 = some 233863904881017939 := by decide +kernel
private theorem endpoint_10_47_w2 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 2 2 233863904881017939 = some 233863904881017939 := by decide +kernel
private theorem endpoint_10_47_p4 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 4 233863904881017939 = some 233863904881017939 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 2 2 233863904881017939 233863904881017939 233863904881017939 endpoint_10_47_w0 endpoint_10_47_w2
private theorem endpoint_10_47_w4 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 4 2 233863904881017939 = some 233863904881017939 := by decide +kernel
private theorem endpoint_10_47_p6 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 6 233863904881017939 = some 233863904881017939 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 4 2 233863904881017939 233863904881017939 233863904881017939 endpoint_10_47_p4 endpoint_10_47_w4
private theorem endpoint_10_47_w6 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 6 2 233863904881017939 = some 233863904881017939 := by decide +kernel
private theorem endpoint_10_47_p8 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 8 233863904881017939 = some 233863904881017939 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 6 2 233863904881017939 233863904881017939 233863904881017939 endpoint_10_47_p6 endpoint_10_47_w6
private theorem endpoint_10_47_w8 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 8 1 233863904881017939 = some 233863904881017939 := by decide +kernel
private theorem endpoint_10_47_p9 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 9 233863904881017939 = some 233863904881017939 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 8 1 233863904881017939 233863904881017939 233863904881017939 endpoint_10_47_p8 endpoint_10_47_w8
def endpoint_10_47 : CertifiedEndpoint :=
  ⟨⟨10, 47, 3896⟩, 233863904881017939, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_47_flag endpoint_10_47_sources 9 233863904881017939 233863904881017939 rfl endpoint_10_47_base endpoint_10_47_p9) (by decide)⟩
private def endpoint_10_48_flag : Flag := ⟨10, 48, 3861⟩
private def endpoint_10_48_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_48_base : receiptBase endpoint_10_48_flag endpoint_10_48_sources = some 236013358551391522 := by decide +kernel
private theorem endpoint_10_48_w0 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 2 236013358551391522 = some 236013358551391522 := by decide +kernel
private theorem endpoint_10_48_w2 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 2 2 236013358551391522 = some 236013358551391522 := by decide +kernel
private theorem endpoint_10_48_p4 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 4 236013358551391522 = some 236013358551391522 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 2 2 236013358551391522 236013358551391522 236013358551391522 endpoint_10_48_w0 endpoint_10_48_w2
private theorem endpoint_10_48_w4 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 4 2 236013358551391522 = some 236013358551391522 := by decide +kernel
private theorem endpoint_10_48_p6 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 6 236013358551391522 = some 236013358551391522 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 4 2 236013358551391522 236013358551391522 236013358551391522 endpoint_10_48_p4 endpoint_10_48_w4
private theorem endpoint_10_48_w6 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 6 2 236013358551391522 = some 236013358551391522 := by decide +kernel
private theorem endpoint_10_48_p8 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 8 236013358551391522 = some 236013358551391522 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 6 2 236013358551391522 236013358551391522 236013358551391522 endpoint_10_48_p6 endpoint_10_48_w6
private theorem endpoint_10_48_w8 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 8 1 236013358551391522 = some 236013358551391522 := by decide +kernel
private theorem endpoint_10_48_p9 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 9 236013358551391522 = some 236013358551391522 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 8 1 236013358551391522 236013358551391522 236013358551391522 endpoint_10_48_p8 endpoint_10_48_w8
def endpoint_10_48 : CertifiedEndpoint :=
  ⟨⟨10, 48, 3861⟩, 236013358551391522, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_48_flag endpoint_10_48_sources 9 236013358551391522 236013358551391522 rfl endpoint_10_48_base endpoint_10_48_p9) (by decide)⟩
private def endpoint_10_49_flag : Flag := ⟨10, 49, 3825⟩
private def endpoint_10_49_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_49_base : receiptBase endpoint_10_49_flag endpoint_10_49_sources = some 238024803505863108 := by decide +kernel
private theorem endpoint_10_49_w0 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 2 238024803505863108 = some 238024803505863108 := by decide +kernel
private theorem endpoint_10_49_w2 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 2 2 238024803505863108 = some 238024803505863108 := by decide +kernel
private theorem endpoint_10_49_p4 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 4 238024803505863108 = some 238024803505863108 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 2 2 238024803505863108 238024803505863108 238024803505863108 endpoint_10_49_w0 endpoint_10_49_w2
private theorem endpoint_10_49_w4 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 4 2 238024803505863108 = some 238024803505863108 := by decide +kernel
private theorem endpoint_10_49_p6 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 6 238024803505863108 = some 238024803505863108 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 4 2 238024803505863108 238024803505863108 238024803505863108 endpoint_10_49_p4 endpoint_10_49_w4
private theorem endpoint_10_49_w6 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 6 2 238024803505863108 = some 238024803505863108 := by decide +kernel
private theorem endpoint_10_49_p8 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 8 238024803505863108 = some 238024803505863108 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 6 2 238024803505863108 238024803505863108 238024803505863108 endpoint_10_49_p6 endpoint_10_49_w6
private theorem endpoint_10_49_w8 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 8 1 238024803505863108 = some 238024803505863108 := by decide +kernel
private theorem endpoint_10_49_p9 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 9 238024803505863108 = some 238024803505863108 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 8 1 238024803505863108 238024803505863108 238024803505863108 endpoint_10_49_p8 endpoint_10_49_w8
def endpoint_10_49 : CertifiedEndpoint :=
  ⟨⟨10, 49, 3825⟩, 238024803505863108, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_49_flag endpoint_10_49_sources 9 238024803505863108 238024803505863108 rfl endpoint_10_49_base endpoint_10_49_p9) (by decide)⟩
private def endpoint_10_50_flag : Flag := ⟨10, 50, 3789⟩
private def endpoint_10_50_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_50_base : receiptBase endpoint_10_50_flag endpoint_10_50_sources = some 239957465103555765 := by decide +kernel
private theorem endpoint_10_50_w0 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 2 239957465103555765 = some 239957465103555765 := by decide +kernel
private theorem endpoint_10_50_w2 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 2 2 239957465103555765 = some 239957465103555765 := by decide +kernel
private theorem endpoint_10_50_p4 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 4 239957465103555765 = some 239957465103555765 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 2 2 239957465103555765 239957465103555765 239957465103555765 endpoint_10_50_w0 endpoint_10_50_w2
private theorem endpoint_10_50_w4 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 4 2 239957465103555765 = some 239957465103555765 := by decide +kernel
private theorem endpoint_10_50_p6 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 6 239957465103555765 = some 239957465103555765 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 4 2 239957465103555765 239957465103555765 239957465103555765 endpoint_10_50_p4 endpoint_10_50_w4
private theorem endpoint_10_50_w6 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 6 2 239957465103555765 = some 239957465103555765 := by decide +kernel
private theorem endpoint_10_50_p8 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 8 239957465103555765 = some 239957465103555765 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 6 2 239957465103555765 239957465103555765 239957465103555765 endpoint_10_50_p6 endpoint_10_50_w6
private theorem endpoint_10_50_w8 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 8 1 239957465103555765 = some 239957465103555765 := by decide +kernel
private theorem endpoint_10_50_p9 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 9 239957465103555765 = some 239957465103555765 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 8 1 239957465103555765 239957465103555765 239957465103555765 endpoint_10_50_p8 endpoint_10_50_w8
def endpoint_10_50 : CertifiedEndpoint :=
  ⟨⟨10, 50, 3789⟩, 239957465103555765, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_50_flag endpoint_10_50_sources 9 239957465103555765 239957465103555765 rfl endpoint_10_50_base endpoint_10_50_p9) (by decide)⟩
private def endpoint_10_51_flag : Flag := ⟨10, 51, 3751⟩
private def endpoint_10_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_51_base : receiptBase endpoint_10_51_flag endpoint_10_51_sources = some 241684258833699638 := by decide +kernel
private theorem endpoint_10_51_w0 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 2 241684258833699638 = some 241684258833699638 := by decide +kernel
private theorem endpoint_10_51_w2 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 2 2 241684258833699638 = some 241684258833699638 := by decide +kernel
private theorem endpoint_10_51_p4 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 4 241684258833699638 = some 241684258833699638 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 2 2 241684258833699638 241684258833699638 241684258833699638 endpoint_10_51_w0 endpoint_10_51_w2
private theorem endpoint_10_51_w4 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 4 2 241684258833699638 = some 241684258833699638 := by decide +kernel
private theorem endpoint_10_51_p6 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 6 241684258833699638 = some 241684258833699638 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 4 2 241684258833699638 241684258833699638 241684258833699638 endpoint_10_51_p4 endpoint_10_51_w4
private theorem endpoint_10_51_w6 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 6 2 241684258833699638 = some 241684258833699638 := by decide +kernel
private theorem endpoint_10_51_p8 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 8 241684258833699638 = some 241684258833699638 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 6 2 241684258833699638 241684258833699638 241684258833699638 endpoint_10_51_p6 endpoint_10_51_w6
private theorem endpoint_10_51_w8 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 8 1 241684258833699638 = some 241684258833699638 := by decide +kernel
private theorem endpoint_10_51_p9 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 9 241684258833699638 = some 241684258833699638 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 8 1 241684258833699638 241684258833699638 241684258833699638 endpoint_10_51_p8 endpoint_10_51_w8
def endpoint_10_51 : CertifiedEndpoint :=
  ⟨⟨10, 51, 3751⟩, 241684258833699638, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_51_flag endpoint_10_51_sources 9 241684258833699638 241684258833699638 rfl endpoint_10_51_base endpoint_10_51_p9) (by decide)⟩
private def endpoint_10_52_flag : Flag := ⟨10, 52, 3713⟩
private def endpoint_10_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_52_base : receiptBase endpoint_10_52_flag endpoint_10_52_sources = some 243327952310802724 := by decide +kernel
private theorem endpoint_10_52_w0 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 2 243327952310802724 = some 243327952310802724 := by decide +kernel
private theorem endpoint_10_52_w2 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 2 2 243327952310802724 = some 243327952310802724 := by decide +kernel
private theorem endpoint_10_52_p4 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 4 243327952310802724 = some 243327952310802724 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 2 2 243327952310802724 243327952310802724 243327952310802724 endpoint_10_52_w0 endpoint_10_52_w2
private theorem endpoint_10_52_w4 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 4 2 243327952310802724 = some 243327952310802724 := by decide +kernel
private theorem endpoint_10_52_p6 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 6 243327952310802724 = some 243327952310802724 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 4 2 243327952310802724 243327952310802724 243327952310802724 endpoint_10_52_p4 endpoint_10_52_w4
private theorem endpoint_10_52_w6 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 6 2 243327952310802724 = some 243327952310802724 := by decide +kernel
private theorem endpoint_10_52_p8 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 8 243327952310802724 = some 243327952310802724 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 6 2 243327952310802724 243327952310802724 243327952310802724 endpoint_10_52_p6 endpoint_10_52_w6
private theorem endpoint_10_52_w8 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 8 1 243327952310802724 = some 243327952310802724 := by decide +kernel
private theorem endpoint_10_52_p9 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 9 243327952310802724 = some 243327952310802724 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 8 1 243327952310802724 243327952310802724 243327952310802724 endpoint_10_52_p8 endpoint_10_52_w8
def endpoint_10_52 : CertifiedEndpoint :=
  ⟨⟨10, 52, 3713⟩, 243327952310802724, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_52_flag endpoint_10_52_sources 9 243327952310802724 243327952310802724 rfl endpoint_10_52_base endpoint_10_52_p9) (by decide)⟩
private def endpoint_10_53_flag : Flag := ⟨10, 53, 3673⟩
private def endpoint_10_53_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_10_53_base : receiptBase endpoint_10_53_flag endpoint_10_53_sources = some 245457634375565166 := by decide +kernel
private theorem endpoint_10_53_w0 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 2 245457634375565166 = some 245457634375565166 := by decide +kernel
private theorem endpoint_10_53_w2 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 2 2 245457634375565166 = some 245457634375565166 := by decide +kernel
private theorem endpoint_10_53_p4 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 4 245457634375565166 = some 245457634375565166 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 2 2 245457634375565166 245457634375565166 245457634375565166 endpoint_10_53_w0 endpoint_10_53_w2
private theorem endpoint_10_53_w4 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 4 2 245457634375565166 = some 245457634375565166 := by decide +kernel
private theorem endpoint_10_53_p6 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 6 245457634375565166 = some 245457634375565166 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 4 2 245457634375565166 245457634375565166 245457634375565166 endpoint_10_53_p4 endpoint_10_53_w4
private theorem endpoint_10_53_w6 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 6 2 245457634375565166 = some 245457634375565166 := by decide +kernel
private theorem endpoint_10_53_p8 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 8 245457634375565166 = some 245457634375565166 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 6 2 245457634375565166 245457634375565166 245457634375565166 endpoint_10_53_p6 endpoint_10_53_w6
private theorem endpoint_10_53_w8 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 8 1 245457634375565166 = some 245457634375565166 := by decide +kernel
private theorem endpoint_10_53_p9 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 9 245457634375565166 = some 245457634375565166 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 8 1 245457634375565166 245457634375565166 245457634375565166 endpoint_10_53_p8 endpoint_10_53_w8
def endpoint_10_53 : CertifiedEndpoint :=
  ⟨⟨10, 53, 3673⟩, 245457634375565166, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_10_53_flag endpoint_10_53_sources 9 245457634375565166 245457634375565166 rfl endpoint_10_53_base endpoint_10_53_p9) (by decide)⟩
private def endpoint_10_54_flag : Flag := ⟨10, 54, 3632⟩
private def endpoint_10_54_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_10_54_base : receiptBase endpoint_10_54_flag endpoint_10_54_sources = some 246740603015509222 := by decide +kernel
private theorem endpoint_10_54_w0 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 2 246740603015509222 = some 246740603015509222 := by decide +kernel
private theorem endpoint_10_54_w2 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 2 2 246740603015509222 = some 246740603015509222 := by decide +kernel
private theorem endpoint_10_54_p4 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 4 246740603015509222 = some 246740603015509222 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 2 2 246740603015509222 246740603015509222 246740603015509222 endpoint_10_54_w0 endpoint_10_54_w2
private theorem endpoint_10_54_w4 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 4 2 246740603015509222 = some 246740603015509222 := by decide +kernel
private theorem endpoint_10_54_p6 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 6 246740603015509222 = some 246740603015509222 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 4 2 246740603015509222 246740603015509222 246740603015509222 endpoint_10_54_p4 endpoint_10_54_w4
private theorem endpoint_10_54_w6 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 6 2 246740603015509222 = some 246740603015509222 := by decide +kernel
private theorem endpoint_10_54_p8 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 8 246740603015509222 = some 246740603015509222 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 6 2 246740603015509222 246740603015509222 246740603015509222 endpoint_10_54_p6 endpoint_10_54_w6
private theorem endpoint_10_54_w8 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 8 1 246740603015509222 = some 246740603015509222 := by decide +kernel
private theorem endpoint_10_54_p9 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 9 246740603015509222 = some 246740603015509222 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 8 1 246740603015509222 246740603015509222 246740603015509222 endpoint_10_54_p8 endpoint_10_54_w8
def endpoint_10_54 : CertifiedEndpoint :=
  ⟨⟨10, 54, 3632⟩, 246740603015509222, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_10_54_flag endpoint_10_54_sources 9 246740603015509222 246740603015509222 rfl endpoint_10_54_base endpoint_10_54_p9) (by decide)⟩
private def endpoint_10_55_flag : Flag := ⟨10, 55, 3590⟩
private def endpoint_10_55_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_10_55_base : receiptBase endpoint_10_55_flag endpoint_10_55_sources = some 247865556360109529 := by decide +kernel
private theorem endpoint_10_55_w0 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 2 247865556360109529 = some 247865556360109529 := by decide +kernel
private theorem endpoint_10_55_w2 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 2 2 247865556360109529 = some 247865556360109529 := by decide +kernel
private theorem endpoint_10_55_p4 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 4 247865556360109529 = some 247865556360109529 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 2 2 247865556360109529 247865556360109529 247865556360109529 endpoint_10_55_w0 endpoint_10_55_w2
private theorem endpoint_10_55_w4 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 4 2 247865556360109529 = some 247865556360109529 := by decide +kernel
private theorem endpoint_10_55_p6 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 6 247865556360109529 = some 247865556360109529 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 4 2 247865556360109529 247865556360109529 247865556360109529 endpoint_10_55_p4 endpoint_10_55_w4
private theorem endpoint_10_55_w6 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 6 2 247865556360109529 = some 247865556360109529 := by decide +kernel
private theorem endpoint_10_55_p8 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 8 247865556360109529 = some 247865556360109529 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 6 2 247865556360109529 247865556360109529 247865556360109529 endpoint_10_55_p6 endpoint_10_55_w6
private theorem endpoint_10_55_w8 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 8 1 247865556360109529 = some 247865556360109529 := by decide +kernel
private theorem endpoint_10_55_p9 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 9 247865556360109529 = some 247865556360109529 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 8 1 247865556360109529 247865556360109529 247865556360109529 endpoint_10_55_p8 endpoint_10_55_w8
def endpoint_10_55 : CertifiedEndpoint :=
  ⟨⟨10, 55, 3590⟩, 247865556360109529, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_10_55_flag endpoint_10_55_sources 9 247865556360109529 247865556360109529 rfl endpoint_10_55_base endpoint_10_55_p9) (by decide)⟩
private def endpoint_10_56_flag : Flag := ⟨10, 56, 3547⟩
private def endpoint_10_56_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_10_56_base : receiptBase endpoint_10_56_flag endpoint_10_56_sources = some 249049179803668687 := by decide +kernel
private theorem endpoint_10_56_w0 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 2 249049179803668687 = some 249049179803668687 := by decide +kernel
private theorem endpoint_10_56_w2 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 2 2 249049179803668687 = some 249049179803668687 := by decide +kernel
private theorem endpoint_10_56_p4 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 4 249049179803668687 = some 249049179803668687 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 2 2 249049179803668687 249049179803668687 249049179803668687 endpoint_10_56_w0 endpoint_10_56_w2
private theorem endpoint_10_56_w4 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 4 2 249049179803668687 = some 249049179803668687 := by decide +kernel
private theorem endpoint_10_56_p6 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 6 249049179803668687 = some 249049179803668687 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 4 2 249049179803668687 249049179803668687 249049179803668687 endpoint_10_56_p4 endpoint_10_56_w4
private theorem endpoint_10_56_w6 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 6 2 249049179803668687 = some 249049179803668687 := by decide +kernel
private theorem endpoint_10_56_p8 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 8 249049179803668687 = some 249049179803668687 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 6 2 249049179803668687 249049179803668687 249049179803668687 endpoint_10_56_p6 endpoint_10_56_w6
private theorem endpoint_10_56_w8 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 8 1 249049179803668687 = some 249049179803668687 := by decide +kernel
private theorem endpoint_10_56_p9 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 9 249049179803668687 = some 249049179803668687 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 8 1 249049179803668687 249049179803668687 249049179803668687 endpoint_10_56_p8 endpoint_10_56_w8
def endpoint_10_56 : CertifiedEndpoint :=
  ⟨⟨10, 56, 3547⟩, 249049179803668687, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_10_56_flag endpoint_10_56_sources 9 249049179803668687 249049179803668687 rfl endpoint_10_56_base endpoint_10_56_p9) (by decide)⟩
private def endpoint_10_57_flag : Flag := ⟨10, 57, 3502⟩
private def endpoint_10_57_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_57_base : receiptBase endpoint_10_57_flag endpoint_10_57_sources = some 252164238370413449 := by decide +kernel
private theorem endpoint_10_57_w0 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 2 252164238370413449 = some 252164238370413449 := by decide +kernel
private theorem endpoint_10_57_w2 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 2 2 252164238370413449 = some 252164238370413449 := by decide +kernel
private theorem endpoint_10_57_p4 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 4 252164238370413449 = some 252164238370413449 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 2 2 252164238370413449 252164238370413449 252164238370413449 endpoint_10_57_w0 endpoint_10_57_w2
private theorem endpoint_10_57_w4 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 4 2 252164238370413449 = some 252164238370413449 := by decide +kernel
private theorem endpoint_10_57_p6 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 6 252164238370413449 = some 252164238370413449 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 4 2 252164238370413449 252164238370413449 252164238370413449 endpoint_10_57_p4 endpoint_10_57_w4
private theorem endpoint_10_57_w6 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 6 2 252164238370413449 = some 252164238370413449 := by decide +kernel
private theorem endpoint_10_57_p8 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 8 252164238370413449 = some 252164238370413449 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 6 2 252164238370413449 252164238370413449 252164238370413449 endpoint_10_57_p6 endpoint_10_57_w6
private theorem endpoint_10_57_w8 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 8 1 252164238370413449 = some 252164238370413449 := by decide +kernel
private theorem endpoint_10_57_p9 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 9 252164238370413449 = some 252164238370413449 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 8 1 252164238370413449 252164238370413449 252164238370413449 endpoint_10_57_p8 endpoint_10_57_w8
def endpoint_10_57 : CertifiedEndpoint :=
  ⟨⟨10, 57, 3502⟩, 252164238370413449, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_57_flag endpoint_10_57_sources 9 252164238370413449 252164238370413449 rfl endpoint_10_57_base endpoint_10_57_p9) (by decide)⟩
private def endpoint_10_58_flag : Flag := ⟨10, 58, 3456⟩
private def endpoint_10_58_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_58_base : receiptBase endpoint_10_58_flag endpoint_10_58_sources = some 252681704645453234 := by decide +kernel
private theorem endpoint_10_58_w0 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 2 252681704645453234 = some 252681704645453234 := by decide +kernel
private theorem endpoint_10_58_w2 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 2 2 252681704645453234 = some 252681704645453234 := by decide +kernel
private theorem endpoint_10_58_p4 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 4 252681704645453234 = some 252681704645453234 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 2 2 252681704645453234 252681704645453234 252681704645453234 endpoint_10_58_w0 endpoint_10_58_w2
private theorem endpoint_10_58_w4 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 4 2 252681704645453234 = some 252681704645453234 := by decide +kernel
private theorem endpoint_10_58_p6 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 6 252681704645453234 = some 252681704645453234 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 4 2 252681704645453234 252681704645453234 252681704645453234 endpoint_10_58_p4 endpoint_10_58_w4
private theorem endpoint_10_58_w6 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 6 2 252681704645453234 = some 252681704645453234 := by decide +kernel
private theorem endpoint_10_58_p8 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 8 252681704645453234 = some 252681704645453234 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 6 2 252681704645453234 252681704645453234 252681704645453234 endpoint_10_58_p6 endpoint_10_58_w6
private theorem endpoint_10_58_w8 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 8 1 252681704645453234 = some 252681704645453234 := by decide +kernel
private theorem endpoint_10_58_p9 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 9 252681704645453234 = some 252681704645453234 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 8 1 252681704645453234 252681704645453234 252681704645453234 endpoint_10_58_p8 endpoint_10_58_w8
def endpoint_10_58 : CertifiedEndpoint :=
  ⟨⟨10, 58, 3456⟩, 252681704645453234, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_58_flag endpoint_10_58_sources 9 252681704645453234 252681704645453234 rfl endpoint_10_58_base endpoint_10_58_p9) (by decide)⟩
private def endpoint_10_59_flag : Flag := ⟨10, 59, 3408⟩
private def endpoint_10_59_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_59_base : receiptBase endpoint_10_59_flag endpoint_10_59_sources = some 252951260802996194 := by decide +kernel
private theorem endpoint_10_59_w0 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 2 252951260802996194 = some 252951260802996194 := by decide +kernel
private theorem endpoint_10_59_w2 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 2 2 252951260802996194 = some 252951260802996194 := by decide +kernel
private theorem endpoint_10_59_p4 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 4 252951260802996194 = some 252951260802996194 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 2 2 252951260802996194 252951260802996194 252951260802996194 endpoint_10_59_w0 endpoint_10_59_w2
private theorem endpoint_10_59_w4 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 4 2 252951260802996194 = some 252951260802996194 := by decide +kernel
private theorem endpoint_10_59_p6 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 6 252951260802996194 = some 252951260802996194 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 4 2 252951260802996194 252951260802996194 252951260802996194 endpoint_10_59_p4 endpoint_10_59_w4
private theorem endpoint_10_59_w6 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 6 2 252951260802996194 = some 252951260802996194 := by decide +kernel
private theorem endpoint_10_59_p8 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 8 252951260802996194 = some 252951260802996194 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 6 2 252951260802996194 252951260802996194 252951260802996194 endpoint_10_59_p6 endpoint_10_59_w6
private theorem endpoint_10_59_w8 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 8 1 252951260802996194 = some 252951260802996194 := by decide +kernel
private theorem endpoint_10_59_p9 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 9 252951260802996194 = some 252951260802996194 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 8 1 252951260802996194 252951260802996194 252951260802996194 endpoint_10_59_p8 endpoint_10_59_w8
def endpoint_10_59 : CertifiedEndpoint :=
  ⟨⟨10, 59, 3408⟩, 252951260802996194, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_59_flag endpoint_10_59_sources 9 252951260802996194 252951260802996194 rfl endpoint_10_59_base endpoint_10_59_p9) (by decide)⟩
private def endpoint_10_60_flag : Flag := ⟨10, 60, 3358⟩
private def endpoint_10_60_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_60_base : receiptBase endpoint_10_60_flag endpoint_10_60_sources = some 252966377526174388 := by decide +kernel
private theorem endpoint_10_60_w0 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 2 252966377526174388 = some 252966377526174388 := by decide +kernel
private theorem endpoint_10_60_w2 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 2 2 252966377526174388 = some 252966377526174388 := by decide +kernel
private theorem endpoint_10_60_p4 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 4 252966377526174388 = some 252966377526174388 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 2 2 252966377526174388 252966377526174388 252966377526174388 endpoint_10_60_w0 endpoint_10_60_w2
private theorem endpoint_10_60_w4 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 4 2 252966377526174388 = some 252966377526174388 := by decide +kernel
private theorem endpoint_10_60_p6 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 6 252966377526174388 = some 252966377526174388 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 4 2 252966377526174388 252966377526174388 252966377526174388 endpoint_10_60_p4 endpoint_10_60_w4
private theorem endpoint_10_60_w6 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 6 2 252966377526174388 = some 252966377526174388 := by decide +kernel
private theorem endpoint_10_60_p8 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 8 252966377526174388 = some 252966377526174388 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 6 2 252966377526174388 252966377526174388 252966377526174388 endpoint_10_60_p6 endpoint_10_60_w6
private theorem endpoint_10_60_w8 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 8 1 252966377526174388 = some 252966377526174388 := by decide +kernel
private theorem endpoint_10_60_p9 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 9 252966377526174388 = some 252966377526174388 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 8 1 252966377526174388 252966377526174388 252966377526174388 endpoint_10_60_p8 endpoint_10_60_w8
def endpoint_10_60 : CertifiedEndpoint :=
  ⟨⟨10, 60, 3358⟩, 252966377526174388, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_60_flag endpoint_10_60_sources 9 252966377526174388 252966377526174388 rfl endpoint_10_60_base endpoint_10_60_p9) (by decide)⟩
private def endpoint_10_61_flag : Flag := ⟨10, 61, 3305⟩
private def endpoint_10_61_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_61_base : receiptBase endpoint_10_61_flag endpoint_10_61_sources = some 252644996206142019 := by decide +kernel
private theorem endpoint_10_61_w0 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 2 252644996206142019 = some 252644996206142019 := by decide +kernel
private theorem endpoint_10_61_w2 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 2 2 252644996206142019 = some 252644996206142019 := by decide +kernel
private theorem endpoint_10_61_p4 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 4 252644996206142019 = some 252644996206142019 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 2 2 252644996206142019 252644996206142019 252644996206142019 endpoint_10_61_w0 endpoint_10_61_w2
private theorem endpoint_10_61_w4 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 4 2 252644996206142019 = some 252644996206142019 := by decide +kernel
private theorem endpoint_10_61_p6 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 6 252644996206142019 = some 252644996206142019 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 4 2 252644996206142019 252644996206142019 252644996206142019 endpoint_10_61_p4 endpoint_10_61_w4
private theorem endpoint_10_61_w6 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 6 2 252644996206142019 = some 252644996206142019 := by decide +kernel
private theorem endpoint_10_61_p8 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 8 252644996206142019 = some 252644996206142019 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 6 2 252644996206142019 252644996206142019 252644996206142019 endpoint_10_61_p6 endpoint_10_61_w6
private theorem endpoint_10_61_w8 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 8 1 252644996206142019 = some 252644996206142019 := by decide +kernel
private theorem endpoint_10_61_p9 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 9 252644996206142019 = some 252644996206142019 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 8 1 252644996206142019 252644996206142019 252644996206142019 endpoint_10_61_p8 endpoint_10_61_w8
def endpoint_10_61 : CertifiedEndpoint :=
  ⟨⟨10, 61, 3305⟩, 252644996206142019, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_61_flag endpoint_10_61_sources 9 252644996206142019 252644996206142019 rfl endpoint_10_61_base endpoint_10_61_p9) (by decide)⟩
private def endpoint_10_62_flag : Flag := ⟨10, 62, 3250⟩
private def endpoint_10_62_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_10_62_base : receiptBase endpoint_10_62_flag endpoint_10_62_sources = some 253353749053986684 := by decide +kernel
private theorem endpoint_10_62_w0 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 2 253353749053986684 = some 253353749053986684 := by decide +kernel
private theorem endpoint_10_62_w2 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 2 2 253353749053986684 = some 253353749053986684 := by decide +kernel
private theorem endpoint_10_62_p4 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 4 253353749053986684 = some 253353749053986684 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 2 2 253353749053986684 253353749053986684 253353749053986684 endpoint_10_62_w0 endpoint_10_62_w2
private theorem endpoint_10_62_w4 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 4 2 253353749053986684 = some 253353749053986684 := by decide +kernel
private theorem endpoint_10_62_p6 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 6 253353749053986684 = some 253353749053986684 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 4 2 253353749053986684 253353749053986684 253353749053986684 endpoint_10_62_p4 endpoint_10_62_w4
private theorem endpoint_10_62_w6 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 6 2 253353749053986684 = some 253353749053986684 := by decide +kernel
private theorem endpoint_10_62_p8 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 8 253353749053986684 = some 253353749053986684 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 6 2 253353749053986684 253353749053986684 253353749053986684 endpoint_10_62_p6 endpoint_10_62_w6
private theorem endpoint_10_62_w8 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 8 1 253353749053986684 = some 253353749053986684 := by decide +kernel
private theorem endpoint_10_62_p9 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 9 253353749053986684 = some 253353749053986684 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 8 1 253353749053986684 253353749053986684 253353749053986684 endpoint_10_62_p8 endpoint_10_62_w8
def endpoint_10_62 : CertifiedEndpoint :=
  ⟨⟨10, 62, 3250⟩, 253353749053986684, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_10_62_flag endpoint_10_62_sources 9 253353749053986684 253353749053986684 rfl endpoint_10_62_base endpoint_10_62_p9) (by decide)⟩
private def endpoint_10_63_flag : Flag := ⟨10, 63, 3192⟩
private def endpoint_10_63_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_10_63_base : receiptBase endpoint_10_63_flag endpoint_10_63_sources = some 252406214171218285 := by decide +kernel
private theorem endpoint_10_63_w0 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 2 252406214171218285 = some 252406214171218285 := by decide +kernel
private theorem endpoint_10_63_w2 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 2 2 252406214171218285 = some 252406214171218285 := by decide +kernel
private theorem endpoint_10_63_p4 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 4 252406214171218285 = some 252406214171218285 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 2 2 252406214171218285 252406214171218285 252406214171218285 endpoint_10_63_w0 endpoint_10_63_w2
private theorem endpoint_10_63_w4 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 4 2 252406214171218285 = some 252406214171218285 := by decide +kernel
private theorem endpoint_10_63_p6 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 6 252406214171218285 = some 252406214171218285 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 4 2 252406214171218285 252406214171218285 252406214171218285 endpoint_10_63_p4 endpoint_10_63_w4
private theorem endpoint_10_63_w6 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 6 2 252406214171218285 = some 252406214171218285 := by decide +kernel
private theorem endpoint_10_63_p8 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 8 252406214171218285 = some 252406214171218285 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 6 2 252406214171218285 252406214171218285 252406214171218285 endpoint_10_63_p6 endpoint_10_63_w6
private theorem endpoint_10_63_w8 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 8 1 252406214171218285 = some 252406214171218285 := by decide +kernel
private theorem endpoint_10_63_p9 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 9 252406214171218285 = some 252406214171218285 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 8 1 252406214171218285 252406214171218285 252406214171218285 endpoint_10_63_p8 endpoint_10_63_w8
def endpoint_10_63 : CertifiedEndpoint :=
  ⟨⟨10, 63, 3192⟩, 252406214171218285, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_10_63_flag endpoint_10_63_sources 9 252406214171218285 252406214171218285 rfl endpoint_10_63_base endpoint_10_63_p9) (by decide)⟩
private def endpoint_10_64_flag : Flag := ⟨10, 64, 3132⟩
private def endpoint_10_64_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_10_64_base : receiptBase endpoint_10_64_flag endpoint_10_64_sources = some 252524349912166872 := by decide +kernel
private theorem endpoint_10_64_w0 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 2 252524349912166872 = some 252524349912166872 := by decide +kernel
private theorem endpoint_10_64_w2 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 2 2 252524349912166872 = some 252524349912166872 := by decide +kernel
private theorem endpoint_10_64_p4 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 4 252524349912166872 = some 252524349912166872 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 2 2 252524349912166872 252524349912166872 252524349912166872 endpoint_10_64_w0 endpoint_10_64_w2
private theorem endpoint_10_64_w4 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 4 2 252524349912166872 = some 252524349912166872 := by decide +kernel
private theorem endpoint_10_64_p6 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 6 252524349912166872 = some 252524349912166872 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 4 2 252524349912166872 252524349912166872 252524349912166872 endpoint_10_64_p4 endpoint_10_64_w4
private theorem endpoint_10_64_w6 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 6 2 252524349912166872 = some 252524349912166872 := by decide +kernel
private theorem endpoint_10_64_p8 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 8 252524349912166872 = some 252524349912166872 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 6 2 252524349912166872 252524349912166872 252524349912166872 endpoint_10_64_p6 endpoint_10_64_w6
private theorem endpoint_10_64_w8 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 8 1 252524349912166872 = some 252524349912166872 := by decide +kernel
private theorem endpoint_10_64_p9 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 9 252524349912166872 = some 252524349912166872 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 8 1 252524349912166872 252524349912166872 252524349912166872 endpoint_10_64_p8 endpoint_10_64_w8
def endpoint_10_64 : CertifiedEndpoint :=
  ⟨⟨10, 64, 3132⟩, 252524349912166872, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_10_64_flag endpoint_10_64_sources 9 252524349912166872 252524349912166872 rfl endpoint_10_64_base endpoint_10_64_p9) (by decide)⟩
private def endpoint_10_65_flag : Flag := ⟨10, 65, 3068⟩
private def endpoint_10_65_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_10_65_base : receiptBase endpoint_10_65_flag endpoint_10_65_sources = some 250829108417452924 := by decide +kernel
private theorem endpoint_10_65_w0 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 2 250829108417452924 = some 250829108417452924 := by decide +kernel
private theorem endpoint_10_65_w2 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 2 2 250829108417452924 = some 250829108417452924 := by decide +kernel
private theorem endpoint_10_65_p4 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 4 250829108417452924 = some 250829108417452924 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 2 2 250829108417452924 250829108417452924 250829108417452924 endpoint_10_65_w0 endpoint_10_65_w2
private theorem endpoint_10_65_w4 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 4 2 250829108417452924 = some 250829108417452924 := by decide +kernel
private theorem endpoint_10_65_p6 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 6 250829108417452924 = some 250829108417452924 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 4 2 250829108417452924 250829108417452924 250829108417452924 endpoint_10_65_p4 endpoint_10_65_w4
private theorem endpoint_10_65_w6 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 6 2 250829108417452924 = some 250829108417452924 := by decide +kernel
private theorem endpoint_10_65_p8 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 8 250829108417452924 = some 250829108417452924 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 6 2 250829108417452924 250829108417452924 250829108417452924 endpoint_10_65_p6 endpoint_10_65_w6
private theorem endpoint_10_65_w8 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 8 1 250829108417452924 = some 250829108417452924 := by decide +kernel
private theorem endpoint_10_65_p9 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 9 250829108417452924 = some 250829108417452924 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 8 1 250829108417452924 250829108417452924 250829108417452924 endpoint_10_65_p8 endpoint_10_65_w8
def endpoint_10_65 : CertifiedEndpoint :=
  ⟨⟨10, 65, 3068⟩, 250829108417452924, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_10_65_flag endpoint_10_65_sources 9 250829108417452924 250829108417452924 rfl endpoint_10_65_base endpoint_10_65_p9) (by decide)⟩
private def endpoint_10_66_flag : Flag := ⟨10, 66, 3001⟩
private def endpoint_10_66_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_10_66_base : receiptBase endpoint_10_66_flag endpoint_10_66_sources = some 250129416734356406 := by decide +kernel
private theorem endpoint_10_66_w0 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 2 250129416734356406 = some 250129416734356406 := by decide +kernel
private theorem endpoint_10_66_w2 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 2 2 250129416734356406 = some 250129416734356406 := by decide +kernel
private theorem endpoint_10_66_p4 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 4 250129416734356406 = some 250129416734356406 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 2 2 250129416734356406 250129416734356406 250129416734356406 endpoint_10_66_w0 endpoint_10_66_w2
private theorem endpoint_10_66_w4 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 4 2 250129416734356406 = some 250129416734356406 := by decide +kernel
private theorem endpoint_10_66_p6 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 6 250129416734356406 = some 250129416734356406 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 4 2 250129416734356406 250129416734356406 250129416734356406 endpoint_10_66_p4 endpoint_10_66_w4
private theorem endpoint_10_66_w6 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 6 2 250129416734356406 = some 250129416734356406 := by decide +kernel
private theorem endpoint_10_66_p8 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 8 250129416734356406 = some 250129416734356406 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 6 2 250129416734356406 250129416734356406 250129416734356406 endpoint_10_66_p6 endpoint_10_66_w6
private theorem endpoint_10_66_w8 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 8 1 250129416734356406 = some 250129416734356406 := by decide +kernel
private theorem endpoint_10_66_p9 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 9 250129416734356406 = some 250129416734356406 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 8 1 250129416734356406 250129416734356406 250129416734356406 endpoint_10_66_p8 endpoint_10_66_w8
def endpoint_10_66 : CertifiedEndpoint :=
  ⟨⟨10, 66, 3001⟩, 250129416734356406, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_10_66_flag endpoint_10_66_sources 9 250129416734356406 250129416734356406 rfl endpoint_10_66_base endpoint_10_66_p9) (by decide)⟩
private def endpoint_10_67_flag : Flag := ⟨10, 67, 2932⟩
private def endpoint_10_67_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_10_67_base : receiptBase endpoint_10_67_flag endpoint_10_67_sources = some 249131099354438662 := by decide +kernel
private theorem endpoint_10_67_w0 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 2 249131099354438662 = some 249131099354438662 := by decide +kernel
private theorem endpoint_10_67_w2 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 2 2 249131099354438662 = some 249131099354438662 := by decide +kernel
private theorem endpoint_10_67_p4 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 4 249131099354438662 = some 249131099354438662 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 2 2 249131099354438662 249131099354438662 249131099354438662 endpoint_10_67_w0 endpoint_10_67_w2
private theorem endpoint_10_67_w4 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 4 2 249131099354438662 = some 249131099354438662 := by decide +kernel
private theorem endpoint_10_67_p6 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 6 249131099354438662 = some 249131099354438662 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 4 2 249131099354438662 249131099354438662 249131099354438662 endpoint_10_67_p4 endpoint_10_67_w4
private theorem endpoint_10_67_w6 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 6 2 249131099354438662 = some 249131099354438662 := by decide +kernel
private theorem endpoint_10_67_p8 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 8 249131099354438662 = some 249131099354438662 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 6 2 249131099354438662 249131099354438662 249131099354438662 endpoint_10_67_p6 endpoint_10_67_w6
private theorem endpoint_10_67_w8 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 8 1 249131099354438662 = some 249131099354438662 := by decide +kernel
private theorem endpoint_10_67_p9 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 9 249131099354438662 = some 249131099354438662 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 8 1 249131099354438662 249131099354438662 249131099354438662 endpoint_10_67_p8 endpoint_10_67_w8
def endpoint_10_67 : CertifiedEndpoint :=
  ⟨⟨10, 67, 2932⟩, 249131099354438662, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_10_67_flag endpoint_10_67_sources 9 249131099354438662 249131099354438662 rfl endpoint_10_67_base endpoint_10_67_p9) (by decide)⟩
private def endpoint_10_68_flag : Flag := ⟨10, 68, 2859⟩
private def endpoint_10_68_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_68_base : receiptBase endpoint_10_68_flag endpoint_10_68_sources = some 247495981885873382 := by decide +kernel
private theorem endpoint_10_68_w0 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 2 247495981885873382 = some 247495981885873382 := by decide +kernel
private theorem endpoint_10_68_w2 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 2 2 247495981885873382 = some 247495981885873382 := by decide +kernel
private theorem endpoint_10_68_p4 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 4 247495981885873382 = some 247495981885873382 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 2 2 247495981885873382 247495981885873382 247495981885873382 endpoint_10_68_w0 endpoint_10_68_w2
private theorem endpoint_10_68_w4 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 4 2 247495981885873382 = some 247495981885873382 := by decide +kernel
private theorem endpoint_10_68_p6 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 6 247495981885873382 = some 247495981885873382 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 4 2 247495981885873382 247495981885873382 247495981885873382 endpoint_10_68_p4 endpoint_10_68_w4
private theorem endpoint_10_68_w6 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 6 2 247495981885873382 = some 247495981885873382 := by decide +kernel
private theorem endpoint_10_68_p8 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 8 247495981885873382 = some 247495981885873382 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 6 2 247495981885873382 247495981885873382 247495981885873382 endpoint_10_68_p6 endpoint_10_68_w6
private theorem endpoint_10_68_w8 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 8 1 247495981885873382 = some 247495981885873382 := by decide +kernel
private theorem endpoint_10_68_p9 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 9 247495981885873382 = some 247495981885873382 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 8 1 247495981885873382 247495981885873382 247495981885873382 endpoint_10_68_p8 endpoint_10_68_w8
def endpoint_10_68 : CertifiedEndpoint :=
  ⟨⟨10, 68, 2859⟩, 247495981885873382, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_68_flag endpoint_10_68_sources 9 247495981885873382 247495981885873382 rfl endpoint_10_68_base endpoint_10_68_p9) (by decide)⟩
private def endpoint_10_69_flag : Flag := ⟨10, 69, 2783⟩
private def endpoint_10_69_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_69_base : receiptBase endpoint_10_69_flag endpoint_10_69_sources = some 244136585283000269 := by decide +kernel
private theorem endpoint_10_69_w0 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 2 244136585283000269 = some 244136585283000269 := by decide +kernel
private theorem endpoint_10_69_w2 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 2 2 244136585283000269 = some 244136585283000269 := by decide +kernel
private theorem endpoint_10_69_p4 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 4 244136585283000269 = some 244136585283000269 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 2 2 244136585283000269 244136585283000269 244136585283000269 endpoint_10_69_w0 endpoint_10_69_w2
private theorem endpoint_10_69_w4 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 4 2 244136585283000269 = some 244136585283000269 := by decide +kernel
private theorem endpoint_10_69_p6 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 6 244136585283000269 = some 244136585283000269 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 4 2 244136585283000269 244136585283000269 244136585283000269 endpoint_10_69_p4 endpoint_10_69_w4
private theorem endpoint_10_69_w6 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 6 2 244136585283000269 = some 244136585283000269 := by decide +kernel
private theorem endpoint_10_69_p8 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 8 244136585283000269 = some 244136585283000269 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 6 2 244136585283000269 244136585283000269 244136585283000269 endpoint_10_69_p6 endpoint_10_69_w6
private theorem endpoint_10_69_w8 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 8 1 244136585283000269 = some 244136585283000269 := by decide +kernel
private theorem endpoint_10_69_p9 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 9 244136585283000269 = some 244136585283000269 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 8 1 244136585283000269 244136585283000269 244136585283000269 endpoint_10_69_p8 endpoint_10_69_w8
def endpoint_10_69 : CertifiedEndpoint :=
  ⟨⟨10, 69, 2783⟩, 244136585283000269, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_69_flag endpoint_10_69_sources 9 244136585283000269 244136585283000269 rfl endpoint_10_69_base endpoint_10_69_p9) (by decide)⟩
private def endpoint_10_70_flag : Flag := ⟨10, 70, 2704⟩
private def endpoint_10_70_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_70_base : receiptBase endpoint_10_70_flag endpoint_10_70_sources = some 240339785224597126 := by decide +kernel
private theorem endpoint_10_70_w0 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 2 240339785224597126 = some 240339785224597126 := by decide +kernel
private theorem endpoint_10_70_w2 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 2 2 240339785224597126 = some 240339785224597126 := by decide +kernel
private theorem endpoint_10_70_p4 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 4 240339785224597126 = some 240339785224597126 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 2 2 240339785224597126 240339785224597126 240339785224597126 endpoint_10_70_w0 endpoint_10_70_w2
private theorem endpoint_10_70_w4 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 4 2 240339785224597126 = some 240339785224597126 := by decide +kernel
private theorem endpoint_10_70_p6 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 6 240339785224597126 = some 240339785224597126 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 4 2 240339785224597126 240339785224597126 240339785224597126 endpoint_10_70_p4 endpoint_10_70_w4
private theorem endpoint_10_70_w6 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 6 2 240339785224597126 = some 240339785224597126 := by decide +kernel
private theorem endpoint_10_70_p8 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 8 240339785224597126 = some 240339785224597126 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 6 2 240339785224597126 240339785224597126 240339785224597126 endpoint_10_70_p6 endpoint_10_70_w6
private theorem endpoint_10_70_w8 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 8 1 240339785224597126 = some 240339785224597126 := by decide +kernel
private theorem endpoint_10_70_p9 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 9 240339785224597126 = some 240339785224597126 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 8 1 240339785224597126 240339785224597126 240339785224597126 endpoint_10_70_p8 endpoint_10_70_w8
def endpoint_10_70 : CertifiedEndpoint :=
  ⟨⟨10, 70, 2704⟩, 240339785224597126, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_70_flag endpoint_10_70_sources 9 240339785224597126 240339785224597126 rfl endpoint_10_70_base endpoint_10_70_p9) (by decide)⟩
private def endpoint_10_71_flag : Flag := ⟨10, 71, 2623⟩
private def endpoint_10_71_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_71_base : receiptBase endpoint_10_71_flag endpoint_10_71_sources = some 236184522877482375 := by decide +kernel
private theorem endpoint_10_71_w0 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 2 236184522877482375 = some 236184522877482375 := by decide +kernel
private theorem endpoint_10_71_w2 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 2 2 236184522877482375 = some 236184522877482375 := by decide +kernel
private theorem endpoint_10_71_p4 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 4 236184522877482375 = some 236184522877482375 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 2 2 236184522877482375 236184522877482375 236184522877482375 endpoint_10_71_w0 endpoint_10_71_w2
private theorem endpoint_10_71_w4 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 4 2 236184522877482375 = some 236184522877482375 := by decide +kernel
private theorem endpoint_10_71_p6 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 6 236184522877482375 = some 236184522877482375 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 4 2 236184522877482375 236184522877482375 236184522877482375 endpoint_10_71_p4 endpoint_10_71_w4
private theorem endpoint_10_71_w6 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 6 2 236184522877482375 = some 236184522877482375 := by decide +kernel
private theorem endpoint_10_71_p8 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 8 236184522877482375 = some 236184522877482375 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 6 2 236184522877482375 236184522877482375 236184522877482375 endpoint_10_71_p6 endpoint_10_71_w6
private theorem endpoint_10_71_w8 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 8 1 236184522877482375 = some 236184522877482375 := by decide +kernel
private theorem endpoint_10_71_p9 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 9 236184522877482375 = some 236184522877482375 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 8 1 236184522877482375 236184522877482375 236184522877482375 endpoint_10_71_p8 endpoint_10_71_w8
def endpoint_10_71 : CertifiedEndpoint :=
  ⟨⟨10, 71, 2623⟩, 236184522877482375, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_71_flag endpoint_10_71_sources 9 236184522877482375 236184522877482375 rfl endpoint_10_71_base endpoint_10_71_p9) (by decide)⟩
private def endpoint_10_72_flag : Flag := ⟨10, 72, 2538⟩
private def endpoint_10_72_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_10_72_base : receiptBase endpoint_10_72_flag endpoint_10_72_sources = some 236413205529307327 := by decide +kernel
private theorem endpoint_10_72_w0 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 2 236413205529307327 = some 236413205529307327 := by decide +kernel
private theorem endpoint_10_72_w2 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 2 2 236413205529307327 = some 236413205529307327 := by decide +kernel
private theorem endpoint_10_72_p4 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 4 236413205529307327 = some 236413205529307327 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 2 2 236413205529307327 236413205529307327 236413205529307327 endpoint_10_72_w0 endpoint_10_72_w2
private theorem endpoint_10_72_w4 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 4 2 236413205529307327 = some 236413205529307327 := by decide +kernel
private theorem endpoint_10_72_p6 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 6 236413205529307327 = some 236413205529307327 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 4 2 236413205529307327 236413205529307327 236413205529307327 endpoint_10_72_p4 endpoint_10_72_w4
private theorem endpoint_10_72_w6 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 6 2 236413205529307327 = some 236413205529307327 := by decide +kernel
private theorem endpoint_10_72_p8 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 8 236413205529307327 = some 236413205529307327 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 6 2 236413205529307327 236413205529307327 236413205529307327 endpoint_10_72_p6 endpoint_10_72_w6
private theorem endpoint_10_72_w8 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 8 1 236413205529307327 = some 236413205529307327 := by decide +kernel
private theorem endpoint_10_72_p9 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 9 236413205529307327 = some 236413205529307327 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 8 1 236413205529307327 236413205529307327 236413205529307327 endpoint_10_72_p8 endpoint_10_72_w8
def endpoint_10_72 : CertifiedEndpoint :=
  ⟨⟨10, 72, 2538⟩, 236413205529307327, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_10_72_flag endpoint_10_72_sources 9 236413205529307327 236413205529307327 rfl endpoint_10_72_base endpoint_10_72_p9) (by decide)⟩
private def endpoint_10_73_flag : Flag := ⟨10, 73, 2450⟩
private def endpoint_10_73_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_10_73_base : receiptBase endpoint_10_73_flag endpoint_10_73_sources = some 231193404464988458 := by decide +kernel
private theorem endpoint_10_73_w0 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 2 231193404464988458 = some 231193404464988458 := by decide +kernel
private theorem endpoint_10_73_w2 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 2 2 231193404464988458 = some 231193404464988458 := by decide +kernel
private theorem endpoint_10_73_p4 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 4 231193404464988458 = some 231193404464988458 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 2 2 231193404464988458 231193404464988458 231193404464988458 endpoint_10_73_w0 endpoint_10_73_w2
private theorem endpoint_10_73_w4 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 4 2 231193404464988458 = some 231193404464988458 := by decide +kernel
private theorem endpoint_10_73_p6 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 6 231193404464988458 = some 231193404464988458 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 4 2 231193404464988458 231193404464988458 231193404464988458 endpoint_10_73_p4 endpoint_10_73_w4
private theorem endpoint_10_73_w6 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 6 2 231193404464988458 = some 231193404464988458 := by decide +kernel
private theorem endpoint_10_73_p8 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 8 231193404464988458 = some 231193404464988458 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 6 2 231193404464988458 231193404464988458 231193404464988458 endpoint_10_73_p6 endpoint_10_73_w6
private theorem endpoint_10_73_w8 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 8 1 231193404464988458 = some 231193404464988458 := by decide +kernel
private theorem endpoint_10_73_p9 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 9 231193404464988458 = some 231193404464988458 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 8 1 231193404464988458 231193404464988458 231193404464988458 endpoint_10_73_p8 endpoint_10_73_w8
def endpoint_10_73 : CertifiedEndpoint :=
  ⟨⟨10, 73, 2450⟩, 231193404464988458, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_10_73_flag endpoint_10_73_sources 9 231193404464988458 231193404464988458 rfl endpoint_10_73_base endpoint_10_73_p9) (by decide)⟩
private def endpoint_10_74_flag : Flag := ⟨10, 74, 2359⟩
private def endpoint_10_74_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_10_74_base : receiptBase endpoint_10_74_flag endpoint_10_74_sources = some 225491865624882560 := by decide +kernel
private theorem endpoint_10_74_w0 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 2 225491865624882560 = some 225491865624882560 := by decide +kernel
private theorem endpoint_10_74_w2 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 2 2 225491865624882560 = some 225491865624882560 := by decide +kernel
private theorem endpoint_10_74_p4 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 4 225491865624882560 = some 225491865624882560 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 2 2 225491865624882560 225491865624882560 225491865624882560 endpoint_10_74_w0 endpoint_10_74_w2
private theorem endpoint_10_74_w4 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 4 2 225491865624882560 = some 225491865624882560 := by decide +kernel
private theorem endpoint_10_74_p6 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 6 225491865624882560 = some 225491865624882560 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 4 2 225491865624882560 225491865624882560 225491865624882560 endpoint_10_74_p4 endpoint_10_74_w4
private theorem endpoint_10_74_w6 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 6 2 225491865624882560 = some 225491865624882560 := by decide +kernel
private theorem endpoint_10_74_p8 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 8 225491865624882560 = some 225491865624882560 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 6 2 225491865624882560 225491865624882560 225491865624882560 endpoint_10_74_p6 endpoint_10_74_w6
private theorem endpoint_10_74_w8 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 8 1 225491865624882560 = some 225491865624882560 := by decide +kernel
private theorem endpoint_10_74_p9 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 9 225491865624882560 = some 225491865624882560 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 8 1 225491865624882560 225491865624882560 225491865624882560 endpoint_10_74_p8 endpoint_10_74_w8
def endpoint_10_74 : CertifiedEndpoint :=
  ⟨⟨10, 74, 2359⟩, 225491865624882560, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_10_74_flag endpoint_10_74_sources 9 225491865624882560 225491865624882560 rfl endpoint_10_74_base endpoint_10_74_p9) (by decide)⟩
private def endpoint_10_75_flag : Flag := ⟨10, 75, 2265⟩
private def endpoint_10_75_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_10_75_base : receiptBase endpoint_10_75_flag endpoint_10_75_sources = some 221053085584599941 := by decide +kernel
private theorem endpoint_10_75_w0 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 2 221053085584599941 = some 221053085584599941 := by decide +kernel
private theorem endpoint_10_75_w2 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 2 2 221053085584599941 = some 221053085584599941 := by decide +kernel
private theorem endpoint_10_75_p4 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 4 221053085584599941 = some 221053085584599941 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 2 2 221053085584599941 221053085584599941 221053085584599941 endpoint_10_75_w0 endpoint_10_75_w2
private theorem endpoint_10_75_w4 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 4 2 221053085584599941 = some 221053085584599941 := by decide +kernel
private theorem endpoint_10_75_p6 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 6 221053085584599941 = some 221053085584599941 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 4 2 221053085584599941 221053085584599941 221053085584599941 endpoint_10_75_p4 endpoint_10_75_w4
private theorem endpoint_10_75_w6 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 6 2 221053085584599941 = some 221053085584599941 := by decide +kernel
private theorem endpoint_10_75_p8 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 8 221053085584599941 = some 221053085584599941 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 6 2 221053085584599941 221053085584599941 221053085584599941 endpoint_10_75_p6 endpoint_10_75_w6
private theorem endpoint_10_75_w8 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 8 1 221053085584599941 = some 221053085584599941 := by decide +kernel
private theorem endpoint_10_75_p9 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 9 221053085584599941 = some 221053085584599941 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 8 1 221053085584599941 221053085584599941 221053085584599941 endpoint_10_75_p8 endpoint_10_75_w8
def endpoint_10_75 : CertifiedEndpoint :=
  ⟨⟨10, 75, 2265⟩, 221053085584599941, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_10_75_flag endpoint_10_75_sources 9 221053085584599941 221053085584599941 rfl endpoint_10_75_base endpoint_10_75_p9) (by decide)⟩
private def endpoint_10_76_flag : Flag := ⟨10, 76, 2167⟩
private def endpoint_10_76_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_10_76_base : receiptBase endpoint_10_76_flag endpoint_10_76_sources = some 214109926361133269 := by decide +kernel
private theorem endpoint_10_76_w0 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 2 214109926361133269 = some 214109926361133269 := by decide +kernel
private theorem endpoint_10_76_w2 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 2 2 214109926361133269 = some 214109926361133269 := by decide +kernel
private theorem endpoint_10_76_p4 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 4 214109926361133269 = some 214109926361133269 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 2 2 214109926361133269 214109926361133269 214109926361133269 endpoint_10_76_w0 endpoint_10_76_w2
private theorem endpoint_10_76_w4 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 4 2 214109926361133269 = some 214109926361133269 := by decide +kernel
private theorem endpoint_10_76_p6 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 6 214109926361133269 = some 214109926361133269 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 4 2 214109926361133269 214109926361133269 214109926361133269 endpoint_10_76_p4 endpoint_10_76_w4
private theorem endpoint_10_76_w6 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 6 2 214109926361133269 = some 214109926361133269 := by decide +kernel
private theorem endpoint_10_76_p8 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 8 214109926361133269 = some 214109926361133269 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 6 2 214109926361133269 214109926361133269 214109926361133269 endpoint_10_76_p6 endpoint_10_76_w6
private theorem endpoint_10_76_w8 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 8 1 214109926361133269 = some 214109926361133269 := by decide +kernel
private theorem endpoint_10_76_p9 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 9 214109926361133269 = some 214109926361133269 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 8 1 214109926361133269 214109926361133269 214109926361133269 endpoint_10_76_p8 endpoint_10_76_w8
def endpoint_10_76 : CertifiedEndpoint :=
  ⟨⟨10, 76, 2167⟩, 214109926361133269, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_10_76_flag endpoint_10_76_sources 9 214109926361133269 214109926361133269 rfl endpoint_10_76_base endpoint_10_76_p9) (by decide)⟩
private def endpoint_10_77_flag : Flag := ⟨10, 77, 2067⟩
private def endpoint_10_77_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_10_77_base : receiptBase endpoint_10_77_flag endpoint_10_77_sources = some 208600035311304974 := by decide +kernel
private theorem endpoint_10_77_w0 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 2 208600035311304974 = some 208600035311304974 := by decide +kernel
private theorem endpoint_10_77_w2 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 2 2 208600035311304974 = some 208600035311304974 := by decide +kernel
private theorem endpoint_10_77_p4 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 4 208600035311304974 = some 208600035311304974 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 2 2 208600035311304974 208600035311304974 208600035311304974 endpoint_10_77_w0 endpoint_10_77_w2
private theorem endpoint_10_77_w4 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 4 2 208600035311304974 = some 208600035311304974 := by decide +kernel
private theorem endpoint_10_77_p6 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 6 208600035311304974 = some 208600035311304974 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 4 2 208600035311304974 208600035311304974 208600035311304974 endpoint_10_77_p4 endpoint_10_77_w4
private theorem endpoint_10_77_w6 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 6 2 208600035311304974 = some 208600035311304974 := by decide +kernel
private theorem endpoint_10_77_p8 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 8 208600035311304974 = some 208600035311304974 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 6 2 208600035311304974 208600035311304974 208600035311304974 endpoint_10_77_p6 endpoint_10_77_w6
private theorem endpoint_10_77_w8 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 8 1 208600035311304974 = some 208600035311304974 := by decide +kernel
private theorem endpoint_10_77_p9 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 9 208600035311304974 = some 208600035311304974 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 8 1 208600035311304974 208600035311304974 208600035311304974 endpoint_10_77_p8 endpoint_10_77_w8
def endpoint_10_77 : CertifiedEndpoint :=
  ⟨⟨10, 77, 2067⟩, 208600035311304974, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_10_77_flag endpoint_10_77_sources 9 208600035311304974 208600035311304974 rfl endpoint_10_77_base endpoint_10_77_p9) (by decide)⟩
private def endpoint_10_78_flag : Flag := ⟨10, 78, 1963⟩
private def endpoint_10_78_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_10_78_base : receiptBase endpoint_10_78_flag endpoint_10_78_sources = some 202393613077854007 := by decide +kernel
private theorem endpoint_10_78_w0 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 2 202393613077854007 = some 202393613077854007 := by decide +kernel
private theorem endpoint_10_78_w2 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 2 2 202393613077854007 = some 202393613077854007 := by decide +kernel
private theorem endpoint_10_78_p4 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 4 202393613077854007 = some 202393613077854007 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 2 2 202393613077854007 202393613077854007 202393613077854007 endpoint_10_78_w0 endpoint_10_78_w2
private theorem endpoint_10_78_w4 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 4 2 202393613077854007 = some 202393613077854007 := by decide +kernel
private theorem endpoint_10_78_p6 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 6 202393613077854007 = some 202393613077854007 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 4 2 202393613077854007 202393613077854007 202393613077854007 endpoint_10_78_p4 endpoint_10_78_w4
private theorem endpoint_10_78_w6 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 6 2 202393613077854007 = some 202393613077854007 := by decide +kernel
private theorem endpoint_10_78_p8 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 8 202393613077854007 = some 202393613077854007 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 6 2 202393613077854007 202393613077854007 202393613077854007 endpoint_10_78_p6 endpoint_10_78_w6
private theorem endpoint_10_78_w8 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 8 1 202393613077854007 = some 202393613077854007 := by decide +kernel
private theorem endpoint_10_78_p9 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 9 202393613077854007 = some 202393613077854007 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 8 1 202393613077854007 202393613077854007 202393613077854007 endpoint_10_78_p8 endpoint_10_78_w8
def endpoint_10_78 : CertifiedEndpoint :=
  ⟨⟨10, 78, 1963⟩, 202393613077854007, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_10_78_flag endpoint_10_78_sources 9 202393613077854007 202393613077854007 rfl endpoint_10_78_base endpoint_10_78_p9) (by decide)⟩
private def endpoint_10_79_flag : Flag := ⟨10, 79, 1857⟩
private def endpoint_10_79_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_10_79_base : receiptBase endpoint_10_79_flag endpoint_10_79_sources = some 193745069031167400 := by decide +kernel
private theorem endpoint_10_79_w0 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 2 193745069031167400 = some 193745069031167400 := by decide +kernel
private theorem endpoint_10_79_w2 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 2 2 193745069031167400 = some 193745069031167400 := by decide +kernel
private theorem endpoint_10_79_p4 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 4 193745069031167400 = some 193745069031167400 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 2 2 193745069031167400 193745069031167400 193745069031167400 endpoint_10_79_w0 endpoint_10_79_w2
private theorem endpoint_10_79_w4 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 4 2 193745069031167400 = some 193745069031167400 := by decide +kernel
private theorem endpoint_10_79_p6 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 6 193745069031167400 = some 193745069031167400 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 4 2 193745069031167400 193745069031167400 193745069031167400 endpoint_10_79_p4 endpoint_10_79_w4
private theorem endpoint_10_79_w6 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 6 2 193745069031167400 = some 193745069031167400 := by decide +kernel
private theorem endpoint_10_79_p8 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 8 193745069031167400 = some 193745069031167400 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 6 2 193745069031167400 193745069031167400 193745069031167400 endpoint_10_79_p6 endpoint_10_79_w6
private theorem endpoint_10_79_w8 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 8 1 193745069031167400 = some 193745069031167400 := by decide +kernel
private theorem endpoint_10_79_p9 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 9 193745069031167400 = some 193745069031167400 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 8 1 193745069031167400 193745069031167400 193745069031167400 endpoint_10_79_p8 endpoint_10_79_w8
def endpoint_10_79 : CertifiedEndpoint :=
  ⟨⟨10, 79, 1857⟩, 193745069031167400, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_10_79_flag endpoint_10_79_sources 9 193745069031167400 193745069031167400 rfl endpoint_10_79_base endpoint_10_79_p9) (by decide)⟩
private def endpoint_10_80_flag : Flag := ⟨10, 80, 1747⟩
private def endpoint_10_80_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_10_80_base : receiptBase endpoint_10_80_flag endpoint_10_80_sources = some 184426500356227759 := by decide +kernel
private theorem endpoint_10_80_w0 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 2 184426500356227759 = some 184426500356227759 := by decide +kernel
private theorem endpoint_10_80_w2 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 2 2 184426500356227759 = some 184426500356227759 := by decide +kernel
private theorem endpoint_10_80_p4 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 4 184426500356227759 = some 184426500356227759 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 2 2 184426500356227759 184426500356227759 184426500356227759 endpoint_10_80_w0 endpoint_10_80_w2
private theorem endpoint_10_80_w4 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 4 2 184426500356227759 = some 184426500356227759 := by decide +kernel
private theorem endpoint_10_80_p6 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 6 184426500356227759 = some 184426500356227759 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 4 2 184426500356227759 184426500356227759 184426500356227759 endpoint_10_80_p4 endpoint_10_80_w4
private theorem endpoint_10_80_w6 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 6 2 184426500356227759 = some 184426500356227759 := by decide +kernel
private theorem endpoint_10_80_p8 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 8 184426500356227759 = some 184426500356227759 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 6 2 184426500356227759 184426500356227759 184426500356227759 endpoint_10_80_p6 endpoint_10_80_w6
private theorem endpoint_10_80_w8 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 8 1 184426500356227759 = some 184426500356227759 := by decide +kernel
private theorem endpoint_10_80_p9 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 9 184426500356227759 = some 184426500356227759 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 8 1 184426500356227759 184426500356227759 184426500356227759 endpoint_10_80_p8 endpoint_10_80_w8
def endpoint_10_80 : CertifiedEndpoint :=
  ⟨⟨10, 80, 1747⟩, 184426500356227759, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_10_80_flag endpoint_10_80_sources 9 184426500356227759 184426500356227759 rfl endpoint_10_80_base endpoint_10_80_p9) (by decide)⟩
private def endpoint_10_81_flag : Flag := ⟨10, 81, 1634⟩
private def endpoint_10_81_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_81_base : receiptBase endpoint_10_81_flag endpoint_10_81_sources = some 177927920694900123 := by decide +kernel
private theorem endpoint_10_81_w0 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 2 177927920694900123 = some 177927920694900123 := by decide +kernel
private theorem endpoint_10_81_w2 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 2 2 177927920694900123 = some 177927920694900123 := by decide +kernel
private theorem endpoint_10_81_p4 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 4 177927920694900123 = some 177927920694900123 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 2 2 177927920694900123 177927920694900123 177927920694900123 endpoint_10_81_w0 endpoint_10_81_w2
private theorem endpoint_10_81_w4 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 4 2 177927920694900123 = some 177927920694900123 := by decide +kernel
private theorem endpoint_10_81_p6 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 6 177927920694900123 = some 177927920694900123 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 4 2 177927920694900123 177927920694900123 177927920694900123 endpoint_10_81_p4 endpoint_10_81_w4
private theorem endpoint_10_81_w6 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 6 2 177927920694900123 = some 177927920694900123 := by decide +kernel
private theorem endpoint_10_81_p8 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 8 177927920694900123 = some 177927920694900123 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 6 2 177927920694900123 177927920694900123 177927920694900123 endpoint_10_81_p6 endpoint_10_81_w6
private theorem endpoint_10_81_w8 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 8 1 177927920694900123 = some 177927920694900123 := by decide +kernel
private theorem endpoint_10_81_p9 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 9 177927920694900123 = some 177927920694900123 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 8 1 177927920694900123 177927920694900123 177927920694900123 endpoint_10_81_p8 endpoint_10_81_w8
def endpoint_10_81 : CertifiedEndpoint :=
  ⟨⟨10, 81, 1634⟩, 177927920694900123, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_81_flag endpoint_10_81_sources 9 177927920694900123 177927920694900123 rfl endpoint_10_81_base endpoint_10_81_p9) (by decide)⟩
private def endpoint_10_82_flag : Flag := ⟨10, 82, 1518⟩
private def endpoint_10_82_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_82_base : receiptBase endpoint_10_82_flag endpoint_10_82_sources = some 167172134985740973 := by decide +kernel
private theorem endpoint_10_82_w0 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 2 167172134985740973 = some 167172134985740973 := by decide +kernel
private theorem endpoint_10_82_w2 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 2 2 167172134985740973 = some 167172134985740973 := by decide +kernel
private theorem endpoint_10_82_p4 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 4 167172134985740973 = some 167172134985740973 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 2 2 167172134985740973 167172134985740973 167172134985740973 endpoint_10_82_w0 endpoint_10_82_w2
private theorem endpoint_10_82_w4 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 4 2 167172134985740973 = some 167172134985740973 := by decide +kernel
private theorem endpoint_10_82_p6 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 6 167172134985740973 = some 167172134985740973 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 4 2 167172134985740973 167172134985740973 167172134985740973 endpoint_10_82_p4 endpoint_10_82_w4
private theorem endpoint_10_82_w6 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 6 2 167172134985740973 = some 167172134985740973 := by decide +kernel
private theorem endpoint_10_82_p8 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 8 167172134985740973 = some 167172134985740973 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 6 2 167172134985740973 167172134985740973 167172134985740973 endpoint_10_82_p6 endpoint_10_82_w6
private theorem endpoint_10_82_w8 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 8 1 167172134985740973 = some 167172134985740973 := by decide +kernel
private theorem endpoint_10_82_p9 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 9 167172134985740973 = some 167172134985740973 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 8 1 167172134985740973 167172134985740973 167172134985740973 endpoint_10_82_p8 endpoint_10_82_w8
def endpoint_10_82 : CertifiedEndpoint :=
  ⟨⟨10, 82, 1518⟩, 167172134985740973, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_82_flag endpoint_10_82_sources 9 167172134985740973 167172134985740973 rfl endpoint_10_82_base endpoint_10_82_p9) (by decide)⟩
def endpoint_10_83 : CertifiedEndpoint :=
  ⟨⟨10, 83, 1399⟩, 257966611832874924, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_84 : CertifiedEndpoint :=
  ⟨⟨10, 84, 1277⟩, 237668847464091167, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_85 : CertifiedEndpoint :=
  ⟨⟨10, 85, 1151⟩, 215987879778798536, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_86 : CertifiedEndpoint :=
  ⟨⟨10, 86, 1022⟩, 193092007032308622, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_87 : CertifiedEndpoint :=
  ⟨⟨10, 87, 891⟩, 169159354612047376, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_88 : CertifiedEndpoint :=
  ⟨⟨10, 88, 756⟩, 143769795384419556, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_89 : CertifiedEndpoint :=
  ⟨⟨10, 89, 617⟩, 116893847953082082, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_90 : CertifiedEndpoint :=
  ⟨⟨10, 90, 476⟩, 88917244489229936, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_91 : CertifiedEndpoint :=
  ⟨⟨10, 91, 332⟩, 59615180727893957, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_92 : CertifiedEndpoint :=
  ⟨⟨10, 92, 184⟩, 28753025271990624, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_11 : CertifiedEndpoint :=
  ⟨⟨11, 11, 4751⟩, 81764383917727444, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_12 : CertifiedEndpoint :=
  ⟨⟨11, 12, 4729⟩, 85557743341577138, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_13 : CertifiedEndpoint :=
  ⟨⟨11, 13, 4707⟩, 89312172192780636, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_14 : CertifiedEndpoint :=
  ⟨⟨11, 14, 4685⟩, 101574679177064393, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_15 : CertifiedEndpoint :=
  ⟨⟨11, 15, 4662⟩, 113690595223353433, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_16 : CertifiedEndpoint :=
  ⟨⟨11, 16, 4639⟩, 125678930363823899, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_17 : CertifiedEndpoint :=
  ⟨⟨11, 17, 4616⟩, 137539684598475791, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_18 : CertifiedEndpoint :=
  ⟨⟨11, 18, 4593⟩, 149272857927309109, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_19 : CertifiedEndpoint :=
  ⟨⟨11, 19, 4570⟩, 160878450350323853, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_20 : CertifiedEndpoint :=
  ⟨⟨11, 20, 4546⟩, 172318450423838986, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_21 : CertifiedEndpoint :=
  ⟨⟨11, 21, 4522⟩, 183625440616819861, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_22 : CertifiedEndpoint :=
  ⟨⟨11, 22, 4498⟩, 194799420929266478, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_23 : CertifiedEndpoint :=
  ⟨⟨11, 23, 4474⟩, 205840391361178837, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_24 : CertifiedEndpoint :=
  ⟨⟨11, 24, 4449⟩, 216699482519444533, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_25 : CertifiedEndpoint :=
  ⟨⟨11, 25, 4424⟩, 227420134822460287, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_26 : CertifiedEndpoint :=
  ⟨⟨11, 26, 4399⟩, 238002348270226099, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_27 : CertifiedEndpoint :=
  ⟨⟨11, 27, 4373⟩, 248389110007556038, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_28 : CertifiedEndpoint :=
  ⟨⟨11, 28, 4347⟩, 258632003914920351, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_11_29_flag : Flag := ⟨11, 29, 4321⟩
private def endpoint_11_29_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_29_base : receiptBase endpoint_11_29_flag endpoint_11_29_sources = some 183857794803878915 := by decide +kernel
private theorem endpoint_11_29_w0 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 0 2 183857794803878915 = some 183857794803878915 := by decide +kernel
private theorem endpoint_11_29_w2 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 2 2 183857794803878915 = some 183857794803878915 := by decide +kernel
private theorem endpoint_11_29_p4 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 0 4 183857794803878915 = some 183857794803878915 :=
  join_receipt_window endpoint_11_29_flag endpoint_11_29_sources 0 2 2 183857794803878915 183857794803878915 183857794803878915 endpoint_11_29_w0 endpoint_11_29_w2
private theorem endpoint_11_29_w4 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 4 2 183857794803878915 = some 183857794803878915 := by decide +kernel
private theorem endpoint_11_29_p6 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 0 6 183857794803878915 = some 183857794803878915 :=
  join_receipt_window endpoint_11_29_flag endpoint_11_29_sources 0 4 2 183857794803878915 183857794803878915 183857794803878915 endpoint_11_29_p4 endpoint_11_29_w4
private theorem endpoint_11_29_w6 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 6 2 183857794803878915 = some 183857794803878915 := by decide +kernel
private theorem endpoint_11_29_p8 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 0 8 183857794803878915 = some 183857794803878915 :=
  join_receipt_window endpoint_11_29_flag endpoint_11_29_sources 0 6 2 183857794803878915 183857794803878915 183857794803878915 endpoint_11_29_p6 endpoint_11_29_w6
private theorem endpoint_11_29_w8 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 8 2 183857794803878915 = some 183857794803878915 := by decide +kernel
private theorem endpoint_11_29_p10 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 0 10 183857794803878915 = some 183857794803878915 :=
  join_receipt_window endpoint_11_29_flag endpoint_11_29_sources 0 8 2 183857794803878915 183857794803878915 183857794803878915 endpoint_11_29_p8 endpoint_11_29_w8
def endpoint_11_29 : CertifiedEndpoint :=
  ⟨⟨11, 29, 4321⟩, 183857794803878915, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_29_flag endpoint_11_29_sources 10 183857794803878915 183857794803878915 rfl endpoint_11_29_base endpoint_11_29_p10) (by decide)⟩
private def endpoint_11_30_flag : Flag := ⟨11, 30, 4294⟩
private def endpoint_11_30_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_30_base : receiptBase endpoint_11_30_flag endpoint_11_30_sources = some 187764112099022409 := by decide +kernel
private theorem endpoint_11_30_w0 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 0 2 187764112099022409 = some 187764112099022409 := by decide +kernel
private theorem endpoint_11_30_w2 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 2 2 187764112099022409 = some 187764112099022409 := by decide +kernel
private theorem endpoint_11_30_p4 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 0 4 187764112099022409 = some 187764112099022409 :=
  join_receipt_window endpoint_11_30_flag endpoint_11_30_sources 0 2 2 187764112099022409 187764112099022409 187764112099022409 endpoint_11_30_w0 endpoint_11_30_w2
private theorem endpoint_11_30_w4 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 4 2 187764112099022409 = some 187764112099022409 := by decide +kernel
private theorem endpoint_11_30_p6 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 0 6 187764112099022409 = some 187764112099022409 :=
  join_receipt_window endpoint_11_30_flag endpoint_11_30_sources 0 4 2 187764112099022409 187764112099022409 187764112099022409 endpoint_11_30_p4 endpoint_11_30_w4
private theorem endpoint_11_30_w6 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 6 2 187764112099022409 = some 187764112099022409 := by decide +kernel
private theorem endpoint_11_30_p8 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 0 8 187764112099022409 = some 187764112099022409 :=
  join_receipt_window endpoint_11_30_flag endpoint_11_30_sources 0 6 2 187764112099022409 187764112099022409 187764112099022409 endpoint_11_30_p6 endpoint_11_30_w6
private theorem endpoint_11_30_w8 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 8 2 187764112099022409 = some 187764112099022409 := by decide +kernel
private theorem endpoint_11_30_p10 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 0 10 187764112099022409 = some 187764112099022409 :=
  join_receipt_window endpoint_11_30_flag endpoint_11_30_sources 0 8 2 187764112099022409 187764112099022409 187764112099022409 endpoint_11_30_p8 endpoint_11_30_w8
def endpoint_11_30 : CertifiedEndpoint :=
  ⟨⟨11, 30, 4294⟩, 187764112099022409, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_30_flag endpoint_11_30_sources 10 187764112099022409 187764112099022409 rfl endpoint_11_30_base endpoint_11_30_p10) (by decide)⟩
private def endpoint_11_31_flag : Flag := ⟨11, 31, 4267⟩
private def endpoint_11_31_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_31_base : receiptBase endpoint_11_31_flag endpoint_11_31_sources = some 191607040505564831 := by decide +kernel
private theorem endpoint_11_31_w0 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 2 191607040505564831 = some 191607040505564831 := by decide +kernel
private theorem endpoint_11_31_w2 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 2 2 191607040505564831 = some 191607040505564831 := by decide +kernel
private theorem endpoint_11_31_p4 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 4 191607040505564831 = some 191607040505564831 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 2 2 191607040505564831 191607040505564831 191607040505564831 endpoint_11_31_w0 endpoint_11_31_w2
private theorem endpoint_11_31_w4 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 4 2 191607040505564831 = some 191607040505564831 := by decide +kernel
private theorem endpoint_11_31_p6 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 6 191607040505564831 = some 191607040505564831 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 4 2 191607040505564831 191607040505564831 191607040505564831 endpoint_11_31_p4 endpoint_11_31_w4
private theorem endpoint_11_31_w6 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 6 2 191607040505564831 = some 191607040505564831 := by decide +kernel
private theorem endpoint_11_31_p8 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 8 191607040505564831 = some 191607040505564831 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 6 2 191607040505564831 191607040505564831 191607040505564831 endpoint_11_31_p6 endpoint_11_31_w6
private theorem endpoint_11_31_w8 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 8 2 191607040505564831 = some 191607040505564831 := by decide +kernel
private theorem endpoint_11_31_p10 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 10 191607040505564831 = some 191607040505564831 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 8 2 191607040505564831 191607040505564831 191607040505564831 endpoint_11_31_p8 endpoint_11_31_w8
def endpoint_11_31 : CertifiedEndpoint :=
  ⟨⟨11, 31, 4267⟩, 191607040505564831, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_31_flag endpoint_11_31_sources 10 191607040505564831 191607040505564831 rfl endpoint_11_31_base endpoint_11_31_p10) (by decide)⟩
private def endpoint_11_32_flag : Flag := ⟨11, 32, 4240⟩
private def endpoint_11_32_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_32_base : receiptBase endpoint_11_32_flag endpoint_11_32_sources = some 195386580023506182 := by decide +kernel
private theorem endpoint_11_32_w0 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 2 195386580023506182 = some 195386580023506182 := by decide +kernel
private theorem endpoint_11_32_w2 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 2 2 195386580023506182 = some 195386580023506182 := by decide +kernel
private theorem endpoint_11_32_p4 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 4 195386580023506182 = some 195386580023506182 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 2 2 195386580023506182 195386580023506182 195386580023506182 endpoint_11_32_w0 endpoint_11_32_w2
private theorem endpoint_11_32_w4 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 4 2 195386580023506182 = some 195386580023506182 := by decide +kernel
private theorem endpoint_11_32_p6 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 6 195386580023506182 = some 195386580023506182 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 4 2 195386580023506182 195386580023506182 195386580023506182 endpoint_11_32_p4 endpoint_11_32_w4
private theorem endpoint_11_32_w6 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 6 2 195386580023506182 = some 195386580023506182 := by decide +kernel
private theorem endpoint_11_32_p8 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 8 195386580023506182 = some 195386580023506182 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 6 2 195386580023506182 195386580023506182 195386580023506182 endpoint_11_32_p6 endpoint_11_32_w6
private theorem endpoint_11_32_w8 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 8 2 195386580023506182 = some 195386580023506182 := by decide +kernel
private theorem endpoint_11_32_p10 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 10 195386580023506182 = some 195386580023506182 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 8 2 195386580023506182 195386580023506182 195386580023506182 endpoint_11_32_p8 endpoint_11_32_w8
def endpoint_11_32 : CertifiedEndpoint :=
  ⟨⟨11, 32, 4240⟩, 195386580023506182, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_32_flag endpoint_11_32_sources 10 195386580023506182 195386580023506182 rfl endpoint_11_32_base endpoint_11_32_p10) (by decide)⟩
private def endpoint_11_33_flag : Flag := ⟨11, 33, 4212⟩
private def endpoint_11_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_33_base : receiptBase endpoint_11_33_flag endpoint_11_33_sources = some 199056110073967586 := by decide +kernel
private theorem endpoint_11_33_w0 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 2 199056110073967586 = some 199056110073967586 := by decide +kernel
private theorem endpoint_11_33_w2 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 2 2 199056110073967586 = some 199056110073967586 := by decide +kernel
private theorem endpoint_11_33_p4 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 4 199056110073967586 = some 199056110073967586 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 2 2 199056110073967586 199056110073967586 199056110073967586 endpoint_11_33_w0 endpoint_11_33_w2
private theorem endpoint_11_33_w4 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 4 2 199056110073967586 = some 199056110073967586 := by decide +kernel
private theorem endpoint_11_33_p6 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 6 199056110073967586 = some 199056110073967586 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 4 2 199056110073967586 199056110073967586 199056110073967586 endpoint_11_33_p4 endpoint_11_33_w4
private theorem endpoint_11_33_w6 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 6 2 199056110073967586 = some 199056110073967586 := by decide +kernel
private theorem endpoint_11_33_p8 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 8 199056110073967586 = some 199056110073967586 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 6 2 199056110073967586 199056110073967586 199056110073967586 endpoint_11_33_p6 endpoint_11_33_w6
private theorem endpoint_11_33_w8 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 8 2 199056110073967586 = some 199056110073967586 := by decide +kernel
private theorem endpoint_11_33_p10 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 10 199056110073967586 = some 199056110073967586 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 8 2 199056110073967586 199056110073967586 199056110073967586 endpoint_11_33_p8 endpoint_11_33_w8
def endpoint_11_33 : CertifiedEndpoint :=
  ⟨⟨11, 33, 4212⟩, 199056110073967586, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_33_flag endpoint_11_33_sources 10 199056110073967586 199056110073967586 rfl endpoint_11_33_base endpoint_11_33_p10) (by decide)⟩
private def endpoint_11_34_flag : Flag := ⟨11, 34, 4184⟩
private def endpoint_11_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_34_base : receiptBase endpoint_11_34_flag endpoint_11_34_sources = some 202659946348955334 := by decide +kernel
private theorem endpoint_11_34_w0 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 2 202659946348955334 = some 202659946348955334 := by decide +kernel
private theorem endpoint_11_34_w2 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 2 2 202659946348955334 = some 202659946348955334 := by decide +kernel
private theorem endpoint_11_34_p4 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 4 202659946348955334 = some 202659946348955334 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 2 2 202659946348955334 202659946348955334 202659946348955334 endpoint_11_34_w0 endpoint_11_34_w2
private theorem endpoint_11_34_w4 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 4 2 202659946348955334 = some 202659946348955334 := by decide +kernel
private theorem endpoint_11_34_p6 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 6 202659946348955334 = some 202659946348955334 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 4 2 202659946348955334 202659946348955334 202659946348955334 endpoint_11_34_p4 endpoint_11_34_w4
private theorem endpoint_11_34_w6 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 6 2 202659946348955334 = some 202659946348955334 := by decide +kernel
private theorem endpoint_11_34_p8 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 8 202659946348955334 = some 202659946348955334 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 6 2 202659946348955334 202659946348955334 202659946348955334 endpoint_11_34_p6 endpoint_11_34_w6
private theorem endpoint_11_34_w8 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 8 2 202659946348955334 = some 202659946348955334 := by decide +kernel
private theorem endpoint_11_34_p10 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 10 202659946348955334 = some 202659946348955334 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 8 2 202659946348955334 202659946348955334 202659946348955334 endpoint_11_34_p8 endpoint_11_34_w8
def endpoint_11_34 : CertifiedEndpoint :=
  ⟨⟨11, 34, 4184⟩, 202659946348955334, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_34_flag endpoint_11_34_sources 10 202659946348955334 202659946348955334 rfl endpoint_11_34_base endpoint_11_34_p10) (by decide)⟩
private def endpoint_11_35_flag : Flag := ⟨11, 35, 4156⟩
private def endpoint_11_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_35_base : receiptBase endpoint_11_35_flag endpoint_11_35_sources = some 206198088848469427 := by decide +kernel
private theorem endpoint_11_35_w0 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 2 206198088848469427 = some 206198088848469427 := by decide +kernel
private theorem endpoint_11_35_w2 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 2 2 206198088848469427 = some 206198088848469427 := by decide +kernel
private theorem endpoint_11_35_p4 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 4 206198088848469427 = some 206198088848469427 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 2 2 206198088848469427 206198088848469427 206198088848469427 endpoint_11_35_w0 endpoint_11_35_w2
private theorem endpoint_11_35_w4 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 4 2 206198088848469427 = some 206198088848469427 := by decide +kernel
private theorem endpoint_11_35_p6 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 6 206198088848469427 = some 206198088848469427 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 4 2 206198088848469427 206198088848469427 206198088848469427 endpoint_11_35_p4 endpoint_11_35_w4
private theorem endpoint_11_35_w6 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 6 2 206198088848469427 = some 206198088848469427 := by decide +kernel
private theorem endpoint_11_35_p8 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 8 206198088848469427 = some 206198088848469427 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 6 2 206198088848469427 206198088848469427 206198088848469427 endpoint_11_35_p6 endpoint_11_35_w6
private theorem endpoint_11_35_w8 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 8 2 206198088848469427 = some 206198088848469427 := by decide +kernel
private theorem endpoint_11_35_p10 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 10 206198088848469427 = some 206198088848469427 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 8 2 206198088848469427 206198088848469427 206198088848469427 endpoint_11_35_p8 endpoint_11_35_w8
def endpoint_11_35 : CertifiedEndpoint :=
  ⟨⟨11, 35, 4156⟩, 206198088848469427, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_35_flag endpoint_11_35_sources 10 206198088848469427 206198088848469427 rfl endpoint_11_35_base endpoint_11_35_p10) (by decide)⟩
private def endpoint_11_36_flag : Flag := ⟨11, 36, 4127⟩
private def endpoint_11_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_36_base : receiptBase endpoint_11_36_flag endpoint_11_36_sources = some 209620459663322113 := by decide +kernel
private theorem endpoint_11_36_w0 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 2 209620459663322113 = some 209620459663322113 := by decide +kernel
private theorem endpoint_11_36_w2 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 2 2 209620459663322113 = some 209620459663322113 := by decide +kernel
private theorem endpoint_11_36_p4 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 4 209620459663322113 = some 209620459663322113 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 2 2 209620459663322113 209620459663322113 209620459663322113 endpoint_11_36_w0 endpoint_11_36_w2
private theorem endpoint_11_36_w4 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 4 2 209620459663322113 = some 209620459663322113 := by decide +kernel
private theorem endpoint_11_36_p6 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 6 209620459663322113 = some 209620459663322113 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 4 2 209620459663322113 209620459663322113 209620459663322113 endpoint_11_36_p4 endpoint_11_36_w4
private theorem endpoint_11_36_w6 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 6 2 209620459663322113 = some 209620459663322113 := by decide +kernel
private theorem endpoint_11_36_p8 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 8 209620459663322113 = some 209620459663322113 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 6 2 209620459663322113 209620459663322113 209620459663322113 endpoint_11_36_p6 endpoint_11_36_w6
private theorem endpoint_11_36_w8 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 8 2 209620459663322113 = some 209620459663322113 := by decide +kernel
private theorem endpoint_11_36_p10 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 10 209620459663322113 = some 209620459663322113 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 8 2 209620459663322113 209620459663322113 209620459663322113 endpoint_11_36_p8 endpoint_11_36_w8
def endpoint_11_36 : CertifiedEndpoint :=
  ⟨⟨11, 36, 4127⟩, 209620459663322113, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_36_flag endpoint_11_36_sources 10 209620459663322113 209620459663322113 rfl endpoint_11_36_base endpoint_11_36_p10) (by decide)⟩
private def endpoint_11_37_flag : Flag := ⟨11, 37, 4097⟩
private def endpoint_11_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_37_base : receiptBase endpoint_11_37_flag endpoint_11_37_sources = some 212923601463204515 := by decide +kernel
private theorem endpoint_11_37_w0 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 2 212923601463204515 = some 212923601463204515 := by decide +kernel
private theorem endpoint_11_37_w2 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 2 2 212923601463204515 = some 212923601463204515 := by decide +kernel
private theorem endpoint_11_37_p4 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 4 212923601463204515 = some 212923601463204515 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 2 2 212923601463204515 212923601463204515 212923601463204515 endpoint_11_37_w0 endpoint_11_37_w2
private theorem endpoint_11_37_w4 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 4 2 212923601463204515 = some 212923601463204515 := by decide +kernel
private theorem endpoint_11_37_p6 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 6 212923601463204515 = some 212923601463204515 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 4 2 212923601463204515 212923601463204515 212923601463204515 endpoint_11_37_p4 endpoint_11_37_w4
private theorem endpoint_11_37_w6 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 6 2 212923601463204515 = some 212923601463204515 := by decide +kernel
private theorem endpoint_11_37_p8 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 8 212923601463204515 = some 212923601463204515 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 6 2 212923601463204515 212923601463204515 212923601463204515 endpoint_11_37_p6 endpoint_11_37_w6
private theorem endpoint_11_37_w8 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 8 2 212923601463204515 = some 212923601463204515 := by decide +kernel
private theorem endpoint_11_37_p10 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 10 212923601463204515 = some 212923601463204515 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 8 2 212923601463204515 212923601463204515 212923601463204515 endpoint_11_37_p8 endpoint_11_37_w8
def endpoint_11_37 : CertifiedEndpoint :=
  ⟨⟨11, 37, 4097⟩, 212923601463204515, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_37_flag endpoint_11_37_sources 10 212923601463204515 212923601463204515 rfl endpoint_11_37_base endpoint_11_37_p10) (by decide)⟩
private def endpoint_11_38_flag : Flag := ⟨11, 38, 4067⟩
private def endpoint_11_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_38_base : receiptBase endpoint_11_38_flag endpoint_11_38_sources = some 216156439713868096 := by decide +kernel
private theorem endpoint_11_38_w0 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 2 216156439713868096 = some 216156439713868096 := by decide +kernel
private theorem endpoint_11_38_w2 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 2 2 216156439713868096 = some 216156439713868096 := by decide +kernel
private theorem endpoint_11_38_p4 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 4 216156439713868096 = some 216156439713868096 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 2 2 216156439713868096 216156439713868096 216156439713868096 endpoint_11_38_w0 endpoint_11_38_w2
private theorem endpoint_11_38_w4 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 4 2 216156439713868096 = some 216156439713868096 := by decide +kernel
private theorem endpoint_11_38_p6 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 6 216156439713868096 = some 216156439713868096 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 4 2 216156439713868096 216156439713868096 216156439713868096 endpoint_11_38_p4 endpoint_11_38_w4
private theorem endpoint_11_38_w6 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 6 2 216156439713868096 = some 216156439713868096 := by decide +kernel
private theorem endpoint_11_38_p8 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 8 216156439713868096 = some 216156439713868096 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 6 2 216156439713868096 216156439713868096 216156439713868096 endpoint_11_38_p6 endpoint_11_38_w6
private theorem endpoint_11_38_w8 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 8 2 216156439713868096 = some 216156439713868096 := by decide +kernel
private theorem endpoint_11_38_p10 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 10 216156439713868096 = some 216156439713868096 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 8 2 216156439713868096 216156439713868096 216156439713868096 endpoint_11_38_p8 endpoint_11_38_w8
def endpoint_11_38 : CertifiedEndpoint :=
  ⟨⟨11, 38, 4067⟩, 216156439713868096, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_38_flag endpoint_11_38_sources 10 216156439713868096 216156439713868096 rfl endpoint_11_38_base endpoint_11_38_p10) (by decide)⟩
private def endpoint_11_39_flag : Flag := ⟨11, 39, 4037⟩
private def endpoint_11_39_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_39_base : receiptBase endpoint_11_39_flag endpoint_11_39_sources = some 219318974415312853 := by decide +kernel
private theorem endpoint_11_39_w0 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 2 219318974415312853 = some 219318974415312853 := by decide +kernel
private theorem endpoint_11_39_w2 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 2 2 219318974415312853 = some 219318974415312853 := by decide +kernel
private theorem endpoint_11_39_p4 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 4 219318974415312853 = some 219318974415312853 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 2 2 219318974415312853 219318974415312853 219318974415312853 endpoint_11_39_w0 endpoint_11_39_w2
private theorem endpoint_11_39_w4 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 4 2 219318974415312853 = some 219318974415312853 := by decide +kernel
private theorem endpoint_11_39_p6 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 6 219318974415312853 = some 219318974415312853 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 4 2 219318974415312853 219318974415312853 219318974415312853 endpoint_11_39_p4 endpoint_11_39_w4
private theorem endpoint_11_39_w6 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 6 2 219318974415312853 = some 219318974415312853 := by decide +kernel
private theorem endpoint_11_39_p8 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 8 219318974415312853 = some 219318974415312853 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 6 2 219318974415312853 219318974415312853 219318974415312853 endpoint_11_39_p6 endpoint_11_39_w6
private theorem endpoint_11_39_w8 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 8 2 219318974415312853 = some 219318974415312853 := by decide +kernel
private theorem endpoint_11_39_p10 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 10 219318974415312853 = some 219318974415312853 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 8 2 219318974415312853 219318974415312853 219318974415312853 endpoint_11_39_p8 endpoint_11_39_w8
def endpoint_11_39 : CertifiedEndpoint :=
  ⟨⟨11, 39, 4037⟩, 219318974415312853, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_39_flag endpoint_11_39_sources 10 219318974415312853 219318974415312853 rfl endpoint_11_39_base endpoint_11_39_p10) (by decide)⟩
private def endpoint_11_40_flag : Flag := ⟨11, 40, 4006⟩
private def endpoint_11_40_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_40_base : receiptBase endpoint_11_40_flag endpoint_11_40_sources = some 222356517884605868 := by decide +kernel
private theorem endpoint_11_40_w0 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 2 222356517884605868 = some 222356517884605868 := by decide +kernel
private theorem endpoint_11_40_w2 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 2 2 222356517884605868 = some 222356517884605868 := by decide +kernel
private theorem endpoint_11_40_p4 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 4 222356517884605868 = some 222356517884605868 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 2 2 222356517884605868 222356517884605868 222356517884605868 endpoint_11_40_w0 endpoint_11_40_w2
private theorem endpoint_11_40_w4 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 4 2 222356517884605868 = some 222356517884605868 := by decide +kernel
private theorem endpoint_11_40_p6 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 6 222356517884605868 = some 222356517884605868 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 4 2 222356517884605868 222356517884605868 222356517884605868 endpoint_11_40_p4 endpoint_11_40_w4
private theorem endpoint_11_40_w6 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 6 2 222356517884605868 = some 222356517884605868 := by decide +kernel
private theorem endpoint_11_40_p8 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 8 222356517884605868 = some 222356517884605868 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 6 2 222356517884605868 222356517884605868 222356517884605868 endpoint_11_40_p6 endpoint_11_40_w6
private theorem endpoint_11_40_w8 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 8 2 222356517884605868 = some 222356517884605868 := by decide +kernel
private theorem endpoint_11_40_p10 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 10 222356517884605868 = some 222356517884605868 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 8 2 222356517884605868 222356517884605868 222356517884605868 endpoint_11_40_p8 endpoint_11_40_w8
def endpoint_11_40 : CertifiedEndpoint :=
  ⟨⟨11, 40, 4006⟩, 222356517884605868, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_40_flag endpoint_11_40_sources 10 222356517884605868 222356517884605868 rfl endpoint_11_40_base endpoint_11_40_p10) (by decide)⟩
private def endpoint_11_41_flag : Flag := ⟨11, 41, 3975⟩
private def endpoint_11_41_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_41_base : receiptBase endpoint_11_41_flag endpoint_11_41_sources = some 225321452917807476 := by decide +kernel
private theorem endpoint_11_41_w0 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 2 225321452917807476 = some 225321452917807476 := by decide +kernel
private theorem endpoint_11_41_w2 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 2 2 225321452917807476 = some 225321452917807476 := by decide +kernel
private theorem endpoint_11_41_p4 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 4 225321452917807476 = some 225321452917807476 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 2 2 225321452917807476 225321452917807476 225321452917807476 endpoint_11_41_w0 endpoint_11_41_w2
private theorem endpoint_11_41_w4 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 4 2 225321452917807476 = some 225321452917807476 := by decide +kernel
private theorem endpoint_11_41_p6 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 6 225321452917807476 = some 225321452917807476 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 4 2 225321452917807476 225321452917807476 225321452917807476 endpoint_11_41_p4 endpoint_11_41_w4
private theorem endpoint_11_41_w6 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 6 2 225321452917807476 = some 225321452917807476 := by decide +kernel
private theorem endpoint_11_41_p8 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 8 225321452917807476 = some 225321452917807476 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 6 2 225321452917807476 225321452917807476 225321452917807476 endpoint_11_41_p6 endpoint_11_41_w6
private theorem endpoint_11_41_w8 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 8 2 225321452917807476 = some 225321452917807476 := by decide +kernel
private theorem endpoint_11_41_p10 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 10 225321452917807476 = some 225321452917807476 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 8 2 225321452917807476 225321452917807476 225321452917807476 endpoint_11_41_p8 endpoint_11_41_w8
def endpoint_11_41 : CertifiedEndpoint :=
  ⟨⟨11, 41, 3975⟩, 225321452917807476, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_41_flag endpoint_11_41_sources 10 225321452917807476 225321452917807476 rfl endpoint_11_41_base endpoint_11_41_p10) (by decide)⟩
private def endpoint_11_42_flag : Flag := ⟨11, 42, 3943⟩
private def endpoint_11_42_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_42_base : receiptBase endpoint_11_42_flag endpoint_11_42_sources = some 228156786945112175 := by decide +kernel
private theorem endpoint_11_42_w0 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 2 228156786945112175 = some 228156786945112175 := by decide +kernel
private theorem endpoint_11_42_w2 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 2 2 228156786945112175 = some 228156786945112175 := by decide +kernel
private theorem endpoint_11_42_p4 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 4 228156786945112175 = some 228156786945112175 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 2 2 228156786945112175 228156786945112175 228156786945112175 endpoint_11_42_w0 endpoint_11_42_w2
private theorem endpoint_11_42_w4 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 4 2 228156786945112175 = some 228156786945112175 := by decide +kernel
private theorem endpoint_11_42_p6 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 6 228156786945112175 = some 228156786945112175 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 4 2 228156786945112175 228156786945112175 228156786945112175 endpoint_11_42_p4 endpoint_11_42_w4
private theorem endpoint_11_42_w6 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 6 2 228156786945112175 = some 228156786945112175 := by decide +kernel
private theorem endpoint_11_42_p8 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 8 228156786945112175 = some 228156786945112175 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 6 2 228156786945112175 228156786945112175 228156786945112175 endpoint_11_42_p6 endpoint_11_42_w6
private theorem endpoint_11_42_w8 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 8 2 228156786945112175 = some 228156786945112175 := by decide +kernel
private theorem endpoint_11_42_p10 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 10 228156786945112175 = some 228156786945112175 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 8 2 228156786945112175 228156786945112175 228156786945112175 endpoint_11_42_p8 endpoint_11_42_w8
def endpoint_11_42 : CertifiedEndpoint :=
  ⟨⟨11, 42, 3943⟩, 228156786945112175, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_42_flag endpoint_11_42_sources 10 228156786945112175 228156786945112175 rfl endpoint_11_42_base endpoint_11_42_p10) (by decide)⟩
private def endpoint_11_43_flag : Flag := ⟨11, 43, 3910⟩
private def endpoint_11_43_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_43_base : receiptBase endpoint_11_43_flag endpoint_11_43_sources = some 230859062636211087 := by decide +kernel
private theorem endpoint_11_43_w0 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 2 230859062636211087 = some 230859062636211087 := by decide +kernel
private theorem endpoint_11_43_w2 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 2 2 230859062636211087 = some 230859062636211087 := by decide +kernel
private theorem endpoint_11_43_p4 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 4 230859062636211087 = some 230859062636211087 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 2 2 230859062636211087 230859062636211087 230859062636211087 endpoint_11_43_w0 endpoint_11_43_w2
private theorem endpoint_11_43_w4 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 4 2 230859062636211087 = some 230859062636211087 := by decide +kernel
private theorem endpoint_11_43_p6 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 6 230859062636211087 = some 230859062636211087 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 4 2 230859062636211087 230859062636211087 230859062636211087 endpoint_11_43_p4 endpoint_11_43_w4
private theorem endpoint_11_43_w6 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 6 2 230859062636211087 = some 230859062636211087 := by decide +kernel
private theorem endpoint_11_43_p8 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 8 230859062636211087 = some 230859062636211087 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 6 2 230859062636211087 230859062636211087 230859062636211087 endpoint_11_43_p6 endpoint_11_43_w6
private theorem endpoint_11_43_w8 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 8 2 230859062636211087 = some 230859062636211087 := by decide +kernel
private theorem endpoint_11_43_p10 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 10 230859062636211087 = some 230859062636211087 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 8 2 230859062636211087 230859062636211087 230859062636211087 endpoint_11_43_p8 endpoint_11_43_w8
def endpoint_11_43 : CertifiedEndpoint :=
  ⟨⟨11, 43, 3910⟩, 230859062636211087, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_43_flag endpoint_11_43_sources 10 230859062636211087 230859062636211087 rfl endpoint_11_43_base endpoint_11_43_p10) (by decide)⟩
private def endpoint_11_44_flag : Flag := ⟨11, 44, 3877⟩
private def endpoint_11_44_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_44_base : receiptBase endpoint_11_44_flag endpoint_11_44_sources = some 233484120117473425 := by decide +kernel
private theorem endpoint_11_44_w0 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 2 233484120117473425 = some 233484120117473425 := by decide +kernel
private theorem endpoint_11_44_w2 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 2 2 233484120117473425 = some 233484120117473425 := by decide +kernel
private theorem endpoint_11_44_p4 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 4 233484120117473425 = some 233484120117473425 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 2 2 233484120117473425 233484120117473425 233484120117473425 endpoint_11_44_w0 endpoint_11_44_w2
private theorem endpoint_11_44_w4 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 4 2 233484120117473425 = some 233484120117473425 := by decide +kernel
private theorem endpoint_11_44_p6 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 6 233484120117473425 = some 233484120117473425 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 4 2 233484120117473425 233484120117473425 233484120117473425 endpoint_11_44_p4 endpoint_11_44_w4
private theorem endpoint_11_44_w6 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 6 2 233484120117473425 = some 233484120117473425 := by decide +kernel
private theorem endpoint_11_44_p8 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 8 233484120117473425 = some 233484120117473425 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 6 2 233484120117473425 233484120117473425 233484120117473425 endpoint_11_44_p6 endpoint_11_44_w6
private theorem endpoint_11_44_w8 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 8 2 233484120117473425 = some 233484120117473425 := by decide +kernel
private theorem endpoint_11_44_p10 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 10 233484120117473425 = some 233484120117473425 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 8 2 233484120117473425 233484120117473425 233484120117473425 endpoint_11_44_p8 endpoint_11_44_w8
def endpoint_11_44 : CertifiedEndpoint :=
  ⟨⟨11, 44, 3877⟩, 233484120117473425, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_44_flag endpoint_11_44_sources 10 233484120117473425 233484120117473425 rfl endpoint_11_44_base endpoint_11_44_p10) (by decide)⟩
private def endpoint_11_45_flag : Flag := ⟨11, 45, 3843⟩
private def endpoint_11_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_45_base : receiptBase endpoint_11_45_flag endpoint_11_45_sources = some 236588367319908364 := by decide +kernel
private theorem endpoint_11_45_w0 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 2 236588367319908364 = some 236588367319908364 := by decide +kernel
private theorem endpoint_11_45_w2 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 2 2 236588367319908364 = some 236588367319908364 := by decide +kernel
private theorem endpoint_11_45_p4 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 4 236588367319908364 = some 236588367319908364 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 2 2 236588367319908364 236588367319908364 236588367319908364 endpoint_11_45_w0 endpoint_11_45_w2
private theorem endpoint_11_45_w4 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 4 2 236588367319908364 = some 236588367319908364 := by decide +kernel
private theorem endpoint_11_45_p6 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 6 236588367319908364 = some 236588367319908364 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 4 2 236588367319908364 236588367319908364 236588367319908364 endpoint_11_45_p4 endpoint_11_45_w4
private theorem endpoint_11_45_w6 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 6 2 236588367319908364 = some 236588367319908364 := by decide +kernel
private theorem endpoint_11_45_p8 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 8 236588367319908364 = some 236588367319908364 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 6 2 236588367319908364 236588367319908364 236588367319908364 endpoint_11_45_p6 endpoint_11_45_w6
private theorem endpoint_11_45_w8 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 8 2 236588367319908364 = some 236588367319908364 := by decide +kernel
private theorem endpoint_11_45_p10 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 10 236588367319908364 = some 236588367319908364 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 8 2 236588367319908364 236588367319908364 236588367319908364 endpoint_11_45_p8 endpoint_11_45_w8
def endpoint_11_45 : CertifiedEndpoint :=
  ⟨⟨11, 45, 3843⟩, 236588367319908364, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_45_flag endpoint_11_45_sources 10 236588367319908364 236588367319908364 rfl endpoint_11_45_base endpoint_11_45_p10) (by decide)⟩

def endpointBlock07 : List CertifiedEndpoint := [
  endpoint_9_92, endpoint_9_93, endpoint_10_10, endpoint_10_11, endpoint_10_12, endpoint_10_13, endpoint_10_14,
  endpoint_10_15, endpoint_10_16, endpoint_10_17, endpoint_10_18, endpoint_10_19, endpoint_10_20, endpoint_10_21,
  endpoint_10_22, endpoint_10_23, endpoint_10_24, endpoint_10_25, endpoint_10_26, endpoint_10_27, endpoint_10_28,
  endpoint_10_29, endpoint_10_30, endpoint_10_31, endpoint_10_32, endpoint_10_33, endpoint_10_34, endpoint_10_35,
  endpoint_10_36, endpoint_10_37, endpoint_10_38, endpoint_10_39, endpoint_10_40, endpoint_10_41, endpoint_10_42,
  endpoint_10_43, endpoint_10_44, endpoint_10_45, endpoint_10_46, endpoint_10_47, endpoint_10_48, endpoint_10_49,
  endpoint_10_50, endpoint_10_51, endpoint_10_52, endpoint_10_53, endpoint_10_54, endpoint_10_55, endpoint_10_56,
  endpoint_10_57, endpoint_10_58, endpoint_10_59, endpoint_10_60, endpoint_10_61, endpoint_10_62, endpoint_10_63,
  endpoint_10_64, endpoint_10_65, endpoint_10_66, endpoint_10_67, endpoint_10_68, endpoint_10_69, endpoint_10_70,
  endpoint_10_71, endpoint_10_72, endpoint_10_73, endpoint_10_74, endpoint_10_75, endpoint_10_76, endpoint_10_77,
  endpoint_10_78, endpoint_10_79, endpoint_10_80, endpoint_10_81, endpoint_10_82, endpoint_10_83, endpoint_10_84,
  endpoint_10_85, endpoint_10_86, endpoint_10_87, endpoint_10_88, endpoint_10_89, endpoint_10_90, endpoint_10_91,
  endpoint_10_92, endpoint_11_11, endpoint_11_12, endpoint_11_13, endpoint_11_14, endpoint_11_15, endpoint_11_16,
  endpoint_11_17, endpoint_11_18, endpoint_11_19, endpoint_11_20, endpoint_11_21, endpoint_11_22, endpoint_11_23,
  endpoint_11_24, endpoint_11_25, endpoint_11_26, endpoint_11_27, endpoint_11_28, endpoint_11_29, endpoint_11_30,
  endpoint_11_31, endpoint_11_32, endpoint_11_33, endpoint_11_34, endpoint_11_35, endpoint_11_36, endpoint_11_37,
  endpoint_11_38, endpoint_11_39, endpoint_11_40, endpoint_11_41, endpoint_11_42, endpoint_11_43, endpoint_11_44,
  endpoint_11_45
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
