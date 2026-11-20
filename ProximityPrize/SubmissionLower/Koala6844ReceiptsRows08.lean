import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_11_59_flag : Flag := ⟨11, 59, 3366⟩
private def endpoint_11_59_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_59_base : receiptBase endpoint_11_59_flag endpoint_11_59_sources = some 262570828533367323 := by decide +kernel
private theorem endpoint_11_59_w0 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 2 262570828533367323 = some 262570828533367323 := by decide +kernel
private theorem endpoint_11_59_w2 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 2 2 262570828533367323 = some 262570828533367323 := by decide +kernel
private theorem endpoint_11_59_p4 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 4 262570828533367323 = some 262570828533367323 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 2 2 262570828533367323 262570828533367323 262570828533367323 endpoint_11_59_w0 endpoint_11_59_w2
private theorem endpoint_11_59_w4 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 4 2 262570828533367323 = some 262570828533367323 := by decide +kernel
private theorem endpoint_11_59_p6 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 6 262570828533367323 = some 262570828533367323 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 4 2 262570828533367323 262570828533367323 262570828533367323 endpoint_11_59_p4 endpoint_11_59_w4
private theorem endpoint_11_59_w6 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 6 2 262570828533367323 = some 262570828533367323 := by decide +kernel
private theorem endpoint_11_59_p8 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 8 262570828533367323 = some 262570828533367323 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 6 2 262570828533367323 262570828533367323 262570828533367323 endpoint_11_59_p6 endpoint_11_59_w6
private theorem endpoint_11_59_w8 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 8 2 262570828533367323 = some 262570828533367323 := by decide +kernel
private theorem endpoint_11_59_p10 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 10 262570828533367323 = some 262570828533367323 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 8 2 262570828533367323 262570828533367323 262570828533367323 endpoint_11_59_p8 endpoint_11_59_w8
def endpoint_11_59 : CertifiedEndpoint :=
  ⟨⟨11, 59, 3366⟩, 262570828533367323, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_59_flag endpoint_11_59_sources 10 262570828533367323 262570828533367323 rfl endpoint_11_59_base endpoint_11_59_p10) (by decide)⟩
private def endpoint_11_60_flag : Flag := ⟨11, 60, 3315⟩
private def endpoint_11_60_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_60_base : receiptBase endpoint_11_60_flag endpoint_11_60_sources = some 262510657029120083 := by decide +kernel
private theorem endpoint_11_60_w0 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 2 262510657029120083 = some 262510657029120083 := by decide +kernel
private theorem endpoint_11_60_w2 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 2 2 262510657029120083 = some 262510657029120083 := by decide +kernel
private theorem endpoint_11_60_p4 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 4 262510657029120083 = some 262510657029120083 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 2 2 262510657029120083 262510657029120083 262510657029120083 endpoint_11_60_w0 endpoint_11_60_w2
private theorem endpoint_11_60_w4 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 4 2 262510657029120083 = some 262510657029120083 := by decide +kernel
private theorem endpoint_11_60_p6 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 6 262510657029120083 = some 262510657029120083 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 4 2 262510657029120083 262510657029120083 262510657029120083 endpoint_11_60_p4 endpoint_11_60_w4
private theorem endpoint_11_60_w6 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 6 2 262510657029120083 = some 262510657029120083 := by decide +kernel
private theorem endpoint_11_60_p8 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 8 262510657029120083 = some 262510657029120083 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 6 2 262510657029120083 262510657029120083 262510657029120083 endpoint_11_60_p6 endpoint_11_60_w6
private theorem endpoint_11_60_w8 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 8 2 262510657029120083 = some 262510657029120083 := by decide +kernel
private theorem endpoint_11_60_p10 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 10 262510657029120083 = some 262510657029120083 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 8 2 262510657029120083 262510657029120083 262510657029120083 endpoint_11_60_p8 endpoint_11_60_w8
def endpoint_11_60 : CertifiedEndpoint :=
  ⟨⟨11, 60, 3315⟩, 262510657029120083, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_60_flag endpoint_11_60_sources 10 262510657029120083 262510657029120083 rfl endpoint_11_60_base endpoint_11_60_p10) (by decide)⟩
private def endpoint_11_61_flag : Flag := ⟨11, 61, 3262⟩
private def endpoint_11_61_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_61_base : receiptBase endpoint_11_61_flag endpoint_11_61_sources = some 262174100463392766 := by decide +kernel
private theorem endpoint_11_61_w0 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 2 262174100463392766 = some 262174100463392766 := by decide +kernel
private theorem endpoint_11_61_w2 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 2 2 262174100463392766 = some 262174100463392766 := by decide +kernel
private theorem endpoint_11_61_p4 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 4 262174100463392766 = some 262174100463392766 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 2 2 262174100463392766 262174100463392766 262174100463392766 endpoint_11_61_w0 endpoint_11_61_w2
private theorem endpoint_11_61_w4 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 4 2 262174100463392766 = some 262174100463392766 := by decide +kernel
private theorem endpoint_11_61_p6 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 6 262174100463392766 = some 262174100463392766 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 4 2 262174100463392766 262174100463392766 262174100463392766 endpoint_11_61_p4 endpoint_11_61_w4
private theorem endpoint_11_61_w6 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 6 2 262174100463392766 = some 262174100463392766 := by decide +kernel
private theorem endpoint_11_61_p8 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 8 262174100463392766 = some 262174100463392766 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 6 2 262174100463392766 262174100463392766 262174100463392766 endpoint_11_61_p6 endpoint_11_61_w6
private theorem endpoint_11_61_w8 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 8 2 262174100463392766 = some 262174100463392766 := by decide +kernel
private theorem endpoint_11_61_p10 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 10 262174100463392766 = some 262174100463392766 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 8 2 262174100463392766 262174100463392766 262174100463392766 endpoint_11_61_p8 endpoint_11_61_w8
def endpoint_11_61 : CertifiedEndpoint :=
  ⟨⟨11, 61, 3262⟩, 262174100463392766, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_61_flag endpoint_11_61_sources 10 262174100463392766 262174100463392766 rfl endpoint_11_61_base endpoint_11_61_p10) (by decide)⟩
private def endpoint_11_62_flag : Flag := ⟨11, 62, 3207⟩
private def endpoint_11_62_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_62_base : receiptBase endpoint_11_62_flag endpoint_11_62_sources = some 261554271168635978 := by decide +kernel
private theorem endpoint_11_62_w0 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 2 261554271168635978 = some 261554271168635978 := by decide +kernel
private theorem endpoint_11_62_w2 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 2 2 261554271168635978 = some 261554271168635978 := by decide +kernel
private theorem endpoint_11_62_p4 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 4 261554271168635978 = some 261554271168635978 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 2 2 261554271168635978 261554271168635978 261554271168635978 endpoint_11_62_w0 endpoint_11_62_w2
private theorem endpoint_11_62_w4 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 4 2 261554271168635978 = some 261554271168635978 := by decide +kernel
private theorem endpoint_11_62_p6 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 6 261554271168635978 = some 261554271168635978 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 4 2 261554271168635978 261554271168635978 261554271168635978 endpoint_11_62_p4 endpoint_11_62_w4
private theorem endpoint_11_62_w6 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 6 2 261554271168635978 = some 261554271168635978 := by decide +kernel
private theorem endpoint_11_62_p8 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 8 261554271168635978 = some 261554271168635978 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 6 2 261554271168635978 261554271168635978 261554271168635978 endpoint_11_62_p6 endpoint_11_62_w6
private theorem endpoint_11_62_w8 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 8 2 261554271168635978 = some 261554271168635978 := by decide +kernel
private theorem endpoint_11_62_p10 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 10 261554271168635978 = some 261554271168635978 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 8 2 261554271168635978 261554271168635978 261554271168635978 endpoint_11_62_p8 endpoint_11_62_w8
def endpoint_11_62 : CertifiedEndpoint :=
  ⟨⟨11, 62, 3207⟩, 261554271168635978, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_62_flag endpoint_11_62_sources 10 261554271168635978 261554271168635978 rfl endpoint_11_62_base endpoint_11_62_p10) (by decide)⟩
private def endpoint_11_63_flag : Flag := ⟨11, 63, 3149⟩
private def endpoint_11_63_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_63_base : receiptBase endpoint_11_63_flag endpoint_11_63_sources = some 260562912203842794 := by decide +kernel
private theorem endpoint_11_63_w0 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 2 260562912203842794 = some 260562912203842794 := by decide +kernel
private theorem endpoint_11_63_w2 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 2 2 260562912203842794 = some 260562912203842794 := by decide +kernel
private theorem endpoint_11_63_p4 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 4 260562912203842794 = some 260562912203842794 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 2 2 260562912203842794 260562912203842794 260562912203842794 endpoint_11_63_w0 endpoint_11_63_w2
private theorem endpoint_11_63_w4 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 4 2 260562912203842794 = some 260562912203842794 := by decide +kernel
private theorem endpoint_11_63_p6 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 6 260562912203842794 = some 260562912203842794 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 4 2 260562912203842794 260562912203842794 260562912203842794 endpoint_11_63_p4 endpoint_11_63_w4
private theorem endpoint_11_63_w6 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 6 2 260562912203842794 = some 260562912203842794 := by decide +kernel
private theorem endpoint_11_63_p8 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 8 260562912203842794 = some 260562912203842794 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 6 2 260562912203842794 260562912203842794 260562912203842794 endpoint_11_63_p6 endpoint_11_63_w6
private theorem endpoint_11_63_w8 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 8 2 260562912203842794 = some 260562912203842794 := by decide +kernel
private theorem endpoint_11_63_p10 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 10 260562912203842794 = some 260562912203842794 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 8 2 260562912203842794 260562912203842794 260562912203842794 endpoint_11_63_p8 endpoint_11_63_w8
def endpoint_11_63 : CertifiedEndpoint :=
  ⟨⟨11, 63, 3149⟩, 260562912203842794, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_63_flag endpoint_11_63_sources 10 260562912203842794 260562912203842794 rfl endpoint_11_63_base endpoint_11_63_p10) (by decide)⟩
private def endpoint_11_64_flag : Flag := ⟨11, 64, 3088⟩
private def endpoint_11_64_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_64_base : receiptBase endpoint_11_64_flag endpoint_11_64_sources = some 259189692067689122 := by decide +kernel
private theorem endpoint_11_64_w0 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 2 259189692067689122 = some 259189692067689122 := by decide +kernel
private theorem endpoint_11_64_w2 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 2 2 259189692067689122 = some 259189692067689122 := by decide +kernel
private theorem endpoint_11_64_p4 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 4 259189692067689122 = some 259189692067689122 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 2 2 259189692067689122 259189692067689122 259189692067689122 endpoint_11_64_w0 endpoint_11_64_w2
private theorem endpoint_11_64_w4 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 4 2 259189692067689122 = some 259189692067689122 := by decide +kernel
private theorem endpoint_11_64_p6 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 6 259189692067689122 = some 259189692067689122 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 4 2 259189692067689122 259189692067689122 259189692067689122 endpoint_11_64_p4 endpoint_11_64_w4
private theorem endpoint_11_64_w6 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 6 2 259189692067689122 = some 259189692067689122 := by decide +kernel
private theorem endpoint_11_64_p8 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 8 259189692067689122 = some 259189692067689122 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 6 2 259189692067689122 259189692067689122 259189692067689122 endpoint_11_64_p6 endpoint_11_64_w6
private theorem endpoint_11_64_w8 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 8 2 259189692067689122 = some 259189692067689122 := by decide +kernel
private theorem endpoint_11_64_p10 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 10 259189692067689122 = some 259189692067689122 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 8 2 259189692067689122 259189692067689122 259189692067689122 endpoint_11_64_p8 endpoint_11_64_w8
def endpoint_11_64 : CertifiedEndpoint :=
  ⟨⟨11, 64, 3088⟩, 259189692067689122, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_64_flag endpoint_11_64_sources 10 259189692067689122 259189692067689122 rfl endpoint_11_64_base endpoint_11_64_p10) (by decide)⟩
private def endpoint_11_65_flag : Flag := ⟨11, 65, 3024⟩
private def endpoint_11_65_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_65_base : receiptBase endpoint_11_65_flag endpoint_11_65_sources = some 260518499268858633 := by decide +kernel
private theorem endpoint_11_65_w0 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 2 260518499268858633 = some 260518499268858633 := by decide +kernel
private theorem endpoint_11_65_w2 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 2 2 260518499268858633 = some 260518499268858633 := by decide +kernel
private theorem endpoint_11_65_p4 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 4 260518499268858633 = some 260518499268858633 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 2 2 260518499268858633 260518499268858633 260518499268858633 endpoint_11_65_w0 endpoint_11_65_w2
private theorem endpoint_11_65_w4 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 4 2 260518499268858633 = some 260518499268858633 := by decide +kernel
private theorem endpoint_11_65_p6 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 6 260518499268858633 = some 260518499268858633 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 4 2 260518499268858633 260518499268858633 260518499268858633 endpoint_11_65_p4 endpoint_11_65_w4
private theorem endpoint_11_65_w6 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 6 2 260518499268858633 = some 260518499268858633 := by decide +kernel
private theorem endpoint_11_65_p8 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 8 260518499268858633 = some 260518499268858633 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 6 2 260518499268858633 260518499268858633 260518499268858633 endpoint_11_65_p6 endpoint_11_65_w6
private theorem endpoint_11_65_w8 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 8 2 260518499268858633 = some 260518499268858633 := by decide +kernel
private theorem endpoint_11_65_p10 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 10 260518499268858633 = some 260518499268858633 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 8 2 260518499268858633 260518499268858633 260518499268858633 endpoint_11_65_p8 endpoint_11_65_w8
def endpoint_11_65 : CertifiedEndpoint :=
  ⟨⟨11, 65, 3024⟩, 260518499268858633, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_65_flag endpoint_11_65_sources 10 260518499268858633 260518499268858633 rfl endpoint_11_65_base endpoint_11_65_p10) (by decide)⟩
private def endpoint_11_66_flag : Flag := ⟨11, 66, 2957⟩
private def endpoint_11_66_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_11_66_base : receiptBase endpoint_11_66_flag endpoint_11_66_sources = some 256114972198846541 := by decide +kernel
private theorem endpoint_11_66_w0 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 2 256114972198846541 = some 256114972198846541 := by decide +kernel
private theorem endpoint_11_66_w2 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 2 2 256114972198846541 = some 256114972198846541 := by decide +kernel
private theorem endpoint_11_66_p4 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 4 256114972198846541 = some 256114972198846541 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 2 2 256114972198846541 256114972198846541 256114972198846541 endpoint_11_66_w0 endpoint_11_66_w2
private theorem endpoint_11_66_w4 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 4 2 256114972198846541 = some 256114972198846541 := by decide +kernel
private theorem endpoint_11_66_p6 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 6 256114972198846541 = some 256114972198846541 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 4 2 256114972198846541 256114972198846541 256114972198846541 endpoint_11_66_p4 endpoint_11_66_w4
private theorem endpoint_11_66_w6 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 6 2 256114972198846541 = some 256114972198846541 := by decide +kernel
private theorem endpoint_11_66_p8 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 8 256114972198846541 = some 256114972198846541 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 6 2 256114972198846541 256114972198846541 256114972198846541 endpoint_11_66_p6 endpoint_11_66_w6
private theorem endpoint_11_66_w8 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 8 2 256114972198846541 = some 256114972198846541 := by decide +kernel
private theorem endpoint_11_66_p10 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 10 256114972198846541 = some 256114972198846541 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 8 2 256114972198846541 256114972198846541 256114972198846541 endpoint_11_66_p8 endpoint_11_66_w8
def endpoint_11_66 : CertifiedEndpoint :=
  ⟨⟨11, 66, 2957⟩, 256114972198846541, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_11_66_flag endpoint_11_66_sources 10 256114972198846541 256114972198846541 rfl endpoint_11_66_base endpoint_11_66_p10) (by decide)⟩
private def endpoint_11_67_flag : Flag := ⟨11, 67, 2888⟩
private def endpoint_11_67_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_67_base : receiptBase endpoint_11_67_flag endpoint_11_67_sources = some 261979587846552060 := by decide +kernel
private theorem endpoint_11_67_w0 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 2 261979587846552060 = some 261979587846552060 := by decide +kernel
private theorem endpoint_11_67_w2 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 2 2 261979587846552060 = some 261979587846552060 := by decide +kernel
private theorem endpoint_11_67_p4 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 4 261979587846552060 = some 261979587846552060 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 2 2 261979587846552060 261979587846552060 261979587846552060 endpoint_11_67_w0 endpoint_11_67_w2
private theorem endpoint_11_67_w4 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 4 2 261979587846552060 = some 261979587846552060 := by decide +kernel
private theorem endpoint_11_67_p6 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 6 261979587846552060 = some 261979587846552060 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 4 2 261979587846552060 261979587846552060 261979587846552060 endpoint_11_67_p4 endpoint_11_67_w4
private theorem endpoint_11_67_w6 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 6 2 261979587846552060 = some 261979587846552060 := by decide +kernel
private theorem endpoint_11_67_p8 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 8 261979587846552060 = some 261979587846552060 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 6 2 261979587846552060 261979587846552060 261979587846552060 endpoint_11_67_p6 endpoint_11_67_w6
private theorem endpoint_11_67_w8 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 8 2 261979587846552060 = some 261979587846552060 := by decide +kernel
private theorem endpoint_11_67_p10 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 10 261979587846552060 = some 261979587846552060 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 8 2 261979587846552060 261979587846552060 261979587846552060 endpoint_11_67_p8 endpoint_11_67_w8
def endpoint_11_67 : CertifiedEndpoint :=
  ⟨⟨11, 67, 2888⟩, 261979587846552060, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_67_flag endpoint_11_67_sources 10 261979587846552060 261979587846552060 rfl endpoint_11_67_base endpoint_11_67_p10) (by decide)⟩
private def endpoint_11_68_flag : Flag := ⟨11, 68, 2815⟩
private def endpoint_11_68_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_68_base : receiptBase endpoint_11_68_flag endpoint_11_68_sources = some 258817343974698652 := by decide +kernel
private theorem endpoint_11_68_w0 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 2 258817343974698652 = some 258817343974698652 := by decide +kernel
private theorem endpoint_11_68_w2 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 2 2 258817343974698652 = some 258817343974698652 := by decide +kernel
private theorem endpoint_11_68_p4 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 4 258817343974698652 = some 258817343974698652 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 2 2 258817343974698652 258817343974698652 258817343974698652 endpoint_11_68_w0 endpoint_11_68_w2
private theorem endpoint_11_68_w4 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 4 2 258817343974698652 = some 258817343974698652 := by decide +kernel
private theorem endpoint_11_68_p6 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 6 258817343974698652 = some 258817343974698652 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 4 2 258817343974698652 258817343974698652 258817343974698652 endpoint_11_68_p4 endpoint_11_68_w4
private theorem endpoint_11_68_w6 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 6 2 258817343974698652 = some 258817343974698652 := by decide +kernel
private theorem endpoint_11_68_p8 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 8 258817343974698652 = some 258817343974698652 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 6 2 258817343974698652 258817343974698652 258817343974698652 endpoint_11_68_p6 endpoint_11_68_w6
private theorem endpoint_11_68_w8 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 8 2 258817343974698652 = some 258817343974698652 := by decide +kernel
private theorem endpoint_11_68_p10 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 10 258817343974698652 = some 258817343974698652 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 8 2 258817343974698652 258817343974698652 258817343974698652 endpoint_11_68_p8 endpoint_11_68_w8
def endpoint_11_68 : CertifiedEndpoint :=
  ⟨⟨11, 68, 2815⟩, 258817343974698652, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_68_flag endpoint_11_68_sources 10 258817343974698652 258817343974698652 rfl endpoint_11_68_base endpoint_11_68_p10) (by decide)⟩
private def endpoint_11_69_flag : Flag := ⟨11, 69, 2740⟩
private def endpoint_11_69_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_69_base : receiptBase endpoint_11_69_flag endpoint_11_69_sources = some 255294042885647440 := by decide +kernel
private theorem endpoint_11_69_w0 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 2 255294042885647440 = some 255294042885647440 := by decide +kernel
private theorem endpoint_11_69_w2 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 2 2 255294042885647440 = some 255294042885647440 := by decide +kernel
private theorem endpoint_11_69_p4 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 4 255294042885647440 = some 255294042885647440 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 2 2 255294042885647440 255294042885647440 255294042885647440 endpoint_11_69_w0 endpoint_11_69_w2
private theorem endpoint_11_69_w4 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 4 2 255294042885647440 = some 255294042885647440 := by decide +kernel
private theorem endpoint_11_69_p6 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 6 255294042885647440 = some 255294042885647440 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 4 2 255294042885647440 255294042885647440 255294042885647440 endpoint_11_69_p4 endpoint_11_69_w4
private theorem endpoint_11_69_w6 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 6 2 255294042885647440 = some 255294042885647440 := by decide +kernel
private theorem endpoint_11_69_p8 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 8 255294042885647440 = some 255294042885647440 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 6 2 255294042885647440 255294042885647440 255294042885647440 endpoint_11_69_p6 endpoint_11_69_w6
private theorem endpoint_11_69_w8 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 8 2 255294042885647440 = some 255294042885647440 := by decide +kernel
private theorem endpoint_11_69_p10 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 10 255294042885647440 = some 255294042885647440 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 8 2 255294042885647440 255294042885647440 255294042885647440 endpoint_11_69_p8 endpoint_11_69_w8
def endpoint_11_69 : CertifiedEndpoint :=
  ⟨⟨11, 69, 2740⟩, 255294042885647440, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_69_flag endpoint_11_69_sources 10 255294042885647440 255294042885647440 rfl endpoint_11_69_base endpoint_11_69_p10) (by decide)⟩
private def endpoint_11_70_flag : Flag := ⟨11, 70, 2662⟩
private def endpoint_11_70_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_11_70_base : receiptBase endpoint_11_70_flag endpoint_11_70_sources = some 256747829287571479 := by decide +kernel
private theorem endpoint_11_70_w0 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 2 256747829287571479 = some 256747829287571479 := by decide +kernel
private theorem endpoint_11_70_w2 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 2 2 256747829287571479 = some 256747829287571479 := by decide +kernel
private theorem endpoint_11_70_p4 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 4 256747829287571479 = some 256747829287571479 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 2 2 256747829287571479 256747829287571479 256747829287571479 endpoint_11_70_w0 endpoint_11_70_w2
private theorem endpoint_11_70_w4 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 4 2 256747829287571479 = some 256747829287571479 := by decide +kernel
private theorem endpoint_11_70_p6 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 6 256747829287571479 = some 256747829287571479 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 4 2 256747829287571479 256747829287571479 256747829287571479 endpoint_11_70_p4 endpoint_11_70_w4
private theorem endpoint_11_70_w6 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 6 2 256747829287571479 = some 256747829287571479 := by decide +kernel
private theorem endpoint_11_70_p8 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 8 256747829287571479 = some 256747829287571479 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 6 2 256747829287571479 256747829287571479 256747829287571479 endpoint_11_70_p6 endpoint_11_70_w6
private theorem endpoint_11_70_w8 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 8 2 256747829287571479 = some 256747829287571479 := by decide +kernel
private theorem endpoint_11_70_p10 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 10 256747829287571479 = some 256747829287571479 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 8 2 256747829287571479 256747829287571479 256747829287571479 endpoint_11_70_p8 endpoint_11_70_w8
def endpoint_11_70 : CertifiedEndpoint :=
  ⟨⟨11, 70, 2662⟩, 256747829287571479, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_11_70_flag endpoint_11_70_sources 10 256747829287571479 256747829287571479 rfl endpoint_11_70_base endpoint_11_70_p10) (by decide)⟩
private def endpoint_11_71_flag : Flag := ⟨11, 71, 2581⟩
private def endpoint_11_71_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_11_71_base : receiptBase endpoint_11_71_flag endpoint_11_71_sources = some 252244125074918803 := by decide +kernel
private theorem endpoint_11_71_w0 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 2 252244125074918803 = some 252244125074918803 := by decide +kernel
private theorem endpoint_11_71_w2 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 2 2 252244125074918803 = some 252244125074918803 := by decide +kernel
private theorem endpoint_11_71_p4 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 4 252244125074918803 = some 252244125074918803 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 2 2 252244125074918803 252244125074918803 252244125074918803 endpoint_11_71_w0 endpoint_11_71_w2
private theorem endpoint_11_71_w4 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 4 2 252244125074918803 = some 252244125074918803 := by decide +kernel
private theorem endpoint_11_71_p6 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 6 252244125074918803 = some 252244125074918803 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 4 2 252244125074918803 252244125074918803 252244125074918803 endpoint_11_71_p4 endpoint_11_71_w4
private theorem endpoint_11_71_w6 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 6 2 252244125074918803 = some 252244125074918803 := by decide +kernel
private theorem endpoint_11_71_p8 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 8 252244125074918803 = some 252244125074918803 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 6 2 252244125074918803 252244125074918803 252244125074918803 endpoint_11_71_p6 endpoint_11_71_w6
private theorem endpoint_11_71_w8 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 8 2 252244125074918803 = some 252244125074918803 := by decide +kernel
private theorem endpoint_11_71_p10 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 10 252244125074918803 = some 252244125074918803 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 8 2 252244125074918803 252244125074918803 252244125074918803 endpoint_11_71_p8 endpoint_11_71_w8
def endpoint_11_71 : CertifiedEndpoint :=
  ⟨⟨11, 71, 2581⟩, 252244125074918803, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_11_71_flag endpoint_11_71_sources 10 252244125074918803 252244125074918803 rfl endpoint_11_71_base endpoint_11_71_p10) (by decide)⟩
private def endpoint_11_72_flag : Flag := ⟨11, 72, 2496⟩
private def endpoint_11_72_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_11_72_base : receiptBase endpoint_11_72_flag endpoint_11_72_sources = some 247156423847395834 := by decide +kernel
private theorem endpoint_11_72_w0 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 2 247156423847395834 = some 247156423847395834 := by decide +kernel
private theorem endpoint_11_72_w2 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 2 2 247156423847395834 = some 247156423847395834 := by decide +kernel
private theorem endpoint_11_72_p4 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 4 247156423847395834 = some 247156423847395834 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 2 2 247156423847395834 247156423847395834 247156423847395834 endpoint_11_72_w0 endpoint_11_72_w2
private theorem endpoint_11_72_w4 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 4 2 247156423847395834 = some 247156423847395834 := by decide +kernel
private theorem endpoint_11_72_p6 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 6 247156423847395834 = some 247156423847395834 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 4 2 247156423847395834 247156423847395834 247156423847395834 endpoint_11_72_p4 endpoint_11_72_w4
private theorem endpoint_11_72_w6 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 6 2 247156423847395834 = some 247156423847395834 := by decide +kernel
private theorem endpoint_11_72_p8 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 8 247156423847395834 = some 247156423847395834 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 6 2 247156423847395834 247156423847395834 247156423847395834 endpoint_11_72_p6 endpoint_11_72_w6
private theorem endpoint_11_72_w8 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 8 2 247156423847395834 = some 247156423847395834 := by decide +kernel
private theorem endpoint_11_72_p10 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 10 247156423847395834 = some 247156423847395834 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 8 2 247156423847395834 247156423847395834 247156423847395834 endpoint_11_72_p8 endpoint_11_72_w8
def endpoint_11_72 : CertifiedEndpoint :=
  ⟨⟨11, 72, 2496⟩, 247156423847395834, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_11_72_flag endpoint_11_72_sources 10 247156423847395834 247156423847395834 rfl endpoint_11_72_base endpoint_11_72_p10) (by decide)⟩
private def endpoint_11_73_flag : Flag := ⟨11, 73, 2409⟩
private def endpoint_11_73_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_11_73_base : receiptBase endpoint_11_73_flag endpoint_11_73_sources = some 243544327675129383 := by decide +kernel
private theorem endpoint_11_73_w0 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 2 243544327675129383 = some 243544327675129383 := by decide +kernel
private theorem endpoint_11_73_w2 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 2 2 243544327675129383 = some 243544327675129383 := by decide +kernel
private theorem endpoint_11_73_p4 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 4 243544327675129383 = some 243544327675129383 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 2 2 243544327675129383 243544327675129383 243544327675129383 endpoint_11_73_w0 endpoint_11_73_w2
private theorem endpoint_11_73_w4 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 4 2 243544327675129383 = some 243544327675129383 := by decide +kernel
private theorem endpoint_11_73_p6 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 6 243544327675129383 = some 243544327675129383 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 4 2 243544327675129383 243544327675129383 243544327675129383 endpoint_11_73_p4 endpoint_11_73_w4
private theorem endpoint_11_73_w6 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 6 2 243544327675129383 = some 243544327675129383 := by decide +kernel
private theorem endpoint_11_73_p8 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 8 243544327675129383 = some 243544327675129383 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 6 2 243544327675129383 243544327675129383 243544327675129383 endpoint_11_73_p6 endpoint_11_73_w6
private theorem endpoint_11_73_w8 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 8 2 243544327675129383 = some 243544327675129383 := by decide +kernel
private theorem endpoint_11_73_p10 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 10 243544327675129383 = some 243544327675129383 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 8 2 243544327675129383 243544327675129383 243544327675129383 endpoint_11_73_p8 endpoint_11_73_w8
def endpoint_11_73 : CertifiedEndpoint :=
  ⟨⟨11, 73, 2409⟩, 243544327675129383, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_11_73_flag endpoint_11_73_sources 10 243544327675129383 243544327675129383 rfl endpoint_11_73_base endpoint_11_73_p10) (by decide)⟩
private def endpoint_11_74_flag : Flag := ⟨11, 74, 2319⟩
private def endpoint_11_74_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_11_74_base : receiptBase endpoint_11_74_flag endpoint_11_74_sources = some 237404795904082287 := by decide +kernel
private theorem endpoint_11_74_w0 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 2 237404795904082287 = some 237404795904082287 := by decide +kernel
private theorem endpoint_11_74_w2 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 2 2 237404795904082287 = some 237404795904082287 := by decide +kernel
private theorem endpoint_11_74_p4 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 4 237404795904082287 = some 237404795904082287 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 2 2 237404795904082287 237404795904082287 237404795904082287 endpoint_11_74_w0 endpoint_11_74_w2
private theorem endpoint_11_74_w4 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 4 2 237404795904082287 = some 237404795904082287 := by decide +kernel
private theorem endpoint_11_74_p6 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 6 237404795904082287 = some 237404795904082287 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 4 2 237404795904082287 237404795904082287 237404795904082287 endpoint_11_74_p4 endpoint_11_74_w4
private theorem endpoint_11_74_w6 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 6 2 237404795904082287 = some 237404795904082287 := by decide +kernel
private theorem endpoint_11_74_p8 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 8 237404795904082287 = some 237404795904082287 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 6 2 237404795904082287 237404795904082287 237404795904082287 endpoint_11_74_p6 endpoint_11_74_w6
private theorem endpoint_11_74_w8 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 8 2 237404795904082287 = some 237404795904082287 := by decide +kernel
private theorem endpoint_11_74_p10 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 10 237404795904082287 = some 237404795904082287 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 8 2 237404795904082287 237404795904082287 237404795904082287 endpoint_11_74_p8 endpoint_11_74_w8
def endpoint_11_74 : CertifiedEndpoint :=
  ⟨⟨11, 74, 2319⟩, 237404795904082287, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_11_74_flag endpoint_11_74_sources 10 237404795904082287 237404795904082287 rfl endpoint_11_74_base endpoint_11_74_p10) (by decide)⟩
private def endpoint_11_75_flag : Flag := ⟨11, 75, 2226⟩
private def endpoint_11_75_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_11_75_base : receiptBase endpoint_11_75_flag endpoint_11_75_sources = some 232646069862873678 := by decide +kernel
private theorem endpoint_11_75_w0 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 2 232646069862873678 = some 232646069862873678 := by decide +kernel
private theorem endpoint_11_75_w2 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 2 2 232646069862873678 = some 232646069862873678 := by decide +kernel
private theorem endpoint_11_75_p4 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 4 232646069862873678 = some 232646069862873678 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 2 2 232646069862873678 232646069862873678 232646069862873678 endpoint_11_75_w0 endpoint_11_75_w2
private theorem endpoint_11_75_w4 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 4 2 232646069862873678 = some 232646069862873678 := by decide +kernel
private theorem endpoint_11_75_p6 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 6 232646069862873678 = some 232646069862873678 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 4 2 232646069862873678 232646069862873678 232646069862873678 endpoint_11_75_p4 endpoint_11_75_w4
private theorem endpoint_11_75_w6 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 6 2 232646069862873678 = some 232646069862873678 := by decide +kernel
private theorem endpoint_11_75_p8 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 8 232646069862873678 = some 232646069862873678 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 6 2 232646069862873678 232646069862873678 232646069862873678 endpoint_11_75_p6 endpoint_11_75_w6
private theorem endpoint_11_75_w8 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 8 2 232646069862873678 = some 232646069862873678 := by decide +kernel
private theorem endpoint_11_75_p10 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 10 232646069862873678 = some 232646069862873678 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 8 2 232646069862873678 232646069862873678 232646069862873678 endpoint_11_75_p8 endpoint_11_75_w8
def endpoint_11_75 : CertifiedEndpoint :=
  ⟨⟨11, 75, 2226⟩, 232646069862873678, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_11_75_flag endpoint_11_75_sources 10 232646069862873678 232646069862873678 rfl endpoint_11_75_base endpoint_11_75_p10) (by decide)⟩
private def endpoint_11_76_flag : Flag := ⟨11, 76, 2129⟩
private def endpoint_11_76_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_11_76_base : receiptBase endpoint_11_76_flag endpoint_11_76_sources = some 225267972427250906 := by decide +kernel
private theorem endpoint_11_76_w0 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 2 225267972427250906 = some 225267972427250906 := by decide +kernel
private theorem endpoint_11_76_w2 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 2 2 225267972427250906 = some 225267972427250906 := by decide +kernel
private theorem endpoint_11_76_p4 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 4 225267972427250906 = some 225267972427250906 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 2 2 225267972427250906 225267972427250906 225267972427250906 endpoint_11_76_w0 endpoint_11_76_w2
private theorem endpoint_11_76_w4 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 4 2 225267972427250906 = some 225267972427250906 := by decide +kernel
private theorem endpoint_11_76_p6 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 6 225267972427250906 = some 225267972427250906 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 4 2 225267972427250906 225267972427250906 225267972427250906 endpoint_11_76_p4 endpoint_11_76_w4
private theorem endpoint_11_76_w6 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 6 2 225267972427250906 = some 225267972427250906 := by decide +kernel
private theorem endpoint_11_76_p8 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 8 225267972427250906 = some 225267972427250906 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 6 2 225267972427250906 225267972427250906 225267972427250906 endpoint_11_76_p6 endpoint_11_76_w6
private theorem endpoint_11_76_w8 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 8 2 225267972427250906 = some 225267972427250906 := by decide +kernel
private theorem endpoint_11_76_p10 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 10 225267972427250906 = some 225267972427250906 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 8 2 225267972427250906 225267972427250906 225267972427250906 endpoint_11_76_p8 endpoint_11_76_w8
def endpoint_11_76 : CertifiedEndpoint :=
  ⟨⟨11, 76, 2129⟩, 225267972427250906, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_11_76_flag endpoint_11_76_sources 10 225267972427250906 225267972427250906 rfl endpoint_11_76_base endpoint_11_76_p10) (by decide)⟩
private def endpoint_11_77_flag : Flag := ⟨11, 77, 2030⟩
private def endpoint_11_77_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_11_77_base : receiptBase endpoint_11_77_flag endpoint_11_77_sources = some 219330768490025377 := by decide +kernel
private theorem endpoint_11_77_w0 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 2 219330768490025377 = some 219330768490025377 := by decide +kernel
private theorem endpoint_11_77_w2 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 2 2 219330768490025377 = some 219330768490025377 := by decide +kernel
private theorem endpoint_11_77_p4 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 4 219330768490025377 = some 219330768490025377 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 2 2 219330768490025377 219330768490025377 219330768490025377 endpoint_11_77_w0 endpoint_11_77_w2
private theorem endpoint_11_77_w4 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 4 2 219330768490025377 = some 219330768490025377 := by decide +kernel
private theorem endpoint_11_77_p6 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 6 219330768490025377 = some 219330768490025377 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 4 2 219330768490025377 219330768490025377 219330768490025377 endpoint_11_77_p4 endpoint_11_77_w4
private theorem endpoint_11_77_w6 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 6 2 219330768490025377 = some 219330768490025377 := by decide +kernel
private theorem endpoint_11_77_p8 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 8 219330768490025377 = some 219330768490025377 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 6 2 219330768490025377 219330768490025377 219330768490025377 endpoint_11_77_p6 endpoint_11_77_w6
private theorem endpoint_11_77_w8 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 8 2 219330768490025377 = some 219330768490025377 := by decide +kernel
private theorem endpoint_11_77_p10 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 10 219330768490025377 = some 219330768490025377 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 8 2 219330768490025377 219330768490025377 219330768490025377 endpoint_11_77_p8 endpoint_11_77_w8
def endpoint_11_77 : CertifiedEndpoint :=
  ⟨⟨11, 77, 2030⟩, 219330768490025377, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_11_77_flag endpoint_11_77_sources 10 219330768490025377 219330768490025377 rfl endpoint_11_77_base endpoint_11_77_p10) (by decide)⟩
private def endpoint_11_78_flag : Flag := ⟨11, 78, 1928⟩
private def endpoint_11_78_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_11_78_base : receiptBase endpoint_11_78_flag endpoint_11_78_sources = some 210820411559308064 := by decide +kernel
private theorem endpoint_11_78_w0 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 2 210820411559308064 = some 210820411559308064 := by decide +kernel
private theorem endpoint_11_78_w2 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 2 2 210820411559308064 = some 210820411559308064 := by decide +kernel
private theorem endpoint_11_78_p4 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 4 210820411559308064 = some 210820411559308064 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 2 2 210820411559308064 210820411559308064 210820411559308064 endpoint_11_78_w0 endpoint_11_78_w2
private theorem endpoint_11_78_w4 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 4 2 210820411559308064 = some 210820411559308064 := by decide +kernel
private theorem endpoint_11_78_p6 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 6 210820411559308064 = some 210820411559308064 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 4 2 210820411559308064 210820411559308064 210820411559308064 endpoint_11_78_p4 endpoint_11_78_w4
private theorem endpoint_11_78_w6 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 6 2 210820411559308064 = some 210820411559308064 := by decide +kernel
private theorem endpoint_11_78_p8 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 8 210820411559308064 = some 210820411559308064 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 6 2 210820411559308064 210820411559308064 210820411559308064 endpoint_11_78_p6 endpoint_11_78_w6
private theorem endpoint_11_78_w8 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 8 2 210820411559308064 = some 210820411559308064 := by decide +kernel
private theorem endpoint_11_78_p10 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 10 210820411559308064 = some 210820411559308064 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 8 2 210820411559308064 210820411559308064 210820411559308064 endpoint_11_78_p8 endpoint_11_78_w8
def endpoint_11_78 : CertifiedEndpoint :=
  ⟨⟨11, 78, 1928⟩, 210820411559308064, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_11_78_flag endpoint_11_78_sources 10 210820411559308064 210820411559308064 rfl endpoint_11_78_base endpoint_11_78_p10) (by decide)⟩
private def endpoint_11_79_flag : Flag := ⟨11, 79, 1822⟩
private def endpoint_11_79_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_11_79_base : receiptBase endpoint_11_79_flag endpoint_11_79_sources = some 201615599618061255 := by decide +kernel
private theorem endpoint_11_79_w0 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 2 201615599618061255 = some 201615599618061255 := by decide +kernel
private theorem endpoint_11_79_w2 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 2 2 201615599618061255 = some 201615599618061255 := by decide +kernel
private theorem endpoint_11_79_p4 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 4 201615599618061255 = some 201615599618061255 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 2 2 201615599618061255 201615599618061255 201615599618061255 endpoint_11_79_w0 endpoint_11_79_w2
private theorem endpoint_11_79_w4 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 4 2 201615599618061255 = some 201615599618061255 := by decide +kernel
private theorem endpoint_11_79_p6 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 6 201615599618061255 = some 201615599618061255 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 4 2 201615599618061255 201615599618061255 201615599618061255 endpoint_11_79_p4 endpoint_11_79_w4
private theorem endpoint_11_79_w6 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 6 2 201615599618061255 = some 201615599618061255 := by decide +kernel
private theorem endpoint_11_79_p8 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 8 201615599618061255 = some 201615599618061255 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 6 2 201615599618061255 201615599618061255 201615599618061255 endpoint_11_79_p6 endpoint_11_79_w6
private theorem endpoint_11_79_w8 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 8 2 201615599618061255 = some 201615599618061255 := by decide +kernel
private theorem endpoint_11_79_p10 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 10 201615599618061255 = some 201615599618061255 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 8 2 201615599618061255 201615599618061255 201615599618061255 endpoint_11_79_p8 endpoint_11_79_w8
def endpoint_11_79 : CertifiedEndpoint :=
  ⟨⟨11, 79, 1822⟩, 201615599618061255, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_11_79_flag endpoint_11_79_sources 10 201615599618061255 201615599618061255 rfl endpoint_11_79_base endpoint_11_79_p10) (by decide)⟩
private def endpoint_11_80_flag : Flag := ⟨11, 80, 1714⟩
private def endpoint_11_80_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_11_80_base : receiptBase endpoint_11_80_flag endpoint_11_80_sources = some 195439087642415046 := by decide +kernel
private theorem endpoint_11_80_w0 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 2 195439087642415046 = some 195439087642415046 := by decide +kernel
private theorem endpoint_11_80_w2 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 2 2 195439087642415046 = some 195439087642415046 := by decide +kernel
private theorem endpoint_11_80_p4 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 4 195439087642415046 = some 195439087642415046 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 2 2 195439087642415046 195439087642415046 195439087642415046 endpoint_11_80_w0 endpoint_11_80_w2
private theorem endpoint_11_80_w4 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 4 2 195439087642415046 = some 195439087642415046 := by decide +kernel
private theorem endpoint_11_80_p6 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 6 195439087642415046 = some 195439087642415046 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 4 2 195439087642415046 195439087642415046 195439087642415046 endpoint_11_80_p4 endpoint_11_80_w4
private theorem endpoint_11_80_w6 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 6 2 195439087642415046 = some 195439087642415046 := by decide +kernel
private theorem endpoint_11_80_p8 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 8 195439087642415046 = some 195439087642415046 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 6 2 195439087642415046 195439087642415046 195439087642415046 endpoint_11_80_p6 endpoint_11_80_w6
private theorem endpoint_11_80_w8 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 8 2 195439087642415046 = some 195439087642415046 := by decide +kernel
private theorem endpoint_11_80_p10 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 10 195439087642415046 = some 195439087642415046 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 8 2 195439087642415046 195439087642415046 195439087642415046 endpoint_11_80_p8 endpoint_11_80_w8
def endpoint_11_80 : CertifiedEndpoint :=
  ⟨⟨11, 80, 1714⟩, 195439087642415046, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_11_80_flag endpoint_11_80_sources 10 195439087642415046 195439087642415046 rfl endpoint_11_80_base endpoint_11_80_p10) (by decide)⟩
private def endpoint_11_81_flag : Flag := ⟨11, 81, 1602⟩
private def endpoint_11_81_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_11_81_base : receiptBase endpoint_11_81_flag endpoint_11_81_sources = some 184771916894440716 := by decide +kernel
private theorem endpoint_11_81_w0 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 2 184771916894440716 = some 184771916894440716 := by decide +kernel
private theorem endpoint_11_81_w2 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 2 2 184771916894440716 = some 184771916894440716 := by decide +kernel
private theorem endpoint_11_81_p4 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 4 184771916894440716 = some 184771916894440716 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 2 2 184771916894440716 184771916894440716 184771916894440716 endpoint_11_81_w0 endpoint_11_81_w2
private theorem endpoint_11_81_w4 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 4 2 184771916894440716 = some 184771916894440716 := by decide +kernel
private theorem endpoint_11_81_p6 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 6 184771916894440716 = some 184771916894440716 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 4 2 184771916894440716 184771916894440716 184771916894440716 endpoint_11_81_p4 endpoint_11_81_w4
private theorem endpoint_11_81_w6 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 6 2 184771916894440716 = some 184771916894440716 := by decide +kernel
private theorem endpoint_11_81_p8 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 8 184771916894440716 = some 184771916894440716 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 6 2 184771916894440716 184771916894440716 184771916894440716 endpoint_11_81_p6 endpoint_11_81_w6
private theorem endpoint_11_81_w8 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 8 2 184771916894440716 = some 184771916894440716 := by decide +kernel
private theorem endpoint_11_81_p10 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 10 184771916894440716 = some 184771916894440716 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 8 2 184771916894440716 184771916894440716 184771916894440716 endpoint_11_81_p8 endpoint_11_81_w8
def endpoint_11_81 : CertifiedEndpoint :=
  ⟨⟨11, 81, 1602⟩, 184771916894440716, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_11_81_flag endpoint_11_81_sources 10 184771916894440716 184771916894440716 rfl endpoint_11_81_base endpoint_11_81_p10) (by decide)⟩
private def endpoint_11_82_flag : Flag := ⟨11, 82, 1487⟩
private def endpoint_11_82_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_11_82_base : receiptBase endpoint_11_82_flag endpoint_11_82_sources = some 174715647067246433 := by decide +kernel
private theorem endpoint_11_82_w0 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 2 174715647067246433 = some 174715647067246433 := by decide +kernel
private theorem endpoint_11_82_w2 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 2 2 174715647067246433 = some 174715647067246433 := by decide +kernel
private theorem endpoint_11_82_p4 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 4 174715647067246433 = some 174715647067246433 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 2 2 174715647067246433 174715647067246433 174715647067246433 endpoint_11_82_w0 endpoint_11_82_w2
private theorem endpoint_11_82_w4 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 4 2 174715647067246433 = some 174715647067246433 := by decide +kernel
private theorem endpoint_11_82_p6 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 6 174715647067246433 = some 174715647067246433 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 4 2 174715647067246433 174715647067246433 174715647067246433 endpoint_11_82_p4 endpoint_11_82_w4
private theorem endpoint_11_82_w6 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 6 2 174715647067246433 = some 174715647067246433 := by decide +kernel
private theorem endpoint_11_82_p8 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 8 174715647067246433 = some 174715647067246433 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 6 2 174715647067246433 174715647067246433 174715647067246433 endpoint_11_82_p6 endpoint_11_82_w6
private theorem endpoint_11_82_w8 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 8 2 174715647067246433 = some 174715647067246433 := by decide +kernel
private theorem endpoint_11_82_p10 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 10 174715647067246433 = some 174715647067246433 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 8 2 174715647067246433 174715647067246433 174715647067246433 endpoint_11_82_p8 endpoint_11_82_w8
def endpoint_11_82 : CertifiedEndpoint :=
  ⟨⟨11, 82, 1487⟩, 174715647067246433, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_11_82_flag endpoint_11_82_sources 10 174715647067246433 174715647067246433 rfl endpoint_11_82_base endpoint_11_82_p10) (by decide)⟩
private def endpoint_11_83_flag : Flag := ⟨11, 83, 1370⟩
private def endpoint_11_83_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_11_83_base : receiptBase endpoint_11_83_flag endpoint_11_83_sources = some 162835868412828899 := by decide +kernel
private theorem endpoint_11_83_w0 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 0 2 162835868412828899 = some 162835868412828899 := by decide +kernel
private theorem endpoint_11_83_w2 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 2 2 162835868412828899 = some 162835868412828899 := by decide +kernel
private theorem endpoint_11_83_p4 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 0 4 162835868412828899 = some 162835868412828899 :=
  join_receipt_window endpoint_11_83_flag endpoint_11_83_sources 0 2 2 162835868412828899 162835868412828899 162835868412828899 endpoint_11_83_w0 endpoint_11_83_w2
private theorem endpoint_11_83_w4 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 4 2 162835868412828899 = some 162835868412828899 := by decide +kernel
private theorem endpoint_11_83_p6 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 0 6 162835868412828899 = some 162835868412828899 :=
  join_receipt_window endpoint_11_83_flag endpoint_11_83_sources 0 4 2 162835868412828899 162835868412828899 162835868412828899 endpoint_11_83_p4 endpoint_11_83_w4
private theorem endpoint_11_83_w6 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 6 2 162835868412828899 = some 162835868412828899 := by decide +kernel
private theorem endpoint_11_83_p8 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 0 8 162835868412828899 = some 162835868412828899 :=
  join_receipt_window endpoint_11_83_flag endpoint_11_83_sources 0 6 2 162835868412828899 162835868412828899 162835868412828899 endpoint_11_83_p6 endpoint_11_83_w6
private theorem endpoint_11_83_w8 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 8 2 162835868412828899 = some 162835868412828899 := by decide +kernel
private theorem endpoint_11_83_p10 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 0 10 162835868412828899 = some 162835868412828899 :=
  join_receipt_window endpoint_11_83_flag endpoint_11_83_sources 0 8 2 162835868412828899 162835868412828899 162835868412828899 endpoint_11_83_p8 endpoint_11_83_w8
def endpoint_11_83 : CertifiedEndpoint :=
  ⟨⟨11, 83, 1370⟩, 162835868412828899, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_11_83_flag endpoint_11_83_sources 10 162835868412828899 162835868412828899 rfl endpoint_11_83_base endpoint_11_83_p10) (by decide)⟩
def endpoint_11_84 : CertifiedEndpoint :=
  ⟨⟨11, 84, 1249⟩, 254946168117019933, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_85 : CertifiedEndpoint :=
  ⟨⟨11, 85, 1125⟩, 231515001524571834, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_86 : CertifiedEndpoint :=
  ⟨⟨11, 86, 998⟩, 206756424752125250, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_87 : CertifiedEndpoint :=
  ⟨⟨11, 87, 868⟩, 180646007413459603, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_88 : CertifiedEndpoint :=
  ⟨⟨11, 88, 734⟩, 152936722538340022, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_89 : CertifiedEndpoint :=
  ⟨⟨11, 89, 598⟩, 124046618421216673, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_90 : CertifiedEndpoint :=
  ⟨⟨11, 90, 458⟩, 93503357020482550, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_91 : CertifiedEndpoint :=
  ⟨⟨11, 91, 316⟩, 61735844580019187, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_92 : CertifiedEndpoint :=
  ⟨⟨11, 92, 170⟩, 28260885108788210, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_12 : CertifiedEndpoint :=
  ⟨⟨12, 12, 4701⟩, 95521257601793181, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_13 : CertifiedEndpoint :=
  ⟨⟨12, 13, 4679⟩, 99601622211025074, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_14 : CertifiedEndpoint :=
  ⟨⟨12, 14, 4656⟩, 103616976522972548, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_15 : CertifiedEndpoint :=
  ⟨⟨12, 15, 4633⟩, 116831142423538066, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_16 : CertifiedEndpoint :=
  ⟨⟨12, 16, 4610⟩, 129905615314810166, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_17 : CertifiedEndpoint :=
  ⟨⟨12, 17, 4587⟩, 142840395196788848, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_18 : CertifiedEndpoint :=
  ⟨⟨12, 18, 4563⟩, 155601293241583209, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_19 : CertifiedEndpoint :=
  ⟨⟨12, 19, 4539⟩, 168216553893709964, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_20 : CertifiedEndpoint :=
  ⟨⟨12, 20, 4515⟩, 180686177153169113, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_21 : CertifiedEndpoint :=
  ⟨⟨12, 21, 4491⟩, 193010163019960656, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_22 : CertifiedEndpoint :=
  ⟨⟨12, 22, 4466⟩, 205142433899445314, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_23 : CertifiedEndpoint :=
  ⟨⟨12, 23, 4442⟩, 217172172789214551, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_24 : CertifiedEndpoint :=
  ⟨⟨12, 24, 4416⟩, 228952230330289248, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_25 : CertifiedEndpoint :=
  ⟨⟨12, 25, 4391⟩, 240629755881648524, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_26 : CertifiedEndpoint :=
  ⟨⟨12, 26, 4365⟩, 252097733295578351, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_27 : CertifiedEndpoint :=
  ⟨⟨12, 27, 4339⟩, 263408184550092196, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_12_28_flag : Flag := ⟨12, 28, 4313⟩
private def endpoint_12_28_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_28_base : receiptBase endpoint_12_28_flag endpoint_12_28_sources = some 188803809892267110 := by decide +kernel
private theorem endpoint_12_28_w0 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 0 2 188803809892267110 = some 188803809892267110 := by decide +kernel
private theorem endpoint_12_28_w2 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 2 2 188803809892267110 = some 188803809892267110 := by decide +kernel
private theorem endpoint_12_28_p4 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 0 4 188803809892267110 = some 188803809892267110 :=
  join_receipt_window endpoint_12_28_flag endpoint_12_28_sources 0 2 2 188803809892267110 188803809892267110 188803809892267110 endpoint_12_28_w0 endpoint_12_28_w2
private theorem endpoint_12_28_w4 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 4 2 188803809892267110 = some 188803809892267110 := by decide +kernel
private theorem endpoint_12_28_p6 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 0 6 188803809892267110 = some 188803809892267110 :=
  join_receipt_window endpoint_12_28_flag endpoint_12_28_sources 0 4 2 188803809892267110 188803809892267110 188803809892267110 endpoint_12_28_p4 endpoint_12_28_w4
private theorem endpoint_12_28_w6 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 6 2 188803809892267110 = some 188803809892267110 := by decide +kernel
private theorem endpoint_12_28_p8 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 0 8 188803809892267110 = some 188803809892267110 :=
  join_receipt_window endpoint_12_28_flag endpoint_12_28_sources 0 6 2 188803809892267110 188803809892267110 188803809892267110 endpoint_12_28_p6 endpoint_12_28_w6
private theorem endpoint_12_28_w8 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 8 2 188803809892267110 = some 188803809892267110 := by decide +kernel
private theorem endpoint_12_28_p10 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 0 10 188803809892267110 = some 188803809892267110 :=
  join_receipt_window endpoint_12_28_flag endpoint_12_28_sources 0 8 2 188803809892267110 188803809892267110 188803809892267110 endpoint_12_28_p8 endpoint_12_28_w8
private theorem endpoint_12_28_w10 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 10 1 188803809892267110 = some 188803809892267110 := by decide +kernel
private theorem endpoint_12_28_p11 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 0 11 188803809892267110 = some 188803809892267110 :=
  join_receipt_window endpoint_12_28_flag endpoint_12_28_sources 0 10 1 188803809892267110 188803809892267110 188803809892267110 endpoint_12_28_p10 endpoint_12_28_w10
def endpoint_12_28 : CertifiedEndpoint :=
  ⟨⟨12, 28, 4313⟩, 188803809892267110, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_28_flag endpoint_12_28_sources 11 188803809892267110 188803809892267110 rfl endpoint_12_28_base endpoint_12_28_p11) (by decide)⟩
private def endpoint_12_29_flag : Flag := ⟨12, 29, 4286⟩
private def endpoint_12_29_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_29_base : receiptBase endpoint_12_29_flag endpoint_12_29_sources = some 192974677861927679 := by decide +kernel
private theorem endpoint_12_29_w0 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 0 2 192974677861927679 = some 192974677861927679 := by decide +kernel
private theorem endpoint_12_29_w2 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 2 2 192974677861927679 = some 192974677861927679 := by decide +kernel
private theorem endpoint_12_29_p4 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 0 4 192974677861927679 = some 192974677861927679 :=
  join_receipt_window endpoint_12_29_flag endpoint_12_29_sources 0 2 2 192974677861927679 192974677861927679 192974677861927679 endpoint_12_29_w0 endpoint_12_29_w2
private theorem endpoint_12_29_w4 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 4 2 192974677861927679 = some 192974677861927679 := by decide +kernel
private theorem endpoint_12_29_p6 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 0 6 192974677861927679 = some 192974677861927679 :=
  join_receipt_window endpoint_12_29_flag endpoint_12_29_sources 0 4 2 192974677861927679 192974677861927679 192974677861927679 endpoint_12_29_p4 endpoint_12_29_w4
private theorem endpoint_12_29_w6 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 6 2 192974677861927679 = some 192974677861927679 := by decide +kernel
private theorem endpoint_12_29_p8 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 0 8 192974677861927679 = some 192974677861927679 :=
  join_receipt_window endpoint_12_29_flag endpoint_12_29_sources 0 6 2 192974677861927679 192974677861927679 192974677861927679 endpoint_12_29_p6 endpoint_12_29_w6
private theorem endpoint_12_29_w8 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 8 2 192974677861927679 = some 192974677861927679 := by decide +kernel
private theorem endpoint_12_29_p10 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 0 10 192974677861927679 = some 192974677861927679 :=
  join_receipt_window endpoint_12_29_flag endpoint_12_29_sources 0 8 2 192974677861927679 192974677861927679 192974677861927679 endpoint_12_29_p8 endpoint_12_29_w8
private theorem endpoint_12_29_w10 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 10 1 192974677861927679 = some 192974677861927679 := by decide +kernel
private theorem endpoint_12_29_p11 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 0 11 192974677861927679 = some 192974677861927679 :=
  join_receipt_window endpoint_12_29_flag endpoint_12_29_sources 0 10 1 192974677861927679 192974677861927679 192974677861927679 endpoint_12_29_p10 endpoint_12_29_w10
def endpoint_12_29 : CertifiedEndpoint :=
  ⟨⟨12, 29, 4286⟩, 192974677861927679, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_29_flag endpoint_12_29_sources 11 192974677861927679 192974677861927679 rfl endpoint_12_29_base endpoint_12_29_p11) (by decide)⟩
private def endpoint_12_30_flag : Flag := ⟨12, 30, 4259⟩
private def endpoint_12_30_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_30_base : receiptBase endpoint_12_30_flag endpoint_12_30_sources = some 197078377314051849 := by decide +kernel
private theorem endpoint_12_30_w0 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 2 197078377314051849 = some 197078377314051849 := by decide +kernel
private theorem endpoint_12_30_w2 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 2 2 197078377314051849 = some 197078377314051849 := by decide +kernel
private theorem endpoint_12_30_p4 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 4 197078377314051849 = some 197078377314051849 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 2 2 197078377314051849 197078377314051849 197078377314051849 endpoint_12_30_w0 endpoint_12_30_w2
private theorem endpoint_12_30_w4 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 4 2 197078377314051849 = some 197078377314051849 := by decide +kernel
private theorem endpoint_12_30_p6 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 6 197078377314051849 = some 197078377314051849 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 4 2 197078377314051849 197078377314051849 197078377314051849 endpoint_12_30_p4 endpoint_12_30_w4
private theorem endpoint_12_30_w6 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 6 2 197078377314051849 = some 197078377314051849 := by decide +kernel
private theorem endpoint_12_30_p8 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 8 197078377314051849 = some 197078377314051849 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 6 2 197078377314051849 197078377314051849 197078377314051849 endpoint_12_30_p6 endpoint_12_30_w6
private theorem endpoint_12_30_w8 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 8 2 197078377314051849 = some 197078377314051849 := by decide +kernel
private theorem endpoint_12_30_p10 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 10 197078377314051849 = some 197078377314051849 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 8 2 197078377314051849 197078377314051849 197078377314051849 endpoint_12_30_p8 endpoint_12_30_w8
private theorem endpoint_12_30_w10 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 10 1 197078377314051849 = some 197078377314051849 := by decide +kernel
private theorem endpoint_12_30_p11 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 11 197078377314051849 = some 197078377314051849 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 10 1 197078377314051849 197078377314051849 197078377314051849 endpoint_12_30_p10 endpoint_12_30_w10
def endpoint_12_30 : CertifiedEndpoint :=
  ⟨⟨12, 30, 4259⟩, 197078377314051849, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_30_flag endpoint_12_30_sources 11 197078377314051849 197078377314051849 rfl endpoint_12_30_base endpoint_12_30_p11) (by decide)⟩
private def endpoint_12_31_flag : Flag := ⟨12, 31, 4232⟩
private def endpoint_12_31_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_31_base : receiptBase endpoint_12_31_flag endpoint_12_31_sources = some 201114908248639620 := by decide +kernel
private theorem endpoint_12_31_w0 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 2 201114908248639620 = some 201114908248639620 := by decide +kernel
private theorem endpoint_12_31_w2 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 2 2 201114908248639620 = some 201114908248639620 := by decide +kernel
private theorem endpoint_12_31_p4 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 4 201114908248639620 = some 201114908248639620 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 2 2 201114908248639620 201114908248639620 201114908248639620 endpoint_12_31_w0 endpoint_12_31_w2
private theorem endpoint_12_31_w4 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 4 2 201114908248639620 = some 201114908248639620 := by decide +kernel
private theorem endpoint_12_31_p6 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 6 201114908248639620 = some 201114908248639620 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 4 2 201114908248639620 201114908248639620 201114908248639620 endpoint_12_31_p4 endpoint_12_31_w4
private theorem endpoint_12_31_w6 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 6 2 201114908248639620 = some 201114908248639620 := by decide +kernel
private theorem endpoint_12_31_p8 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 8 201114908248639620 = some 201114908248639620 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 6 2 201114908248639620 201114908248639620 201114908248639620 endpoint_12_31_p6 endpoint_12_31_w6
private theorem endpoint_12_31_w8 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 8 2 201114908248639620 = some 201114908248639620 := by decide +kernel
private theorem endpoint_12_31_p10 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 10 201114908248639620 = some 201114908248639620 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 8 2 201114908248639620 201114908248639620 201114908248639620 endpoint_12_31_p8 endpoint_12_31_w8
private theorem endpoint_12_31_w10 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 10 1 201114908248639620 = some 201114908248639620 := by decide +kernel
private theorem endpoint_12_31_p11 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 11 201114908248639620 = some 201114908248639620 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 10 1 201114908248639620 201114908248639620 201114908248639620 endpoint_12_31_p10 endpoint_12_31_w10
def endpoint_12_31 : CertifiedEndpoint :=
  ⟨⟨12, 31, 4232⟩, 201114908248639620, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_31_flag endpoint_12_31_sources 11 201114908248639620 201114908248639620 rfl endpoint_12_31_base endpoint_12_31_p11) (by decide)⟩
private def endpoint_12_32_flag : Flag := ⟨12, 32, 4204⟩
private def endpoint_12_32_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_32_base : receiptBase endpoint_12_32_flag endpoint_12_32_sources = some 205036168010118207 := by decide +kernel
private theorem endpoint_12_32_w0 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 2 205036168010118207 = some 205036168010118207 := by decide +kernel
private theorem endpoint_12_32_w2 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 2 2 205036168010118207 = some 205036168010118207 := by decide +kernel
private theorem endpoint_12_32_p4 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 4 205036168010118207 = some 205036168010118207 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 2 2 205036168010118207 205036168010118207 205036168010118207 endpoint_12_32_w0 endpoint_12_32_w2
private theorem endpoint_12_32_w4 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 4 2 205036168010118207 = some 205036168010118207 := by decide +kernel
private theorem endpoint_12_32_p6 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 6 205036168010118207 = some 205036168010118207 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 4 2 205036168010118207 205036168010118207 205036168010118207 endpoint_12_32_p4 endpoint_12_32_w4
private theorem endpoint_12_32_w6 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 6 2 205036168010118207 = some 205036168010118207 := by decide +kernel
private theorem endpoint_12_32_p8 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 8 205036168010118207 = some 205036168010118207 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 6 2 205036168010118207 205036168010118207 205036168010118207 endpoint_12_32_p6 endpoint_12_32_w6
private theorem endpoint_12_32_w8 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 8 2 205036168010118207 = some 205036168010118207 := by decide +kernel
private theorem endpoint_12_32_p10 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 10 205036168010118207 = some 205036168010118207 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 8 2 205036168010118207 205036168010118207 205036168010118207 endpoint_12_32_p8 endpoint_12_32_w8
private theorem endpoint_12_32_w10 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 10 1 205036168010118207 = some 205036168010118207 := by decide +kernel
private theorem endpoint_12_32_p11 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 11 205036168010118207 = some 205036168010118207 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 10 1 205036168010118207 205036168010118207 205036168010118207 endpoint_12_32_p10 endpoint_12_32_w10
def endpoint_12_32 : CertifiedEndpoint :=
  ⟨⟨12, 32, 4204⟩, 205036168010118207, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_32_flag endpoint_12_32_sources 11 205036168010118207 205036168010118207 rfl endpoint_12_32_base endpoint_12_32_p11) (by decide)⟩
private def endpoint_12_33_flag : Flag := ⟨12, 33, 4176⟩
private def endpoint_12_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_33_base : receiptBase endpoint_12_33_flag endpoint_12_33_sources = some 208887816926135618 := by decide +kernel
private theorem endpoint_12_33_w0 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 2 208887816926135618 = some 208887816926135618 := by decide +kernel
private theorem endpoint_12_33_w2 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 2 2 208887816926135618 = some 208887816926135618 := by decide +kernel
private theorem endpoint_12_33_p4 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 4 208887816926135618 = some 208887816926135618 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 2 2 208887816926135618 208887816926135618 208887816926135618 endpoint_12_33_w0 endpoint_12_33_w2
private theorem endpoint_12_33_w4 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 4 2 208887816926135618 = some 208887816926135618 := by decide +kernel
private theorem endpoint_12_33_p6 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 6 208887816926135618 = some 208887816926135618 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 4 2 208887816926135618 208887816926135618 208887816926135618 endpoint_12_33_p4 endpoint_12_33_w4
private theorem endpoint_12_33_w6 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 6 2 208887816926135618 = some 208887816926135618 := by decide +kernel
private theorem endpoint_12_33_p8 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 8 208887816926135618 = some 208887816926135618 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 6 2 208887816926135618 208887816926135618 208887816926135618 endpoint_12_33_p6 endpoint_12_33_w6
private theorem endpoint_12_33_w8 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 8 2 208887816926135618 = some 208887816926135618 := by decide +kernel
private theorem endpoint_12_33_p10 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 10 208887816926135618 = some 208887816926135618 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 8 2 208887816926135618 208887816926135618 208887816926135618 endpoint_12_33_p8 endpoint_12_33_w8
private theorem endpoint_12_33_w10 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 10 1 208887816926135618 = some 208887816926135618 := by decide +kernel
private theorem endpoint_12_33_p11 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 11 208887816926135618 = some 208887816926135618 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 10 1 208887816926135618 208887816926135618 208887816926135618 endpoint_12_33_p10 endpoint_12_33_w10
def endpoint_12_33 : CertifiedEndpoint :=
  ⟨⟨12, 33, 4176⟩, 208887816926135618, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_33_flag endpoint_12_33_sources 11 208887816926135618 208887816926135618 rfl endpoint_12_33_base endpoint_12_33_p11) (by decide)⟩
private def endpoint_12_34_flag : Flag := ⟨12, 34, 4147⟩
private def endpoint_12_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_34_base : receiptBase endpoint_12_34_flag endpoint_12_34_sources = some 212619310013194289 := by decide +kernel
private theorem endpoint_12_34_w0 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 2 212619310013194289 = some 212619310013194289 := by decide +kernel
private theorem endpoint_12_34_w2 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 2 2 212619310013194289 = some 212619310013194289 := by decide +kernel
private theorem endpoint_12_34_p4 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 4 212619310013194289 = some 212619310013194289 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 2 2 212619310013194289 212619310013194289 212619310013194289 endpoint_12_34_w0 endpoint_12_34_w2
private theorem endpoint_12_34_w4 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 4 2 212619310013194289 = some 212619310013194289 := by decide +kernel
private theorem endpoint_12_34_p6 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 6 212619310013194289 = some 212619310013194289 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 4 2 212619310013194289 212619310013194289 212619310013194289 endpoint_12_34_p4 endpoint_12_34_w4
private theorem endpoint_12_34_w6 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 6 2 212619310013194289 = some 212619310013194289 := by decide +kernel
private theorem endpoint_12_34_p8 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 8 212619310013194289 = some 212619310013194289 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 6 2 212619310013194289 212619310013194289 212619310013194289 endpoint_12_34_p6 endpoint_12_34_w6
private theorem endpoint_12_34_w8 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 8 2 212619310013194289 = some 212619310013194289 := by decide +kernel
private theorem endpoint_12_34_p10 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 10 212619310013194289 = some 212619310013194289 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 8 2 212619310013194289 212619310013194289 212619310013194289 endpoint_12_34_p8 endpoint_12_34_w8
private theorem endpoint_12_34_w10 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 10 1 212619310013194289 = some 212619310013194289 := by decide +kernel
private theorem endpoint_12_34_p11 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 11 212619310013194289 = some 212619310013194289 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 10 1 212619310013194289 212619310013194289 212619310013194289 endpoint_12_34_p10 endpoint_12_34_w10
def endpoint_12_34 : CertifiedEndpoint :=
  ⟨⟨12, 34, 4147⟩, 212619310013194289, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_34_flag endpoint_12_34_sources 11 212619310013194289 212619310013194289 rfl endpoint_12_34_base endpoint_12_34_p11) (by decide)⟩
private def endpoint_12_35_flag : Flag := ⟨12, 35, 4118⟩
private def endpoint_12_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_35_base : receiptBase endpoint_12_35_flag endpoint_12_35_sources = some 216278749926867006 := by decide +kernel
private theorem endpoint_12_35_w0 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 2 216278749926867006 = some 216278749926867006 := by decide +kernel
private theorem endpoint_12_35_w2 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 2 2 216278749926867006 = some 216278749926867006 := by decide +kernel
private theorem endpoint_12_35_p4 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 4 216278749926867006 = some 216278749926867006 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 2 2 216278749926867006 216278749926867006 216278749926867006 endpoint_12_35_w0 endpoint_12_35_w2
private theorem endpoint_12_35_w4 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 4 2 216278749926867006 = some 216278749926867006 := by decide +kernel
private theorem endpoint_12_35_p6 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 6 216278749926867006 = some 216278749926867006 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 4 2 216278749926867006 216278749926867006 216278749926867006 endpoint_12_35_p4 endpoint_12_35_w4
private theorem endpoint_12_35_w6 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 6 2 216278749926867006 = some 216278749926867006 := by decide +kernel
private theorem endpoint_12_35_p8 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 8 216278749926867006 = some 216278749926867006 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 6 2 216278749926867006 216278749926867006 216278749926867006 endpoint_12_35_p6 endpoint_12_35_w6
private theorem endpoint_12_35_w8 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 8 2 216278749926867006 = some 216278749926867006 := by decide +kernel
private theorem endpoint_12_35_p10 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 10 216278749926867006 = some 216278749926867006 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 8 2 216278749926867006 216278749926867006 216278749926867006 endpoint_12_35_p8 endpoint_12_35_w8
private theorem endpoint_12_35_w10 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 10 1 216278749926867006 = some 216278749926867006 := by decide +kernel
private theorem endpoint_12_35_p11 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 11 216278749926867006 = some 216278749926867006 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 10 1 216278749926867006 216278749926867006 216278749926867006 endpoint_12_35_p10 endpoint_12_35_w10
def endpoint_12_35 : CertifiedEndpoint :=
  ⟨⟨12, 35, 4118⟩, 216278749926867006, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_35_flag endpoint_12_35_sources 11 216278749926867006 216278749926867006 rfl endpoint_12_35_base endpoint_12_35_p11) (by decide)⟩
private def endpoint_12_36_flag : Flag := ⟨12, 36, 4089⟩
private def endpoint_12_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_36_base : receiptBase endpoint_12_36_flag endpoint_12_36_sources = some 219866136667153769 := by decide +kernel
private theorem endpoint_12_36_w0 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 2 219866136667153769 = some 219866136667153769 := by decide +kernel
private theorem endpoint_12_36_w2 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 2 2 219866136667153769 = some 219866136667153769 := by decide +kernel
private theorem endpoint_12_36_p4 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 4 219866136667153769 = some 219866136667153769 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 2 2 219866136667153769 219866136667153769 219866136667153769 endpoint_12_36_w0 endpoint_12_36_w2
private theorem endpoint_12_36_w4 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 4 2 219866136667153769 = some 219866136667153769 := by decide +kernel
private theorem endpoint_12_36_p6 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 6 219866136667153769 = some 219866136667153769 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 4 2 219866136667153769 219866136667153769 219866136667153769 endpoint_12_36_p4 endpoint_12_36_w4
private theorem endpoint_12_36_w6 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 6 2 219866136667153769 = some 219866136667153769 := by decide +kernel
private theorem endpoint_12_36_p8 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 8 219866136667153769 = some 219866136667153769 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 6 2 219866136667153769 219866136667153769 219866136667153769 endpoint_12_36_p6 endpoint_12_36_w6
private theorem endpoint_12_36_w8 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 8 2 219866136667153769 = some 219866136667153769 := by decide +kernel
private theorem endpoint_12_36_p10 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 10 219866136667153769 = some 219866136667153769 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 8 2 219866136667153769 219866136667153769 219866136667153769 endpoint_12_36_p8 endpoint_12_36_w8
private theorem endpoint_12_36_w10 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 10 1 219866136667153769 = some 219866136667153769 := by decide +kernel
private theorem endpoint_12_36_p11 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 11 219866136667153769 = some 219866136667153769 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 10 1 219866136667153769 219866136667153769 219866136667153769 endpoint_12_36_p10 endpoint_12_36_w10
def endpoint_12_36 : CertifiedEndpoint :=
  ⟨⟨12, 36, 4089⟩, 219866136667153769, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_36_flag endpoint_12_36_sources 11 219866136667153769 219866136667153769 rfl endpoint_12_36_base endpoint_12_36_p11) (by decide)⟩
private def endpoint_12_37_flag : Flag := ⟨12, 37, 4059⟩
private def endpoint_12_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_37_base : receiptBase endpoint_12_37_flag endpoint_12_37_sources = some 223327261758669849 := by decide +kernel
private theorem endpoint_12_37_w0 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 2 223327261758669849 = some 223327261758669849 := by decide +kernel
private theorem endpoint_12_37_w2 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 2 2 223327261758669849 = some 223327261758669849 := by decide +kernel
private theorem endpoint_12_37_p4 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 4 223327261758669849 = some 223327261758669849 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 2 2 223327261758669849 223327261758669849 223327261758669849 endpoint_12_37_w0 endpoint_12_37_w2
private theorem endpoint_12_37_w4 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 4 2 223327261758669849 = some 223327261758669849 := by decide +kernel
private theorem endpoint_12_37_p6 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 6 223327261758669849 = some 223327261758669849 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 4 2 223327261758669849 223327261758669849 223327261758669849 endpoint_12_37_p4 endpoint_12_37_w4
private theorem endpoint_12_37_w6 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 6 2 223327261758669849 = some 223327261758669849 := by decide +kernel
private theorem endpoint_12_37_p8 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 8 223327261758669849 = some 223327261758669849 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 6 2 223327261758669849 223327261758669849 223327261758669849 endpoint_12_37_p6 endpoint_12_37_w6
private theorem endpoint_12_37_w8 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 8 2 223327261758669849 = some 223327261758669849 := by decide +kernel
private theorem endpoint_12_37_p10 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 10 223327261758669849 = some 223327261758669849 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 8 2 223327261758669849 223327261758669849 223327261758669849 endpoint_12_37_p8 endpoint_12_37_w8
private theorem endpoint_12_37_w10 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 10 1 223327261758669849 = some 223327261758669849 := by decide +kernel
private theorem endpoint_12_37_p11 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 11 223327261758669849 = some 223327261758669849 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 10 1 223327261758669849 223327261758669849 223327261758669849 endpoint_12_37_p10 endpoint_12_37_w10
def endpoint_12_37 : CertifiedEndpoint :=
  ⟨⟨12, 37, 4059⟩, 223327261758669849, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_37_flag endpoint_12_37_sources 11 223327261758669849 223327261758669849 rfl endpoint_12_37_base endpoint_12_37_p11) (by decide)⟩
private def endpoint_12_38_flag : Flag := ⟨12, 38, 4028⟩
private def endpoint_12_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_38_base : receiptBase endpoint_12_38_flag endpoint_12_38_sources = some 226658461709528079 := by decide +kernel
private theorem endpoint_12_38_w0 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 2 226658461709528079 = some 226658461709528079 := by decide +kernel
private theorem endpoint_12_38_w2 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 2 2 226658461709528079 = some 226658461709528079 := by decide +kernel
private theorem endpoint_12_38_p4 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 4 226658461709528079 = some 226658461709528079 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 2 2 226658461709528079 226658461709528079 226658461709528079 endpoint_12_38_w0 endpoint_12_38_w2
private theorem endpoint_12_38_w4 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 4 2 226658461709528079 = some 226658461709528079 := by decide +kernel
private theorem endpoint_12_38_p6 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 6 226658461709528079 = some 226658461709528079 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 4 2 226658461709528079 226658461709528079 226658461709528079 endpoint_12_38_p4 endpoint_12_38_w4
private theorem endpoint_12_38_w6 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 6 2 226658461709528079 = some 226658461709528079 := by decide +kernel
private theorem endpoint_12_38_p8 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 8 226658461709528079 = some 226658461709528079 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 6 2 226658461709528079 226658461709528079 226658461709528079 endpoint_12_38_p6 endpoint_12_38_w6
private theorem endpoint_12_38_w8 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 8 2 226658461709528079 = some 226658461709528079 := by decide +kernel
private theorem endpoint_12_38_p10 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 10 226658461709528079 = some 226658461709528079 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 8 2 226658461709528079 226658461709528079 226658461709528079 endpoint_12_38_p8 endpoint_12_38_w8
private theorem endpoint_12_38_w10 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 10 1 226658461709528079 = some 226658461709528079 := by decide +kernel
private theorem endpoint_12_38_p11 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 11 226658461709528079 = some 226658461709528079 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 10 1 226658461709528079 226658461709528079 226658461709528079 endpoint_12_38_p10 endpoint_12_38_w10
def endpoint_12_38 : CertifiedEndpoint :=
  ⟨⟨12, 38, 4028⟩, 226658461709528079, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_38_flag endpoint_12_38_sources 11 226658461709528079 226658461709528079 rfl endpoint_12_38_base endpoint_12_38_p11) (by decide)⟩
private def endpoint_12_39_flag : Flag := ⟨12, 39, 3997⟩
private def endpoint_12_39_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_39_base : receiptBase endpoint_12_39_flag endpoint_12_39_sources = some 230858936527153059 := by decide +kernel
private theorem endpoint_12_39_w0 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 2 230858936527153059 = some 230858936527153059 := by decide +kernel
private theorem endpoint_12_39_w2 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 2 2 230858936527153059 = some 230858936527153059 := by decide +kernel
private theorem endpoint_12_39_p4 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 4 230858936527153059 = some 230858936527153059 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 2 2 230858936527153059 230858936527153059 230858936527153059 endpoint_12_39_w0 endpoint_12_39_w2
private theorem endpoint_12_39_w4 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 4 2 230858936527153059 = some 230858936527153059 := by decide +kernel
private theorem endpoint_12_39_p6 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 6 230858936527153059 = some 230858936527153059 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 4 2 230858936527153059 230858936527153059 230858936527153059 endpoint_12_39_p4 endpoint_12_39_w4
private theorem endpoint_12_39_w6 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 6 2 230858936527153059 = some 230858936527153059 := by decide +kernel
private theorem endpoint_12_39_p8 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 8 230858936527153059 = some 230858936527153059 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 6 2 230858936527153059 230858936527153059 230858936527153059 endpoint_12_39_p6 endpoint_12_39_w6
private theorem endpoint_12_39_w8 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 8 2 230858936527153059 = some 230858936527153059 := by decide +kernel
private theorem endpoint_12_39_p10 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 10 230858936527153059 = some 230858936527153059 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 8 2 230858936527153059 230858936527153059 230858936527153059 endpoint_12_39_p8 endpoint_12_39_w8
private theorem endpoint_12_39_w10 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 10 1 230858936527153059 = some 230858936527153059 := by decide +kernel
private theorem endpoint_12_39_p11 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 11 230858936527153059 = some 230858936527153059 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 10 1 230858936527153059 230858936527153059 230858936527153059 endpoint_12_39_p10 endpoint_12_39_w10
def endpoint_12_39 : CertifiedEndpoint :=
  ⟨⟨12, 39, 3997⟩, 230858936527153059, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_39_flag endpoint_12_39_sources 11 230858936527153059 230858936527153059 rfl endpoint_12_39_base endpoint_12_39_p11) (by decide)⟩
private def endpoint_12_40_flag : Flag := ⟨12, 40, 3966⟩
private def endpoint_12_40_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_40_base : receiptBase endpoint_12_40_flag endpoint_12_40_sources = some 233999327417562949 := by decide +kernel
private theorem endpoint_12_40_w0 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 2 233999327417562949 = some 233999327417562949 := by decide +kernel
private theorem endpoint_12_40_w2 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 2 2 233999327417562949 = some 233999327417562949 := by decide +kernel
private theorem endpoint_12_40_p4 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 4 233999327417562949 = some 233999327417562949 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 2 2 233999327417562949 233999327417562949 233999327417562949 endpoint_12_40_w0 endpoint_12_40_w2
private theorem endpoint_12_40_w4 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 4 2 233999327417562949 = some 233999327417562949 := by decide +kernel
private theorem endpoint_12_40_p6 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 6 233999327417562949 = some 233999327417562949 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 4 2 233999327417562949 233999327417562949 233999327417562949 endpoint_12_40_p4 endpoint_12_40_w4
private theorem endpoint_12_40_w6 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 6 2 233999327417562949 = some 233999327417562949 := by decide +kernel
private theorem endpoint_12_40_p8 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 8 233999327417562949 = some 233999327417562949 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 6 2 233999327417562949 233999327417562949 233999327417562949 endpoint_12_40_p6 endpoint_12_40_w6
private theorem endpoint_12_40_w8 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 8 2 233999327417562949 = some 233999327417562949 := by decide +kernel
private theorem endpoint_12_40_p10 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 10 233999327417562949 = some 233999327417562949 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 8 2 233999327417562949 233999327417562949 233999327417562949 endpoint_12_40_p8 endpoint_12_40_w8
private theorem endpoint_12_40_w10 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 10 1 233999327417562949 = some 233999327417562949 := by decide +kernel
private theorem endpoint_12_40_p11 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 11 233999327417562949 = some 233999327417562949 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 10 1 233999327417562949 233999327417562949 233999327417562949 endpoint_12_40_p10 endpoint_12_40_w10
def endpoint_12_40 : CertifiedEndpoint :=
  ⟨⟨12, 40, 3966⟩, 233999327417562949, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_40_flag endpoint_12_40_sources 11 233999327417562949 233999327417562949 rfl endpoint_12_40_base endpoint_12_40_p11) (by decide)⟩
private def endpoint_12_41_flag : Flag := ⟨12, 41, 3934⟩
private def endpoint_12_41_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_41_base : receiptBase endpoint_12_41_flag endpoint_12_41_sources = some 237003658156028147 := by decide +kernel
private theorem endpoint_12_41_w0 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 2 237003658156028147 = some 237003658156028147 := by decide +kernel
private theorem endpoint_12_41_w2 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 2 2 237003658156028147 = some 237003658156028147 := by decide +kernel
private theorem endpoint_12_41_p4 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 4 237003658156028147 = some 237003658156028147 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 2 2 237003658156028147 237003658156028147 237003658156028147 endpoint_12_41_w0 endpoint_12_41_w2
private theorem endpoint_12_41_w4 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 4 2 237003658156028147 = some 237003658156028147 := by decide +kernel
private theorem endpoint_12_41_p6 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 6 237003658156028147 = some 237003658156028147 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 4 2 237003658156028147 237003658156028147 237003658156028147 endpoint_12_41_p4 endpoint_12_41_w4
private theorem endpoint_12_41_w6 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 6 2 237003658156028147 = some 237003658156028147 := by decide +kernel
private theorem endpoint_12_41_p8 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 8 237003658156028147 = some 237003658156028147 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 6 2 237003658156028147 237003658156028147 237003658156028147 endpoint_12_41_p6 endpoint_12_41_w6
private theorem endpoint_12_41_w8 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 8 2 237003658156028147 = some 237003658156028147 := by decide +kernel
private theorem endpoint_12_41_p10 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 10 237003658156028147 = some 237003658156028147 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 8 2 237003658156028147 237003658156028147 237003658156028147 endpoint_12_41_p8 endpoint_12_41_w8
private theorem endpoint_12_41_w10 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 10 1 237003658156028147 = some 237003658156028147 := by decide +kernel
private theorem endpoint_12_41_p11 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 11 237003658156028147 = some 237003658156028147 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 10 1 237003658156028147 237003658156028147 237003658156028147 endpoint_12_41_p10 endpoint_12_41_w10
def endpoint_12_41 : CertifiedEndpoint :=
  ⟨⟨12, 41, 3934⟩, 237003658156028147, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_41_flag endpoint_12_41_sources 11 237003658156028147 237003658156028147 rfl endpoint_12_41_base endpoint_12_41_p11) (by decide)⟩
private def endpoint_12_42_flag : Flag := ⟨12, 42, 3901⟩
private def endpoint_12_42_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_42_base : receiptBase endpoint_12_42_flag endpoint_12_42_sources = some 239868278747198021 := by decide +kernel
private theorem endpoint_12_42_w0 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 2 239868278747198021 = some 239868278747198021 := by decide +kernel
private theorem endpoint_12_42_w2 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 2 2 239868278747198021 = some 239868278747198021 := by decide +kernel
private theorem endpoint_12_42_p4 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 4 239868278747198021 = some 239868278747198021 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 2 2 239868278747198021 239868278747198021 239868278747198021 endpoint_12_42_w0 endpoint_12_42_w2
private theorem endpoint_12_42_w4 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 4 2 239868278747198021 = some 239868278747198021 := by decide +kernel
private theorem endpoint_12_42_p6 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 6 239868278747198021 = some 239868278747198021 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 4 2 239868278747198021 239868278747198021 239868278747198021 endpoint_12_42_p4 endpoint_12_42_w4
private theorem endpoint_12_42_w6 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 6 2 239868278747198021 = some 239868278747198021 := by decide +kernel
private theorem endpoint_12_42_p8 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 8 239868278747198021 = some 239868278747198021 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 6 2 239868278747198021 239868278747198021 239868278747198021 endpoint_12_42_p6 endpoint_12_42_w6
private theorem endpoint_12_42_w8 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 8 2 239868278747198021 = some 239868278747198021 := by decide +kernel
private theorem endpoint_12_42_p10 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 10 239868278747198021 = some 239868278747198021 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 8 2 239868278747198021 239868278747198021 239868278747198021 endpoint_12_42_p8 endpoint_12_42_w8
private theorem endpoint_12_42_w10 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 10 1 239868278747198021 = some 239868278747198021 := by decide +kernel
private theorem endpoint_12_42_p11 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 11 239868278747198021 = some 239868278747198021 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 10 1 239868278747198021 239868278747198021 239868278747198021 endpoint_12_42_p10 endpoint_12_42_w10
def endpoint_12_42 : CertifiedEndpoint :=
  ⟨⟨12, 42, 3901⟩, 239868278747198021, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_42_flag endpoint_12_42_sources 11 239868278747198021 239868278747198021 rfl endpoint_12_42_base endpoint_12_42_p11) (by decide)⟩
private def endpoint_12_43_flag : Flag := ⟨12, 43, 3868⟩
private def endpoint_12_43_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_43_base : receiptBase endpoint_12_43_flag endpoint_12_43_sources = some 242651382775537080 := by decide +kernel
private theorem endpoint_12_43_w0 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 2 242651382775537080 = some 242651382775537080 := by decide +kernel
private theorem endpoint_12_43_w2 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 2 2 242651382775537080 = some 242651382775537080 := by decide +kernel
private theorem endpoint_12_43_p4 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 4 242651382775537080 = some 242651382775537080 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 2 2 242651382775537080 242651382775537080 242651382775537080 endpoint_12_43_w0 endpoint_12_43_w2
private theorem endpoint_12_43_w4 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 4 2 242651382775537080 = some 242651382775537080 := by decide +kernel
private theorem endpoint_12_43_p6 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 6 242651382775537080 = some 242651382775537080 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 4 2 242651382775537080 242651382775537080 242651382775537080 endpoint_12_43_p4 endpoint_12_43_w4
private theorem endpoint_12_43_w6 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 6 2 242651382775537080 = some 242651382775537080 := by decide +kernel
private theorem endpoint_12_43_p8 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 8 242651382775537080 = some 242651382775537080 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 6 2 242651382775537080 242651382775537080 242651382775537080 endpoint_12_43_p6 endpoint_12_43_w6
private theorem endpoint_12_43_w8 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 8 2 242651382775537080 = some 242651382775537080 := by decide +kernel
private theorem endpoint_12_43_p10 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 10 242651382775537080 = some 242651382775537080 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 8 2 242651382775537080 242651382775537080 242651382775537080 endpoint_12_43_p8 endpoint_12_43_w8
private theorem endpoint_12_43_w10 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 10 1 242651382775537080 = some 242651382775537080 := by decide +kernel
private theorem endpoint_12_43_p11 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 11 242651382775537080 = some 242651382775537080 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 10 1 242651382775537080 242651382775537080 242651382775537080 endpoint_12_43_p10 endpoint_12_43_w10
def endpoint_12_43 : CertifiedEndpoint :=
  ⟨⟨12, 43, 3868⟩, 242651382775537080, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_43_flag endpoint_12_43_sources 11 242651382775537080 242651382775537080 rfl endpoint_12_43_base endpoint_12_43_p11) (by decide)⟩
private def endpoint_12_44_flag : Flag := ⟨12, 44, 3834⟩
private def endpoint_12_44_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_44_base : receiptBase endpoint_12_44_flag endpoint_12_44_sources = some 245289909996113303 := by decide +kernel
private theorem endpoint_12_44_w0 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 2 245289909996113303 = some 245289909996113303 := by decide +kernel
private theorem endpoint_12_44_w2 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 2 2 245289909996113303 = some 245289909996113303 := by decide +kernel
private theorem endpoint_12_44_p4 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 4 245289909996113303 = some 245289909996113303 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 2 2 245289909996113303 245289909996113303 245289909996113303 endpoint_12_44_w0 endpoint_12_44_w2
private theorem endpoint_12_44_w4 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 4 2 245289909996113303 = some 245289909996113303 := by decide +kernel
private theorem endpoint_12_44_p6 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 6 245289909996113303 = some 245289909996113303 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 4 2 245289909996113303 245289909996113303 245289909996113303 endpoint_12_44_p4 endpoint_12_44_w4
private theorem endpoint_12_44_w6 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 6 2 245289909996113303 = some 245289909996113303 := by decide +kernel
private theorem endpoint_12_44_p8 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 8 245289909996113303 = some 245289909996113303 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 6 2 245289909996113303 245289909996113303 245289909996113303 endpoint_12_44_p6 endpoint_12_44_w6
private theorem endpoint_12_44_w8 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 8 2 245289909996113303 = some 245289909996113303 := by decide +kernel
private theorem endpoint_12_44_p10 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 10 245289909996113303 = some 245289909996113303 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 8 2 245289909996113303 245289909996113303 245289909996113303 endpoint_12_44_p8 endpoint_12_44_w8
private theorem endpoint_12_44_w10 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 10 1 245289909996113303 = some 245289909996113303 := by decide +kernel
private theorem endpoint_12_44_p11 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 11 245289909996113303 = some 245289909996113303 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 10 1 245289909996113303 245289909996113303 245289909996113303 endpoint_12_44_p10 endpoint_12_44_w10
def endpoint_12_44 : CertifiedEndpoint :=
  ⟨⟨12, 44, 3834⟩, 245289909996113303, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_44_flag endpoint_12_44_sources 11 245289909996113303 245289909996113303 rfl endpoint_12_44_base endpoint_12_44_p11) (by decide)⟩
private def endpoint_12_45_flag : Flag := ⟨12, 45, 3800⟩
private def endpoint_12_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_45_base : receiptBase endpoint_12_45_flag endpoint_12_45_sources = some 247844487323624955 := by decide +kernel
private theorem endpoint_12_45_w0 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 2 247844487323624955 = some 247844487323624955 := by decide +kernel
private theorem endpoint_12_45_w2 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 2 2 247844487323624955 = some 247844487323624955 := by decide +kernel
private theorem endpoint_12_45_p4 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 4 247844487323624955 = some 247844487323624955 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 2 2 247844487323624955 247844487323624955 247844487323624955 endpoint_12_45_w0 endpoint_12_45_w2
private theorem endpoint_12_45_w4 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 4 2 247844487323624955 = some 247844487323624955 := by decide +kernel
private theorem endpoint_12_45_p6 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 6 247844487323624955 = some 247844487323624955 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 4 2 247844487323624955 247844487323624955 247844487323624955 endpoint_12_45_p4 endpoint_12_45_w4
private theorem endpoint_12_45_w6 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 6 2 247844487323624955 = some 247844487323624955 := by decide +kernel
private theorem endpoint_12_45_p8 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 8 247844487323624955 = some 247844487323624955 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 6 2 247844487323624955 247844487323624955 247844487323624955 endpoint_12_45_p6 endpoint_12_45_w6
private theorem endpoint_12_45_w8 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 8 2 247844487323624955 = some 247844487323624955 := by decide +kernel
private theorem endpoint_12_45_p10 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 10 247844487323624955 = some 247844487323624955 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 8 2 247844487323624955 247844487323624955 247844487323624955 endpoint_12_45_p8 endpoint_12_45_w8
private theorem endpoint_12_45_w10 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 10 1 247844487323624955 = some 247844487323624955 := by decide +kernel
private theorem endpoint_12_45_p11 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 11 247844487323624955 = some 247844487323624955 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 10 1 247844487323624955 247844487323624955 247844487323624955 endpoint_12_45_p10 endpoint_12_45_w10
def endpoint_12_45 : CertifiedEndpoint :=
  ⟨⟨12, 45, 3800⟩, 247844487323624955, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_45_flag endpoint_12_45_sources 11 247844487323624955 247844487323624955 rfl endpoint_12_45_base endpoint_12_45_p11) (by decide)⟩
private def endpoint_12_46_flag : Flag := ⟨12, 46, 3764⟩
private def endpoint_12_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_46_base : receiptBase endpoint_12_46_flag endpoint_12_46_sources = some 250184127607740483 := by decide +kernel
private theorem endpoint_12_46_w0 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 2 250184127607740483 = some 250184127607740483 := by decide +kernel
private theorem endpoint_12_46_w2 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 2 2 250184127607740483 = some 250184127607740483 := by decide +kernel
private theorem endpoint_12_46_p4 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 4 250184127607740483 = some 250184127607740483 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 2 2 250184127607740483 250184127607740483 250184127607740483 endpoint_12_46_w0 endpoint_12_46_w2
private theorem endpoint_12_46_w4 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 4 2 250184127607740483 = some 250184127607740483 := by decide +kernel
private theorem endpoint_12_46_p6 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 6 250184127607740483 = some 250184127607740483 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 4 2 250184127607740483 250184127607740483 250184127607740483 endpoint_12_46_p4 endpoint_12_46_w4
private theorem endpoint_12_46_w6 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 6 2 250184127607740483 = some 250184127607740483 := by decide +kernel
private theorem endpoint_12_46_p8 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 8 250184127607740483 = some 250184127607740483 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 6 2 250184127607740483 250184127607740483 250184127607740483 endpoint_12_46_p6 endpoint_12_46_w6
private theorem endpoint_12_46_w8 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 8 2 250184127607740483 = some 250184127607740483 := by decide +kernel
private theorem endpoint_12_46_p10 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 10 250184127607740483 = some 250184127607740483 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 8 2 250184127607740483 250184127607740483 250184127607740483 endpoint_12_46_p8 endpoint_12_46_w8
private theorem endpoint_12_46_w10 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 10 1 250184127607740483 = some 250184127607740483 := by decide +kernel
private theorem endpoint_12_46_p11 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 11 250184127607740483 = some 250184127607740483 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 10 1 250184127607740483 250184127607740483 250184127607740483 endpoint_12_46_p10 endpoint_12_46_w10
def endpoint_12_46 : CertifiedEndpoint :=
  ⟨⟨12, 46, 3764⟩, 250184127607740483, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_46_flag endpoint_12_46_sources 11 250184127607740483 250184127607740483 rfl endpoint_12_46_base endpoint_12_46_p11) (by decide)⟩
private def endpoint_12_47_flag : Flag := ⟨12, 47, 3728⟩
private def endpoint_12_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_47_base : receiptBase endpoint_12_47_flag endpoint_12_47_sources = some 252434951338323929 := by decide +kernel
private theorem endpoint_12_47_w0 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 2 252434951338323929 = some 252434951338323929 := by decide +kernel
private theorem endpoint_12_47_w2 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 2 2 252434951338323929 = some 252434951338323929 := by decide +kernel
private theorem endpoint_12_47_p4 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 4 252434951338323929 = some 252434951338323929 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 2 2 252434951338323929 252434951338323929 252434951338323929 endpoint_12_47_w0 endpoint_12_47_w2
private theorem endpoint_12_47_w4 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 4 2 252434951338323929 = some 252434951338323929 := by decide +kernel
private theorem endpoint_12_47_p6 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 6 252434951338323929 = some 252434951338323929 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 4 2 252434951338323929 252434951338323929 252434951338323929 endpoint_12_47_p4 endpoint_12_47_w4
private theorem endpoint_12_47_w6 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 6 2 252434951338323929 = some 252434951338323929 := by decide +kernel
private theorem endpoint_12_47_p8 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 8 252434951338323929 = some 252434951338323929 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 6 2 252434951338323929 252434951338323929 252434951338323929 endpoint_12_47_p6 endpoint_12_47_w6
private theorem endpoint_12_47_w8 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 8 2 252434951338323929 = some 252434951338323929 := by decide +kernel
private theorem endpoint_12_47_p10 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 10 252434951338323929 = some 252434951338323929 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 8 2 252434951338323929 252434951338323929 252434951338323929 endpoint_12_47_p8 endpoint_12_47_w8
private theorem endpoint_12_47_w10 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 10 1 252434951338323929 = some 252434951338323929 := by decide +kernel
private theorem endpoint_12_47_p11 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 11 252434951338323929 = some 252434951338323929 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 10 1 252434951338323929 252434951338323929 252434951338323929 endpoint_12_47_p10 endpoint_12_47_w10
def endpoint_12_47 : CertifiedEndpoint :=
  ⟨⟨12, 47, 3728⟩, 252434951338323929, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_47_flag endpoint_12_47_sources 11 252434951338323929 252434951338323929 rfl endpoint_12_47_base endpoint_12_47_p11) (by decide)⟩
private def endpoint_12_48_flag : Flag := ⟨12, 48, 3692⟩
private def endpoint_12_48_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_48_base : receiptBase endpoint_12_48_flag endpoint_12_48_sources = some 255187294728097836 := by decide +kernel
private theorem endpoint_12_48_w0 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 2 255187294728097836 = some 255187294728097836 := by decide +kernel
private theorem endpoint_12_48_w2 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 2 2 255187294728097836 = some 255187294728097836 := by decide +kernel
private theorem endpoint_12_48_p4 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 4 255187294728097836 = some 255187294728097836 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 2 2 255187294728097836 255187294728097836 255187294728097836 endpoint_12_48_w0 endpoint_12_48_w2
private theorem endpoint_12_48_w4 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 4 2 255187294728097836 = some 255187294728097836 := by decide +kernel
private theorem endpoint_12_48_p6 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 6 255187294728097836 = some 255187294728097836 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 4 2 255187294728097836 255187294728097836 255187294728097836 endpoint_12_48_p4 endpoint_12_48_w4
private theorem endpoint_12_48_w6 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 6 2 255187294728097836 = some 255187294728097836 := by decide +kernel
private theorem endpoint_12_48_p8 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 8 255187294728097836 = some 255187294728097836 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 6 2 255187294728097836 255187294728097836 255187294728097836 endpoint_12_48_p6 endpoint_12_48_w6
private theorem endpoint_12_48_w8 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 8 2 255187294728097836 = some 255187294728097836 := by decide +kernel
private theorem endpoint_12_48_p10 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 10 255187294728097836 = some 255187294728097836 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 8 2 255187294728097836 255187294728097836 255187294728097836 endpoint_12_48_p8 endpoint_12_48_w8
private theorem endpoint_12_48_w10 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 10 1 255187294728097836 = some 255187294728097836 := by decide +kernel
private theorem endpoint_12_48_p11 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 11 255187294728097836 = some 255187294728097836 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 10 1 255187294728097836 255187294728097836 255187294728097836 endpoint_12_48_p10 endpoint_12_48_w10
def endpoint_12_48 : CertifiedEndpoint :=
  ⟨⟨12, 48, 3692⟩, 255187294728097836, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_48_flag endpoint_12_48_sources 11 255187294728097836 255187294728097836 rfl endpoint_12_48_base endpoint_12_48_p11) (by decide)⟩
private def endpoint_12_49_flag : Flag := ⟨12, 49, 3654⟩
private def endpoint_12_49_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_49_base : receiptBase endpoint_12_49_flag endpoint_12_49_sources = some 257132102579926848 := by decide +kernel
private theorem endpoint_12_49_w0 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 2 257132102579926848 = some 257132102579926848 := by decide +kernel
private theorem endpoint_12_49_w2 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 2 2 257132102579926848 = some 257132102579926848 := by decide +kernel
private theorem endpoint_12_49_p4 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 4 257132102579926848 = some 257132102579926848 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 2 2 257132102579926848 257132102579926848 257132102579926848 endpoint_12_49_w0 endpoint_12_49_w2
private theorem endpoint_12_49_w4 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 4 2 257132102579926848 = some 257132102579926848 := by decide +kernel
private theorem endpoint_12_49_p6 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 6 257132102579926848 = some 257132102579926848 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 4 2 257132102579926848 257132102579926848 257132102579926848 endpoint_12_49_p4 endpoint_12_49_w4
private theorem endpoint_12_49_w6 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 6 2 257132102579926848 = some 257132102579926848 := by decide +kernel
private theorem endpoint_12_49_p8 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 8 257132102579926848 = some 257132102579926848 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 6 2 257132102579926848 257132102579926848 257132102579926848 endpoint_12_49_p6 endpoint_12_49_w6
private theorem endpoint_12_49_w8 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 8 2 257132102579926848 = some 257132102579926848 := by decide +kernel
private theorem endpoint_12_49_p10 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 10 257132102579926848 = some 257132102579926848 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 8 2 257132102579926848 257132102579926848 257132102579926848 endpoint_12_49_p8 endpoint_12_49_w8
private theorem endpoint_12_49_w10 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 10 1 257132102579926848 = some 257132102579926848 := by decide +kernel
private theorem endpoint_12_49_p11 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 11 257132102579926848 = some 257132102579926848 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 10 1 257132102579926848 257132102579926848 257132102579926848 endpoint_12_49_p10 endpoint_12_49_w10
def endpoint_12_49 : CertifiedEndpoint :=
  ⟨⟨12, 49, 3654⟩, 257132102579926848, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_49_flag endpoint_12_49_sources 11 257132102579926848 257132102579926848 rfl endpoint_12_49_base endpoint_12_49_p11) (by decide)⟩
private def endpoint_12_50_flag : Flag := ⟨12, 50, 3615⟩
private def endpoint_12_50_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_50_base : receiptBase endpoint_12_50_flag endpoint_12_50_sources = some 258912344940597851 := by decide +kernel
private theorem endpoint_12_50_w0 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 2 258912344940597851 = some 258912344940597851 := by decide +kernel
private theorem endpoint_12_50_w2 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 2 2 258912344940597851 = some 258912344940597851 := by decide +kernel
private theorem endpoint_12_50_p4 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 4 258912344940597851 = some 258912344940597851 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 2 2 258912344940597851 258912344940597851 258912344940597851 endpoint_12_50_w0 endpoint_12_50_w2
private theorem endpoint_12_50_w4 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 4 2 258912344940597851 = some 258912344940597851 := by decide +kernel
private theorem endpoint_12_50_p6 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 6 258912344940597851 = some 258912344940597851 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 4 2 258912344940597851 258912344940597851 258912344940597851 endpoint_12_50_p4 endpoint_12_50_w4
private theorem endpoint_12_50_w6 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 6 2 258912344940597851 = some 258912344940597851 := by decide +kernel
private theorem endpoint_12_50_p8 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 8 258912344940597851 = some 258912344940597851 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 6 2 258912344940597851 258912344940597851 258912344940597851 endpoint_12_50_p6 endpoint_12_50_w6
private theorem endpoint_12_50_w8 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 8 2 258912344940597851 = some 258912344940597851 := by decide +kernel
private theorem endpoint_12_50_p10 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 10 258912344940597851 = some 258912344940597851 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 8 2 258912344940597851 258912344940597851 258912344940597851 endpoint_12_50_p8 endpoint_12_50_w8
private theorem endpoint_12_50_w10 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 10 1 258912344940597851 = some 258912344940597851 := by decide +kernel
private theorem endpoint_12_50_p11 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 11 258912344940597851 = some 258912344940597851 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 10 1 258912344940597851 258912344940597851 258912344940597851 endpoint_12_50_p10 endpoint_12_50_w10
def endpoint_12_50 : CertifiedEndpoint :=
  ⟨⟨12, 50, 3615⟩, 258912344940597851, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_50_flag endpoint_12_50_sources 11 258912344940597851 258912344940597851 rfl endpoint_12_50_base endpoint_12_50_p11) (by decide)⟩
private def endpoint_12_51_flag : Flag := ⟨12, 51, 3575⟩
private def endpoint_12_51_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_51_base : receiptBase endpoint_12_51_flag endpoint_12_51_sources = some 260524358313666642 := by decide +kernel
private theorem endpoint_12_51_w0 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 2 260524358313666642 = some 260524358313666642 := by decide +kernel
private theorem endpoint_12_51_w2 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 2 2 260524358313666642 = some 260524358313666642 := by decide +kernel
private theorem endpoint_12_51_p4 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 4 260524358313666642 = some 260524358313666642 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 2 2 260524358313666642 260524358313666642 260524358313666642 endpoint_12_51_w0 endpoint_12_51_w2
private theorem endpoint_12_51_w4 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 4 2 260524358313666642 = some 260524358313666642 := by decide +kernel
private theorem endpoint_12_51_p6 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 6 260524358313666642 = some 260524358313666642 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 4 2 260524358313666642 260524358313666642 260524358313666642 endpoint_12_51_p4 endpoint_12_51_w4
private theorem endpoint_12_51_w6 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 6 2 260524358313666642 = some 260524358313666642 := by decide +kernel
private theorem endpoint_12_51_p8 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 8 260524358313666642 = some 260524358313666642 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 6 2 260524358313666642 260524358313666642 260524358313666642 endpoint_12_51_p6 endpoint_12_51_w6
private theorem endpoint_12_51_w8 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 8 2 260524358313666642 = some 260524358313666642 := by decide +kernel
private theorem endpoint_12_51_p10 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 10 260524358313666642 = some 260524358313666642 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 8 2 260524358313666642 260524358313666642 260524358313666642 endpoint_12_51_p8 endpoint_12_51_w8
private theorem endpoint_12_51_w10 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 10 1 260524358313666642 = some 260524358313666642 := by decide +kernel
private theorem endpoint_12_51_p11 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 11 260524358313666642 = some 260524358313666642 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 10 1 260524358313666642 260524358313666642 260524358313666642 endpoint_12_51_p10 endpoint_12_51_w10
def endpoint_12_51 : CertifiedEndpoint :=
  ⟨⟨12, 51, 3575⟩, 260524358313666642, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_51_flag endpoint_12_51_sources 11 260524358313666642 260524358313666642 rfl endpoint_12_51_base endpoint_12_51_p11) (by decide)⟩
private def endpoint_12_52_flag : Flag := ⟨12, 52, 3535⟩
private def endpoint_12_52_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_12_52_base : receiptBase endpoint_12_52_flag endpoint_12_52_sources = some 263032565072375418 := by decide +kernel
private theorem endpoint_12_52_w0 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 2 263032565072375418 = some 263032565072375418 := by decide +kernel
private theorem endpoint_12_52_w2 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 2 2 263032565072375418 = some 263032565072375418 := by decide +kernel
private theorem endpoint_12_52_p4 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 4 263032565072375418 = some 263032565072375418 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 2 2 263032565072375418 263032565072375418 263032565072375418 endpoint_12_52_w0 endpoint_12_52_w2
private theorem endpoint_12_52_w4 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 4 2 263032565072375418 = some 263032565072375418 := by decide +kernel
private theorem endpoint_12_52_p6 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 6 263032565072375418 = some 263032565072375418 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 4 2 263032565072375418 263032565072375418 263032565072375418 endpoint_12_52_p4 endpoint_12_52_w4
private theorem endpoint_12_52_w6 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 6 2 263032565072375418 = some 263032565072375418 := by decide +kernel
private theorem endpoint_12_52_p8 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 8 263032565072375418 = some 263032565072375418 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 6 2 263032565072375418 263032565072375418 263032565072375418 endpoint_12_52_p6 endpoint_12_52_w6
private theorem endpoint_12_52_w8 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 8 2 263032565072375418 = some 263032565072375418 := by decide +kernel
private theorem endpoint_12_52_p10 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 10 263032565072375418 = some 263032565072375418 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 8 2 263032565072375418 263032565072375418 263032565072375418 endpoint_12_52_p8 endpoint_12_52_w8
private theorem endpoint_12_52_w10 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 10 1 263032565072375418 = some 263032565072375418 := by decide +kernel
private theorem endpoint_12_52_p11 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 11 263032565072375418 = some 263032565072375418 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 10 1 263032565072375418 263032565072375418 263032565072375418 endpoint_12_52_p10 endpoint_12_52_w10
def endpoint_12_52 : CertifiedEndpoint :=
  ⟨⟨12, 52, 3535⟩, 263032565072375418, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_12_52_flag endpoint_12_52_sources 11 263032565072375418 263032565072375418 rfl endpoint_12_52_base endpoint_12_52_p11) (by decide)⟩
private def endpoint_12_53_flag : Flag := ⟨12, 53, 3493⟩
private def endpoint_12_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_53_base : receiptBase endpoint_12_53_flag endpoint_12_53_sources = some 262668551708956374 := by decide +kernel
private theorem endpoint_12_53_w0 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 2 262668551708956374 = some 262668551708956374 := by decide +kernel
private theorem endpoint_12_53_w2 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 2 2 262668551708956374 = some 262668551708956374 := by decide +kernel
private theorem endpoint_12_53_p4 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 4 262668551708956374 = some 262668551708956374 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 2 2 262668551708956374 262668551708956374 262668551708956374 endpoint_12_53_w0 endpoint_12_53_w2
private theorem endpoint_12_53_w4 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 4 2 262668551708956374 = some 262668551708956374 := by decide +kernel
private theorem endpoint_12_53_p6 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 6 262668551708956374 = some 262668551708956374 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 4 2 262668551708956374 262668551708956374 262668551708956374 endpoint_12_53_p4 endpoint_12_53_w4
private theorem endpoint_12_53_w6 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 6 2 262668551708956374 = some 262668551708956374 := by decide +kernel
private theorem endpoint_12_53_p8 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 8 262668551708956374 = some 262668551708956374 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 6 2 262668551708956374 262668551708956374 262668551708956374 endpoint_12_53_p6 endpoint_12_53_w6
private theorem endpoint_12_53_w8 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 8 2 262668551708956374 = some 262668551708956374 := by decide +kernel
private theorem endpoint_12_53_p10 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 10 262668551708956374 = some 262668551708956374 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 8 2 262668551708956374 262668551708956374 262668551708956374 endpoint_12_53_p8 endpoint_12_53_w8
private theorem endpoint_12_53_w10 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 10 1 262668551708956374 = some 262668551708956374 := by decide +kernel
private theorem endpoint_12_53_p11 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 11 262668551708956374 = some 262668551708956374 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 10 1 262668551708956374 262668551708956374 262668551708956374 endpoint_12_53_p10 endpoint_12_53_w10
def endpoint_12_53 : CertifiedEndpoint :=
  ⟨⟨12, 53, 3493⟩, 262668551708956374, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_53_flag endpoint_12_53_sources 11 262668551708956374 262668551708956374 rfl endpoint_12_53_base endpoint_12_53_p11) (by decide)⟩
private def endpoint_12_54_flag : Flag := ⟨12, 54, 3449⟩
private def endpoint_12_54_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_54_base : receiptBase endpoint_12_54_flag endpoint_12_54_sources = some 263672727758788172 := by decide +kernel
private theorem endpoint_12_54_w0 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 2 263672727758788172 = some 263672727758788172 := by decide +kernel
private theorem endpoint_12_54_w2 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 2 2 263672727758788172 = some 263672727758788172 := by decide +kernel
private theorem endpoint_12_54_p4 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 4 263672727758788172 = some 263672727758788172 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 2 2 263672727758788172 263672727758788172 263672727758788172 endpoint_12_54_w0 endpoint_12_54_w2
private theorem endpoint_12_54_w4 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 4 2 263672727758788172 = some 263672727758788172 := by decide +kernel
private theorem endpoint_12_54_p6 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 6 263672727758788172 = some 263672727758788172 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 4 2 263672727758788172 263672727758788172 263672727758788172 endpoint_12_54_p4 endpoint_12_54_w4
private theorem endpoint_12_54_w6 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 6 2 263672727758788172 = some 263672727758788172 := by decide +kernel
private theorem endpoint_12_54_p8 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 8 263672727758788172 = some 263672727758788172 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 6 2 263672727758788172 263672727758788172 263672727758788172 endpoint_12_54_p6 endpoint_12_54_w6
private theorem endpoint_12_54_w8 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 8 2 263672727758788172 = some 263672727758788172 := by decide +kernel
private theorem endpoint_12_54_p10 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 10 263672727758788172 = some 263672727758788172 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 8 2 263672727758788172 263672727758788172 263672727758788172 endpoint_12_54_p8 endpoint_12_54_w8
private theorem endpoint_12_54_w10 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 10 1 263672727758788172 = some 263672727758788172 := by decide +kernel
private theorem endpoint_12_54_p11 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 11 263672727758788172 = some 263672727758788172 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 10 1 263672727758788172 263672727758788172 263672727758788172 endpoint_12_54_p10 endpoint_12_54_w10
def endpoint_12_54 : CertifiedEndpoint :=
  ⟨⟨12, 54, 3449⟩, 263672727758788172, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_54_flag endpoint_12_54_sources 11 263672727758788172 263672727758788172 rfl endpoint_12_54_base endpoint_12_54_p11) (by decide)⟩
private def endpoint_12_55_flag : Flag := ⟨12, 55, 3405⟩
private def endpoint_12_55_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_12_55_base : receiptBase endpoint_12_55_flag endpoint_12_55_sources = some 263816170280678089 := by decide +kernel
private theorem endpoint_12_55_w0 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 2 263816170280678089 = some 263816170280678089 := by decide +kernel
private theorem endpoint_12_55_w2 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 2 2 263816170280678089 = some 263816170280678089 := by decide +kernel
private theorem endpoint_12_55_p4 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 4 263816170280678089 = some 263816170280678089 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 2 2 263816170280678089 263816170280678089 263816170280678089 endpoint_12_55_w0 endpoint_12_55_w2
private theorem endpoint_12_55_w4 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 4 2 263816170280678089 = some 263816170280678089 := by decide +kernel
private theorem endpoint_12_55_p6 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 6 263816170280678089 = some 263816170280678089 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 4 2 263816170280678089 263816170280678089 263816170280678089 endpoint_12_55_p4 endpoint_12_55_w4
private theorem endpoint_12_55_w6 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 6 2 263816170280678089 = some 263816170280678089 := by decide +kernel
private theorem endpoint_12_55_p8 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 8 263816170280678089 = some 263816170280678089 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 6 2 263816170280678089 263816170280678089 263816170280678089 endpoint_12_55_p6 endpoint_12_55_w6
private theorem endpoint_12_55_w8 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 8 2 263816170280678089 = some 263816170280678089 := by decide +kernel
private theorem endpoint_12_55_p10 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 10 263816170280678089 = some 263816170280678089 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 8 2 263816170280678089 263816170280678089 263816170280678089 endpoint_12_55_p8 endpoint_12_55_w8
private theorem endpoint_12_55_w10 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 10 1 263816170280678089 = some 263816170280678089 := by decide +kernel
private theorem endpoint_12_55_p11 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 11 263816170280678089 = some 263816170280678089 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 10 1 263816170280678089 263816170280678089 263816170280678089 endpoint_12_55_p10 endpoint_12_55_w10
def endpoint_12_55 : CertifiedEndpoint :=
  ⟨⟨12, 55, 3405⟩, 263816170280678089, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_12_55_flag endpoint_12_55_sources 11 263816170280678089 263816170280678089 rfl endpoint_12_55_base endpoint_12_55_p11) (by decide)⟩
private def endpoint_12_56_flag : Flag := ⟨12, 56, 3359⟩
private def endpoint_12_56_sources : Sources := ⟨contact00, contact35, contact36⟩
private theorem endpoint_12_56_base : receiptBase endpoint_12_56_flag endpoint_12_56_sources = some 264552798461505874 := by decide +kernel
private theorem endpoint_12_56_w0 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 2 264552798461505874 = some 264552798461505874 := by decide +kernel
private theorem endpoint_12_56_w2 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 2 2 264552798461505874 = some 264552798461505874 := by decide +kernel
private theorem endpoint_12_56_p4 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 4 264552798461505874 = some 264552798461505874 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 2 2 264552798461505874 264552798461505874 264552798461505874 endpoint_12_56_w0 endpoint_12_56_w2
private theorem endpoint_12_56_w4 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 4 2 264552798461505874 = some 264552798461505874 := by decide +kernel
private theorem endpoint_12_56_p6 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 6 264552798461505874 = some 264552798461505874 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 4 2 264552798461505874 264552798461505874 264552798461505874 endpoint_12_56_p4 endpoint_12_56_w4
private theorem endpoint_12_56_w6 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 6 2 264552798461505874 = some 264552798461505874 := by decide +kernel
private theorem endpoint_12_56_p8 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 8 264552798461505874 = some 264552798461505874 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 6 2 264552798461505874 264552798461505874 264552798461505874 endpoint_12_56_p6 endpoint_12_56_w6
private theorem endpoint_12_56_w8 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 8 2 264552798461505874 = some 264552798461505874 := by decide +kernel
private theorem endpoint_12_56_p10 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 10 264552798461505874 = some 264552798461505874 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 8 2 264552798461505874 264552798461505874 264552798461505874 endpoint_12_56_p8 endpoint_12_56_w8
private theorem endpoint_12_56_w10 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 10 1 264552798461505874 = some 264552798461505874 := by decide +kernel
private theorem endpoint_12_56_p11 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 11 264552798461505874 = some 264552798461505874 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 10 1 264552798461505874 264552798461505874 264552798461505874 endpoint_12_56_p10 endpoint_12_56_w10
def endpoint_12_56 : CertifiedEndpoint :=
  ⟨⟨12, 56, 3359⟩, 264552798461505874, .terminal ⟨contact00, contact35, contact36⟩ (finish_receipt_window endpoint_12_56_flag endpoint_12_56_sources 11 264552798461505874 264552798461505874 rfl endpoint_12_56_base endpoint_12_56_p11) (by decide)⟩
private def endpoint_12_57_flag : Flag := ⟨12, 57, 3311⟩
private def endpoint_12_57_sources : Sources := ⟨contact00, contact35, contact36⟩
private theorem endpoint_12_57_base : receiptBase endpoint_12_57_flag endpoint_12_57_sources = some 264894284764946908 := by decide +kernel
private theorem endpoint_12_57_w0 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 2 264894284764946908 = some 264894284764946908 := by decide +kernel
private theorem endpoint_12_57_w2 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 2 2 264894284764946908 = some 264894284764946908 := by decide +kernel
private theorem endpoint_12_57_p4 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 4 264894284764946908 = some 264894284764946908 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 2 2 264894284764946908 264894284764946908 264894284764946908 endpoint_12_57_w0 endpoint_12_57_w2
private theorem endpoint_12_57_w4 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 4 2 264894284764946908 = some 264894284764946908 := by decide +kernel
private theorem endpoint_12_57_p6 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 6 264894284764946908 = some 264894284764946908 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 4 2 264894284764946908 264894284764946908 264894284764946908 endpoint_12_57_p4 endpoint_12_57_w4
private theorem endpoint_12_57_w6 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 6 2 264894284764946908 = some 264894284764946908 := by decide +kernel
private theorem endpoint_12_57_p8 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 8 264894284764946908 = some 264894284764946908 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 6 2 264894284764946908 264894284764946908 264894284764946908 endpoint_12_57_p6 endpoint_12_57_w6
private theorem endpoint_12_57_w8 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 8 2 264894284764946908 = some 264894284764946908 := by decide +kernel
private theorem endpoint_12_57_p10 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 10 264894284764946908 = some 264894284764946908 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 8 2 264894284764946908 264894284764946908 264894284764946908 endpoint_12_57_p8 endpoint_12_57_w8
private theorem endpoint_12_57_w10 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 10 1 264894284764946908 = some 264894284764946908 := by decide +kernel
private theorem endpoint_12_57_p11 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 11 264894284764946908 = some 264894284764946908 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 10 1 264894284764946908 264894284764946908 264894284764946908 endpoint_12_57_p10 endpoint_12_57_w10
def endpoint_12_57 : CertifiedEndpoint :=
  ⟨⟨12, 57, 3311⟩, 264894284764946908, .terminal ⟨contact00, contact35, contact36⟩ (finish_receipt_window endpoint_12_57_flag endpoint_12_57_sources 11 264894284764946908 264894284764946908 rfl endpoint_12_57_base endpoint_12_57_p11) (by decide)⟩
private def endpoint_12_58_flag : Flag := ⟨12, 58, 3262⟩
private def endpoint_12_58_sources : Sources := ⟨contact00, contact35, contact36⟩
private theorem endpoint_12_58_base : receiptBase endpoint_12_58_flag endpoint_12_58_sources = some 265037038180007601 := by decide +kernel
private theorem endpoint_12_58_w0 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 2 265037038180007601 = some 265037038180007601 := by decide +kernel
private theorem endpoint_12_58_w2 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 2 2 265037038180007601 = some 265037038180007601 := by decide +kernel
private theorem endpoint_12_58_p4 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 4 265037038180007601 = some 265037038180007601 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 2 2 265037038180007601 265037038180007601 265037038180007601 endpoint_12_58_w0 endpoint_12_58_w2
private theorem endpoint_12_58_w4 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 4 2 265037038180007601 = some 265037038180007601 := by decide +kernel
private theorem endpoint_12_58_p6 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 6 265037038180007601 = some 265037038180007601 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 4 2 265037038180007601 265037038180007601 265037038180007601 endpoint_12_58_p4 endpoint_12_58_w4
private theorem endpoint_12_58_w6 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 6 2 265037038180007601 = some 265037038180007601 := by decide +kernel
private theorem endpoint_12_58_p8 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 8 265037038180007601 = some 265037038180007601 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 6 2 265037038180007601 265037038180007601 265037038180007601 endpoint_12_58_p6 endpoint_12_58_w6
private theorem endpoint_12_58_w8 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 8 2 265037038180007601 = some 265037038180007601 := by decide +kernel
private theorem endpoint_12_58_p10 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 10 265037038180007601 = some 265037038180007601 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 8 2 265037038180007601 265037038180007601 265037038180007601 endpoint_12_58_p8 endpoint_12_58_w8
private theorem endpoint_12_58_w10 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 10 1 265037038180007601 = some 265037038180007601 := by decide +kernel
private theorem endpoint_12_58_p11 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 11 265037038180007601 = some 265037038180007601 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 10 1 265037038180007601 265037038180007601 265037038180007601 endpoint_12_58_p10 endpoint_12_58_w10
def endpoint_12_58 : CertifiedEndpoint :=
  ⟨⟨12, 58, 3262⟩, 265037038180007601, .terminal ⟨contact00, contact35, contact36⟩ (finish_receipt_window endpoint_12_58_flag endpoint_12_58_sources 11 265037038180007601 265037038180007601 rfl endpoint_12_58_base endpoint_12_58_p11) (by decide)⟩
private def endpoint_12_59_flag : Flag := ⟨12, 59, 3210⟩
private def endpoint_12_59_sources : Sources := ⟨contact00, contact35, contact36⟩
private theorem endpoint_12_59_base : receiptBase endpoint_12_59_flag endpoint_12_59_sources = some 264814389230833309 := by decide +kernel
private theorem endpoint_12_59_w0 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 2 264814389230833309 = some 264814389230833309 := by decide +kernel
private theorem endpoint_12_59_w2 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 2 2 264814389230833309 = some 264814389230833309 := by decide +kernel
private theorem endpoint_12_59_p4 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 4 264814389230833309 = some 264814389230833309 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 2 2 264814389230833309 264814389230833309 264814389230833309 endpoint_12_59_w0 endpoint_12_59_w2
private theorem endpoint_12_59_w4 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 4 2 264814389230833309 = some 264814389230833309 := by decide +kernel
private theorem endpoint_12_59_p6 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 6 264814389230833309 = some 264814389230833309 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 4 2 264814389230833309 264814389230833309 264814389230833309 endpoint_12_59_p4 endpoint_12_59_w4
private theorem endpoint_12_59_w6 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 6 2 264814389230833309 = some 264814389230833309 := by decide +kernel
private theorem endpoint_12_59_p8 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 8 264814389230833309 = some 264814389230833309 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 6 2 264814389230833309 264814389230833309 264814389230833309 endpoint_12_59_p6 endpoint_12_59_w6
private theorem endpoint_12_59_w8 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 8 2 264814389230833309 = some 264814389230833309 := by decide +kernel
private theorem endpoint_12_59_p10 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 10 264814389230833309 = some 264814389230833309 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 8 2 264814389230833309 264814389230833309 264814389230833309 endpoint_12_59_p8 endpoint_12_59_w8
private theorem endpoint_12_59_w10 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 10 1 264814389230833309 = some 264814389230833309 := by decide +kernel
private theorem endpoint_12_59_p11 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 11 264814389230833309 = some 264814389230833309 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 10 1 264814389230833309 264814389230833309 264814389230833309 endpoint_12_59_p10 endpoint_12_59_w10
def endpoint_12_59 : CertifiedEndpoint :=
  ⟨⟨12, 59, 3210⟩, 264814389230833309, .terminal ⟨contact00, contact35, contact36⟩ (finish_receipt_window endpoint_12_59_flag endpoint_12_59_sources 11 264814389230833309 264814389230833309 rfl endpoint_12_59_base endpoint_12_59_p11) (by decide)⟩
private def endpoint_12_60_flag : Flag := ⟨12, 60, 3157⟩
private def endpoint_12_60_sources : Sources := ⟨contact00, contact35, contact36⟩
private theorem endpoint_12_60_base : receiptBase endpoint_12_60_flag endpoint_12_60_sources = some 264380795472637613 := by decide +kernel
private theorem endpoint_12_60_w0 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 2 264380795472637613 = some 264380795472637613 := by decide +kernel
private theorem endpoint_12_60_w2 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 2 2 264380795472637613 = some 264380795472637613 := by decide +kernel
private theorem endpoint_12_60_p4 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 4 264380795472637613 = some 264380795472637613 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 2 2 264380795472637613 264380795472637613 264380795472637613 endpoint_12_60_w0 endpoint_12_60_w2
private theorem endpoint_12_60_w4 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 4 2 264380795472637613 = some 264380795472637613 := by decide +kernel
private theorem endpoint_12_60_p6 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 6 264380795472637613 = some 264380795472637613 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 4 2 264380795472637613 264380795472637613 264380795472637613 endpoint_12_60_p4 endpoint_12_60_w4
private theorem endpoint_12_60_w6 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 6 2 264380795472637613 = some 264380795472637613 := by decide +kernel
private theorem endpoint_12_60_p8 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 8 264380795472637613 = some 264380795472637613 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 6 2 264380795472637613 264380795472637613 264380795472637613 endpoint_12_60_p6 endpoint_12_60_w6
private theorem endpoint_12_60_w8 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 8 2 264380795472637613 = some 264380795472637613 := by decide +kernel
private theorem endpoint_12_60_p10 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 10 264380795472637613 = some 264380795472637613 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 8 2 264380795472637613 264380795472637613 264380795472637613 endpoint_12_60_p8 endpoint_12_60_w8
private theorem endpoint_12_60_w10 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 10 1 264380795472637613 = some 264380795472637613 := by decide +kernel
private theorem endpoint_12_60_p11 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 11 264380795472637613 = some 264380795472637613 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 10 1 264380795472637613 264380795472637613 264380795472637613 endpoint_12_60_p10 endpoint_12_60_w10
def endpoint_12_60 : CertifiedEndpoint :=
  ⟨⟨12, 60, 3157⟩, 264380795472637613, .terminal ⟨contact00, contact35, contact36⟩ (finish_receipt_window endpoint_12_60_flag endpoint_12_60_sources 11 264380795472637613 264380795472637613 rfl endpoint_12_60_base endpoint_12_60_p11) (by decide)⟩
private def endpoint_12_61_flag : Flag := ⟨12, 61, 3101⟩
private def endpoint_12_61_sources : Sources := ⟨contact00, contact01, contact36⟩
private theorem endpoint_12_61_base : receiptBase endpoint_12_61_flag endpoint_12_61_sources = some 263781887059404251 := by decide +kernel
private theorem endpoint_12_61_w0 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 2 263781887059404251 = some 263781887059404251 := by decide +kernel
private theorem endpoint_12_61_w2 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 2 2 263781887059404251 = some 263781887059404251 := by decide +kernel
private theorem endpoint_12_61_p4 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 4 263781887059404251 = some 263781887059404251 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 2 2 263781887059404251 263781887059404251 263781887059404251 endpoint_12_61_w0 endpoint_12_61_w2
private theorem endpoint_12_61_w4 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 4 2 263781887059404251 = some 263781887059404251 := by decide +kernel
private theorem endpoint_12_61_p6 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 6 263781887059404251 = some 263781887059404251 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 4 2 263781887059404251 263781887059404251 263781887059404251 endpoint_12_61_p4 endpoint_12_61_w4
private theorem endpoint_12_61_w6 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 6 2 263781887059404251 = some 263781887059404251 := by decide +kernel
private theorem endpoint_12_61_p8 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 8 263781887059404251 = some 263781887059404251 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 6 2 263781887059404251 263781887059404251 263781887059404251 endpoint_12_61_p6 endpoint_12_61_w6
private theorem endpoint_12_61_w8 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 8 2 263781887059404251 = some 263781887059404251 := by decide +kernel
private theorem endpoint_12_61_p10 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 10 263781887059404251 = some 263781887059404251 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 8 2 263781887059404251 263781887059404251 263781887059404251 endpoint_12_61_p8 endpoint_12_61_w8
private theorem endpoint_12_61_w10 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 10 1 263781887059404251 = some 263781887059404251 := by decide +kernel
private theorem endpoint_12_61_p11 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 11 263781887059404251 = some 263781887059404251 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 10 1 263781887059404251 263781887059404251 263781887059404251 endpoint_12_61_p10 endpoint_12_61_w10
def endpoint_12_61 : CertifiedEndpoint :=
  ⟨⟨12, 61, 3101⟩, 263781887059404251, .terminal ⟨contact00, contact01, contact36⟩ (finish_receipt_window endpoint_12_61_flag endpoint_12_61_sources 11 263781887059404251 263781887059404251 rfl endpoint_12_61_base endpoint_12_61_p11) (by decide)⟩
private def endpoint_12_62_flag : Flag := ⟨12, 62, 3042⟩
private def endpoint_12_62_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_62_base : receiptBase endpoint_12_62_flag endpoint_12_62_sources = some 263805630900562851 := by decide +kernel
private theorem endpoint_12_62_w0 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 2 263805630900562851 = some 263805630900562851 := by decide +kernel
private theorem endpoint_12_62_w2 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 2 2 263805630900562851 = some 263805630900562851 := by decide +kernel
private theorem endpoint_12_62_p4 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 4 263805630900562851 = some 263805630900562851 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 2 2 263805630900562851 263805630900562851 263805630900562851 endpoint_12_62_w0 endpoint_12_62_w2
private theorem endpoint_12_62_w4 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 4 2 263805630900562851 = some 263805630900562851 := by decide +kernel
private theorem endpoint_12_62_p6 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 6 263805630900562851 = some 263805630900562851 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 4 2 263805630900562851 263805630900562851 263805630900562851 endpoint_12_62_p4 endpoint_12_62_w4
private theorem endpoint_12_62_w6 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 6 2 263805630900562851 = some 263805630900562851 := by decide +kernel
private theorem endpoint_12_62_p8 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 8 263805630900562851 = some 263805630900562851 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 6 2 263805630900562851 263805630900562851 263805630900562851 endpoint_12_62_p6 endpoint_12_62_w6
private theorem endpoint_12_62_w8 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 8 2 263805630900562851 = some 263805630900562851 := by decide +kernel
private theorem endpoint_12_62_p10 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 10 263805630900562851 = some 263805630900562851 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 8 2 263805630900562851 263805630900562851 263805630900562851 endpoint_12_62_p8 endpoint_12_62_w8
private theorem endpoint_12_62_w10 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 10 1 263805630900562851 = some 263805630900562851 := by decide +kernel
private theorem endpoint_12_62_p11 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 11 263805630900562851 = some 263805630900562851 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 10 1 263805630900562851 263805630900562851 263805630900562851 endpoint_12_62_p10 endpoint_12_62_w10
def endpoint_12_62 : CertifiedEndpoint :=
  ⟨⟨12, 62, 3042⟩, 263805630900562851, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_62_flag endpoint_12_62_sources 11 263805630900562851 263805630900562851 rfl endpoint_12_62_base endpoint_12_62_p11) (by decide)⟩
private def endpoint_12_63_flag : Flag := ⟨12, 63, 2981⟩
private def endpoint_12_63_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_12_63_base : receiptBase endpoint_12_63_flag endpoint_12_63_sources = some 262578272893871560 := by decide +kernel
private theorem endpoint_12_63_w0 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 2 262578272893871560 = some 262578272893871560 := by decide +kernel
private theorem endpoint_12_63_w2 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 2 2 262578272893871560 = some 262578272893871560 := by decide +kernel
private theorem endpoint_12_63_p4 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 4 262578272893871560 = some 262578272893871560 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 2 2 262578272893871560 262578272893871560 262578272893871560 endpoint_12_63_w0 endpoint_12_63_w2
private theorem endpoint_12_63_w4 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 4 2 262578272893871560 = some 262578272893871560 := by decide +kernel
private theorem endpoint_12_63_p6 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 6 262578272893871560 = some 262578272893871560 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 4 2 262578272893871560 262578272893871560 262578272893871560 endpoint_12_63_p4 endpoint_12_63_w4
private theorem endpoint_12_63_w6 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 6 2 262578272893871560 = some 262578272893871560 := by decide +kernel
private theorem endpoint_12_63_p8 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 8 262578272893871560 = some 262578272893871560 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 6 2 262578272893871560 262578272893871560 262578272893871560 endpoint_12_63_p6 endpoint_12_63_w6
private theorem endpoint_12_63_w8 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 8 2 262578272893871560 = some 262578272893871560 := by decide +kernel
private theorem endpoint_12_63_p10 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 10 262578272893871560 = some 262578272893871560 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 8 2 262578272893871560 262578272893871560 262578272893871560 endpoint_12_63_p8 endpoint_12_63_w8
private theorem endpoint_12_63_w10 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 10 1 262578272893871560 = some 262578272893871560 := by decide +kernel
private theorem endpoint_12_63_p11 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 11 262578272893871560 = some 262578272893871560 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 10 1 262578272893871560 262578272893871560 262578272893871560 endpoint_12_63_p10 endpoint_12_63_w10
def endpoint_12_63 : CertifiedEndpoint :=
  ⟨⟨12, 63, 2981⟩, 262578272893871560, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_12_63_flag endpoint_12_63_sources 11 262578272893871560 262578272893871560 rfl endpoint_12_63_base endpoint_12_63_p11) (by decide)⟩
private def endpoint_12_64_flag : Flag := ⟨12, 64, 2917⟩
private def endpoint_12_64_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_12_64_base : receiptBase endpoint_12_64_flag endpoint_12_64_sources = some 260643083506223100 := by decide +kernel
private theorem endpoint_12_64_w0 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 2 260643083506223100 = some 260643083506223100 := by decide +kernel
private theorem endpoint_12_64_w2 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 2 2 260643083506223100 = some 260643083506223100 := by decide +kernel
private theorem endpoint_12_64_p4 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 4 260643083506223100 = some 260643083506223100 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 2 2 260643083506223100 260643083506223100 260643083506223100 endpoint_12_64_w0 endpoint_12_64_w2
private theorem endpoint_12_64_w4 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 4 2 260643083506223100 = some 260643083506223100 := by decide +kernel
private theorem endpoint_12_64_p6 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 6 260643083506223100 = some 260643083506223100 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 4 2 260643083506223100 260643083506223100 260643083506223100 endpoint_12_64_p4 endpoint_12_64_w4
private theorem endpoint_12_64_w6 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 6 2 260643083506223100 = some 260643083506223100 := by decide +kernel
private theorem endpoint_12_64_p8 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 8 260643083506223100 = some 260643083506223100 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 6 2 260643083506223100 260643083506223100 260643083506223100 endpoint_12_64_p6 endpoint_12_64_w6
private theorem endpoint_12_64_w8 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 8 2 260643083506223100 = some 260643083506223100 := by decide +kernel
private theorem endpoint_12_64_p10 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 10 260643083506223100 = some 260643083506223100 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 8 2 260643083506223100 260643083506223100 260643083506223100 endpoint_12_64_p8 endpoint_12_64_w8
private theorem endpoint_12_64_w10 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 10 1 260643083506223100 = some 260643083506223100 := by decide +kernel
private theorem endpoint_12_64_p11 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 11 260643083506223100 = some 260643083506223100 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 10 1 260643083506223100 260643083506223100 260643083506223100 endpoint_12_64_p10 endpoint_12_64_w10
def endpoint_12_64 : CertifiedEndpoint :=
  ⟨⟨12, 64, 2917⟩, 260643083506223100, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_12_64_flag endpoint_12_64_sources 11 260643083506223100 260643083506223100 rfl endpoint_12_64_base endpoint_12_64_p11) (by decide)⟩
private def endpoint_12_65_flag : Flag := ⟨12, 65, 2851⟩
private def endpoint_12_65_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_12_65_base : receiptBase endpoint_12_65_flag endpoint_12_65_sources = some 261056795442017350 := by decide +kernel
private theorem endpoint_12_65_w0 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 2 261056795442017350 = some 261056795442017350 := by decide +kernel
private theorem endpoint_12_65_w2 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 2 2 261056795442017350 = some 261056795442017350 := by decide +kernel
private theorem endpoint_12_65_p4 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 4 261056795442017350 = some 261056795442017350 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 2 2 261056795442017350 261056795442017350 261056795442017350 endpoint_12_65_w0 endpoint_12_65_w2
private theorem endpoint_12_65_w4 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 4 2 261056795442017350 = some 261056795442017350 := by decide +kernel
private theorem endpoint_12_65_p6 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 6 261056795442017350 = some 261056795442017350 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 4 2 261056795442017350 261056795442017350 261056795442017350 endpoint_12_65_p4 endpoint_12_65_w4
private theorem endpoint_12_65_w6 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 6 2 261056795442017350 = some 261056795442017350 := by decide +kernel
private theorem endpoint_12_65_p8 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 8 261056795442017350 = some 261056795442017350 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 6 2 261056795442017350 261056795442017350 261056795442017350 endpoint_12_65_p6 endpoint_12_65_w6
private theorem endpoint_12_65_w8 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 8 2 261056795442017350 = some 261056795442017350 := by decide +kernel
private theorem endpoint_12_65_p10 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 10 261056795442017350 = some 261056795442017350 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 8 2 261056795442017350 261056795442017350 261056795442017350 endpoint_12_65_p8 endpoint_12_65_w8
private theorem endpoint_12_65_w10 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 10 1 261056795442017350 = some 261056795442017350 := by decide +kernel
private theorem endpoint_12_65_p11 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 11 261056795442017350 = some 261056795442017350 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 10 1 261056795442017350 261056795442017350 261056795442017350 endpoint_12_65_p10 endpoint_12_65_w10
def endpoint_12_65 : CertifiedEndpoint :=
  ⟨⟨12, 65, 2851⟩, 261056795442017350, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_12_65_flag endpoint_12_65_sources 11 261056795442017350 261056795442017350 rfl endpoint_12_65_base endpoint_12_65_p11) (by decide)⟩
private def endpoint_12_66_flag : Flag := ⟨12, 66, 2781⟩
private def endpoint_12_66_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_66_base : receiptBase endpoint_12_66_flag endpoint_12_66_sources = some 263324809755076603 := by decide +kernel
private theorem endpoint_12_66_w0 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 2 263324809755076603 = some 263324809755076603 := by decide +kernel
private theorem endpoint_12_66_w2 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 2 2 263324809755076603 = some 263324809755076603 := by decide +kernel
private theorem endpoint_12_66_p4 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 4 263324809755076603 = some 263324809755076603 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 2 2 263324809755076603 263324809755076603 263324809755076603 endpoint_12_66_w0 endpoint_12_66_w2
private theorem endpoint_12_66_w4 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 4 2 263324809755076603 = some 263324809755076603 := by decide +kernel
private theorem endpoint_12_66_p6 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 6 263324809755076603 = some 263324809755076603 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 4 2 263324809755076603 263324809755076603 263324809755076603 endpoint_12_66_p4 endpoint_12_66_w4
private theorem endpoint_12_66_w6 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 6 2 263324809755076603 = some 263324809755076603 := by decide +kernel
private theorem endpoint_12_66_p8 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 8 263324809755076603 = some 263324809755076603 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 6 2 263324809755076603 263324809755076603 263324809755076603 endpoint_12_66_p6 endpoint_12_66_w6
private theorem endpoint_12_66_w8 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 8 2 263324809755076603 = some 263324809755076603 := by decide +kernel
private theorem endpoint_12_66_p10 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 10 263324809755076603 = some 263324809755076603 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 8 2 263324809755076603 263324809755076603 263324809755076603 endpoint_12_66_p8 endpoint_12_66_w8
private theorem endpoint_12_66_w10 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 10 1 263324809755076603 = some 263324809755076603 := by decide +kernel
private theorem endpoint_12_66_p11 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 11 263324809755076603 = some 263324809755076603 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 10 1 263324809755076603 263324809755076603 263324809755076603 endpoint_12_66_p10 endpoint_12_66_w10
def endpoint_12_66 : CertifiedEndpoint :=
  ⟨⟨12, 66, 2781⟩, 263324809755076603, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_66_flag endpoint_12_66_sources 11 263324809755076603 263324809755076603 rfl endpoint_12_66_base endpoint_12_66_p11) (by decide)⟩
private def endpoint_12_67_flag : Flag := ⟨12, 67, 2709⟩
private def endpoint_12_67_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_67_base : receiptBase endpoint_12_67_flag endpoint_12_67_sources = some 260040001838582576 := by decide +kernel
private theorem endpoint_12_67_w0 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 2 260040001838582576 = some 260040001838582576 := by decide +kernel
private theorem endpoint_12_67_w2 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 2 2 260040001838582576 = some 260040001838582576 := by decide +kernel
private theorem endpoint_12_67_p4 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 4 260040001838582576 = some 260040001838582576 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 2 2 260040001838582576 260040001838582576 260040001838582576 endpoint_12_67_w0 endpoint_12_67_w2
private theorem endpoint_12_67_w4 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 4 2 260040001838582576 = some 260040001838582576 := by decide +kernel
private theorem endpoint_12_67_p6 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 6 260040001838582576 = some 260040001838582576 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 4 2 260040001838582576 260040001838582576 260040001838582576 endpoint_12_67_p4 endpoint_12_67_w4
private theorem endpoint_12_67_w6 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 6 2 260040001838582576 = some 260040001838582576 := by decide +kernel
private theorem endpoint_12_67_p8 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 8 260040001838582576 = some 260040001838582576 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 6 2 260040001838582576 260040001838582576 260040001838582576 endpoint_12_67_p6 endpoint_12_67_w6
private theorem endpoint_12_67_w8 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 8 2 260040001838582576 = some 260040001838582576 := by decide +kernel
private theorem endpoint_12_67_p10 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 10 260040001838582576 = some 260040001838582576 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 8 2 260040001838582576 260040001838582576 260040001838582576 endpoint_12_67_p8 endpoint_12_67_w8
private theorem endpoint_12_67_w10 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 10 1 260040001838582576 = some 260040001838582576 := by decide +kernel
private theorem endpoint_12_67_p11 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 11 260040001838582576 = some 260040001838582576 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 10 1 260040001838582576 260040001838582576 260040001838582576 endpoint_12_67_p10 endpoint_12_67_w10
def endpoint_12_67 : CertifiedEndpoint :=
  ⟨⟨12, 67, 2709⟩, 260040001838582576, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_67_flag endpoint_12_67_sources 11 260040001838582576 260040001838582576 rfl endpoint_12_67_base endpoint_12_67_p11) (by decide)⟩
private def endpoint_12_68_flag : Flag := ⟨12, 68, 2634⟩
private def endpoint_12_68_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_12_68_base : receiptBase endpoint_12_68_flag endpoint_12_68_sources = some 262023764465267572 := by decide +kernel
private theorem endpoint_12_68_w0 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 2 262023764465267572 = some 262023764465267572 := by decide +kernel
private theorem endpoint_12_68_w2 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 2 2 262023764465267572 = some 262023764465267572 := by decide +kernel
private theorem endpoint_12_68_p4 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 4 262023764465267572 = some 262023764465267572 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 2 2 262023764465267572 262023764465267572 262023764465267572 endpoint_12_68_w0 endpoint_12_68_w2
private theorem endpoint_12_68_w4 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 4 2 262023764465267572 = some 262023764465267572 := by decide +kernel
private theorem endpoint_12_68_p6 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 6 262023764465267572 = some 262023764465267572 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 4 2 262023764465267572 262023764465267572 262023764465267572 endpoint_12_68_p4 endpoint_12_68_w4
private theorem endpoint_12_68_w6 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 6 2 262023764465267572 = some 262023764465267572 := by decide +kernel
private theorem endpoint_12_68_p8 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 8 262023764465267572 = some 262023764465267572 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 6 2 262023764465267572 262023764465267572 262023764465267572 endpoint_12_68_p6 endpoint_12_68_w6
private theorem endpoint_12_68_w8 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 8 2 262023764465267572 = some 262023764465267572 := by decide +kernel
private theorem endpoint_12_68_p10 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 10 262023764465267572 = some 262023764465267572 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 8 2 262023764465267572 262023764465267572 262023764465267572 endpoint_12_68_p8 endpoint_12_68_w8
private theorem endpoint_12_68_w10 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 10 1 262023764465267572 = some 262023764465267572 := by decide +kernel
private theorem endpoint_12_68_p11 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 11 262023764465267572 = some 262023764465267572 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 10 1 262023764465267572 262023764465267572 262023764465267572 endpoint_12_68_p10 endpoint_12_68_w10
def endpoint_12_68 : CertifiedEndpoint :=
  ⟨⟨12, 68, 2634⟩, 262023764465267572, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_12_68_flag endpoint_12_68_sources 11 262023764465267572 262023764465267572 rfl endpoint_12_68_base endpoint_12_68_p11) (by decide)⟩
private def endpoint_12_69_flag : Flag := ⟨12, 69, 2557⟩
private def endpoint_12_69_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_12_69_base : receiptBase endpoint_12_69_flag endpoint_12_69_sources = some 257834580143183457 := by decide +kernel
private theorem endpoint_12_69_w0 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 2 257834580143183457 = some 257834580143183457 := by decide +kernel
private theorem endpoint_12_69_w2 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 2 2 257834580143183457 = some 257834580143183457 := by decide +kernel
private theorem endpoint_12_69_p4 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 4 257834580143183457 = some 257834580143183457 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 2 2 257834580143183457 257834580143183457 257834580143183457 endpoint_12_69_w0 endpoint_12_69_w2
private theorem endpoint_12_69_w4 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 4 2 257834580143183457 = some 257834580143183457 := by decide +kernel
private theorem endpoint_12_69_p6 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 6 257834580143183457 = some 257834580143183457 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 4 2 257834580143183457 257834580143183457 257834580143183457 endpoint_12_69_p4 endpoint_12_69_w4
private theorem endpoint_12_69_w6 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 6 2 257834580143183457 = some 257834580143183457 := by decide +kernel
private theorem endpoint_12_69_p8 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 8 257834580143183457 = some 257834580143183457 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 6 2 257834580143183457 257834580143183457 257834580143183457 endpoint_12_69_p6 endpoint_12_69_w6
private theorem endpoint_12_69_w8 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 8 2 257834580143183457 = some 257834580143183457 := by decide +kernel
private theorem endpoint_12_69_p10 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 10 257834580143183457 = some 257834580143183457 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 8 2 257834580143183457 257834580143183457 257834580143183457 endpoint_12_69_p8 endpoint_12_69_w8
private theorem endpoint_12_69_w10 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 10 1 257834580143183457 = some 257834580143183457 := by decide +kernel
private theorem endpoint_12_69_p11 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 11 257834580143183457 = some 257834580143183457 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 10 1 257834580143183457 257834580143183457 257834580143183457 endpoint_12_69_p10 endpoint_12_69_w10
def endpoint_12_69 : CertifiedEndpoint :=
  ⟨⟨12, 69, 2557⟩, 257834580143183457, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_12_69_flag endpoint_12_69_sources 11 257834580143183457 257834580143183457 rfl endpoint_12_69_base endpoint_12_69_p11) (by decide)⟩
private def endpoint_12_70_flag : Flag := ⟨12, 70, 2476⟩
private def endpoint_12_70_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_12_70_base : receiptBase endpoint_12_70_flag endpoint_12_70_sources = some 253048391171615694 := by decide +kernel
private theorem endpoint_12_70_w0 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 2 253048391171615694 = some 253048391171615694 := by decide +kernel
private theorem endpoint_12_70_w2 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 2 2 253048391171615694 = some 253048391171615694 := by decide +kernel
private theorem endpoint_12_70_p4 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 4 253048391171615694 = some 253048391171615694 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 2 2 253048391171615694 253048391171615694 253048391171615694 endpoint_12_70_w0 endpoint_12_70_w2
private theorem endpoint_12_70_w4 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 4 2 253048391171615694 = some 253048391171615694 := by decide +kernel
private theorem endpoint_12_70_p6 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 6 253048391171615694 = some 253048391171615694 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 4 2 253048391171615694 253048391171615694 253048391171615694 endpoint_12_70_p4 endpoint_12_70_w4
private theorem endpoint_12_70_w6 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 6 2 253048391171615694 = some 253048391171615694 := by decide +kernel
private theorem endpoint_12_70_p8 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 8 253048391171615694 = some 253048391171615694 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 6 2 253048391171615694 253048391171615694 253048391171615694 endpoint_12_70_p6 endpoint_12_70_w6
private theorem endpoint_12_70_w8 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 8 2 253048391171615694 = some 253048391171615694 := by decide +kernel
private theorem endpoint_12_70_p10 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 10 253048391171615694 = some 253048391171615694 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 8 2 253048391171615694 253048391171615694 253048391171615694 endpoint_12_70_p8 endpoint_12_70_w8
private theorem endpoint_12_70_w10 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 10 1 253048391171615694 = some 253048391171615694 := by decide +kernel
private theorem endpoint_12_70_p11 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 11 253048391171615694 = some 253048391171615694 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 10 1 253048391171615694 253048391171615694 253048391171615694 endpoint_12_70_p10 endpoint_12_70_w10
def endpoint_12_70 : CertifiedEndpoint :=
  ⟨⟨12, 70, 2476⟩, 253048391171615694, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_12_70_flag endpoint_12_70_sources 11 253048391171615694 253048391171615694 rfl endpoint_12_70_base endpoint_12_70_p11) (by decide)⟩
private def endpoint_12_71_flag : Flag := ⟨12, 71, 2392⟩
private def endpoint_12_71_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_12_71_base : receiptBase endpoint_12_71_flag endpoint_12_71_sources = some 249337929391195171 := by decide +kernel
private theorem endpoint_12_71_w0 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 2 249337929391195171 = some 249337929391195171 := by decide +kernel
private theorem endpoint_12_71_w2 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 2 2 249337929391195171 = some 249337929391195171 := by decide +kernel
private theorem endpoint_12_71_p4 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 4 249337929391195171 = some 249337929391195171 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 2 2 249337929391195171 249337929391195171 249337929391195171 endpoint_12_71_w0 endpoint_12_71_w2
private theorem endpoint_12_71_w4 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 4 2 249337929391195171 = some 249337929391195171 := by decide +kernel
private theorem endpoint_12_71_p6 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 6 249337929391195171 = some 249337929391195171 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 4 2 249337929391195171 249337929391195171 249337929391195171 endpoint_12_71_p4 endpoint_12_71_w4
private theorem endpoint_12_71_w6 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 6 2 249337929391195171 = some 249337929391195171 := by decide +kernel
private theorem endpoint_12_71_p8 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 8 249337929391195171 = some 249337929391195171 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 6 2 249337929391195171 249337929391195171 249337929391195171 endpoint_12_71_p6 endpoint_12_71_w6
private theorem endpoint_12_71_w8 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 8 2 249337929391195171 = some 249337929391195171 := by decide +kernel
private theorem endpoint_12_71_p10 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 10 249337929391195171 = some 249337929391195171 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 8 2 249337929391195171 249337929391195171 249337929391195171 endpoint_12_71_p8 endpoint_12_71_w8
private theorem endpoint_12_71_w10 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 10 1 249337929391195171 = some 249337929391195171 := by decide +kernel
private theorem endpoint_12_71_p11 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 11 249337929391195171 = some 249337929391195171 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 10 1 249337929391195171 249337929391195171 249337929391195171 endpoint_12_71_p10 endpoint_12_71_w10
def endpoint_12_71 : CertifiedEndpoint :=
  ⟨⟨12, 71, 2392⟩, 249337929391195171, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_12_71_flag endpoint_12_71_sources 11 249337929391195171 249337929391195171 rfl endpoint_12_71_base endpoint_12_71_p11) (by decide)⟩
private def endpoint_12_72_flag : Flag := ⟨12, 72, 2306⟩
private def endpoint_12_72_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_12_72_base : receiptBase endpoint_12_72_flag endpoint_12_72_sources = some 243669692475874078 := by decide +kernel
private theorem endpoint_12_72_w0 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 2 243669692475874078 = some 243669692475874078 := by decide +kernel
private theorem endpoint_12_72_w2 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 2 2 243669692475874078 = some 243669692475874078 := by decide +kernel
private theorem endpoint_12_72_p4 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 4 243669692475874078 = some 243669692475874078 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 2 2 243669692475874078 243669692475874078 243669692475874078 endpoint_12_72_w0 endpoint_12_72_w2
private theorem endpoint_12_72_w4 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 4 2 243669692475874078 = some 243669692475874078 := by decide +kernel
private theorem endpoint_12_72_p6 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 6 243669692475874078 = some 243669692475874078 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 4 2 243669692475874078 243669692475874078 243669692475874078 endpoint_12_72_p4 endpoint_12_72_w4
private theorem endpoint_12_72_w6 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 6 2 243669692475874078 = some 243669692475874078 := by decide +kernel
private theorem endpoint_12_72_p8 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 8 243669692475874078 = some 243669692475874078 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 6 2 243669692475874078 243669692475874078 243669692475874078 endpoint_12_72_p6 endpoint_12_72_w6
private theorem endpoint_12_72_w8 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 8 2 243669692475874078 = some 243669692475874078 := by decide +kernel
private theorem endpoint_12_72_p10 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 10 243669692475874078 = some 243669692475874078 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 8 2 243669692475874078 243669692475874078 243669692475874078 endpoint_12_72_p8 endpoint_12_72_w8
private theorem endpoint_12_72_w10 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 10 1 243669692475874078 = some 243669692475874078 := by decide +kernel
private theorem endpoint_12_72_p11 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 11 243669692475874078 = some 243669692475874078 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 10 1 243669692475874078 243669692475874078 243669692475874078 endpoint_12_72_p10 endpoint_12_72_w10
def endpoint_12_72 : CertifiedEndpoint :=
  ⟨⟨12, 72, 2306⟩, 243669692475874078, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_12_72_flag endpoint_12_72_sources 11 243669692475874078 243669692475874078 rfl endpoint_12_72_base endpoint_12_72_p11) (by decide)⟩
private def endpoint_12_73_flag : Flag := ⟨12, 73, 2216⟩
private def endpoint_12_73_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_12_73_base : receiptBase endpoint_12_73_flag endpoint_12_73_sources = some 238953967524352906 := by decide +kernel
private theorem endpoint_12_73_w0 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 2 238953967524352906 = some 238953967524352906 := by decide +kernel
private theorem endpoint_12_73_w2 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 2 2 238953967524352906 = some 238953967524352906 := by decide +kernel
private theorem endpoint_12_73_p4 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 4 238953967524352906 = some 238953967524352906 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 2 2 238953967524352906 238953967524352906 238953967524352906 endpoint_12_73_w0 endpoint_12_73_w2
private theorem endpoint_12_73_w4 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 4 2 238953967524352906 = some 238953967524352906 := by decide +kernel
private theorem endpoint_12_73_p6 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 6 238953967524352906 = some 238953967524352906 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 4 2 238953967524352906 238953967524352906 238953967524352906 endpoint_12_73_p4 endpoint_12_73_w4
private theorem endpoint_12_73_w6 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 6 2 238953967524352906 = some 238953967524352906 := by decide +kernel
private theorem endpoint_12_73_p8 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 8 238953967524352906 = some 238953967524352906 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 6 2 238953967524352906 238953967524352906 238953967524352906 endpoint_12_73_p6 endpoint_12_73_w6
private theorem endpoint_12_73_w8 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 8 2 238953967524352906 = some 238953967524352906 := by decide +kernel
private theorem endpoint_12_73_p10 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 10 238953967524352906 = some 238953967524352906 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 8 2 238953967524352906 238953967524352906 238953967524352906 endpoint_12_73_p8 endpoint_12_73_w8
private theorem endpoint_12_73_w10 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 10 1 238953967524352906 = some 238953967524352906 := by decide +kernel
private theorem endpoint_12_73_p11 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 11 238953967524352906 = some 238953967524352906 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 10 1 238953967524352906 238953967524352906 238953967524352906 endpoint_12_73_p10 endpoint_12_73_w10
def endpoint_12_73 : CertifiedEndpoint :=
  ⟨⟨12, 73, 2216⟩, 238953967524352906, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_12_73_flag endpoint_12_73_sources 11 238953967524352906 238953967524352906 rfl endpoint_12_73_base endpoint_12_73_p11) (by decide)⟩
private def endpoint_12_74_flag : Flag := ⟨12, 74, 2124⟩
private def endpoint_12_74_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_12_74_base : receiptBase endpoint_12_74_flag endpoint_12_74_sources = some 231946109875292149 := by decide +kernel
private theorem endpoint_12_74_w0 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 2 231946109875292149 = some 231946109875292149 := by decide +kernel
private theorem endpoint_12_74_w2 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 2 2 231946109875292149 = some 231946109875292149 := by decide +kernel
private theorem endpoint_12_74_p4 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 4 231946109875292149 = some 231946109875292149 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 2 2 231946109875292149 231946109875292149 231946109875292149 endpoint_12_74_w0 endpoint_12_74_w2
private theorem endpoint_12_74_w4 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 4 2 231946109875292149 = some 231946109875292149 := by decide +kernel
private theorem endpoint_12_74_p6 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 6 231946109875292149 = some 231946109875292149 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 4 2 231946109875292149 231946109875292149 231946109875292149 endpoint_12_74_p4 endpoint_12_74_w4
private theorem endpoint_12_74_w6 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 6 2 231946109875292149 = some 231946109875292149 := by decide +kernel
private theorem endpoint_12_74_p8 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 8 231946109875292149 = some 231946109875292149 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 6 2 231946109875292149 231946109875292149 231946109875292149 endpoint_12_74_p6 endpoint_12_74_w6
private theorem endpoint_12_74_w8 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 8 2 231946109875292149 = some 231946109875292149 := by decide +kernel
private theorem endpoint_12_74_p10 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 10 231946109875292149 = some 231946109875292149 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 8 2 231946109875292149 231946109875292149 231946109875292149 endpoint_12_74_p8 endpoint_12_74_w8
private theorem endpoint_12_74_w10 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 10 1 231946109875292149 = some 231946109875292149 := by decide +kernel
private theorem endpoint_12_74_p11 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 11 231946109875292149 = some 231946109875292149 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 10 1 231946109875292149 231946109875292149 231946109875292149 endpoint_12_74_p10 endpoint_12_74_w10
def endpoint_12_74 : CertifiedEndpoint :=
  ⟨⟨12, 74, 2124⟩, 231946109875292149, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_12_74_flag endpoint_12_74_sources 11 231946109875292149 231946109875292149 rfl endpoint_12_74_base endpoint_12_74_p11) (by decide)⟩
private def endpoint_12_75_flag : Flag := ⟨12, 75, 2028⟩
private def endpoint_12_75_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_12_75_base : receiptBase endpoint_12_75_flag endpoint_12_75_sources = some 226077805153736889 := by decide +kernel
private theorem endpoint_12_75_w0 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 2 226077805153736889 = some 226077805153736889 := by decide +kernel
private theorem endpoint_12_75_w2 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 2 2 226077805153736889 = some 226077805153736889 := by decide +kernel
private theorem endpoint_12_75_p4 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 4 226077805153736889 = some 226077805153736889 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 2 2 226077805153736889 226077805153736889 226077805153736889 endpoint_12_75_w0 endpoint_12_75_w2
private theorem endpoint_12_75_w4 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 4 2 226077805153736889 = some 226077805153736889 := by decide +kernel
private theorem endpoint_12_75_p6 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 6 226077805153736889 = some 226077805153736889 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 4 2 226077805153736889 226077805153736889 226077805153736889 endpoint_12_75_p4 endpoint_12_75_w4
private theorem endpoint_12_75_w6 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 6 2 226077805153736889 = some 226077805153736889 := by decide +kernel
private theorem endpoint_12_75_p8 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 8 226077805153736889 = some 226077805153736889 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 6 2 226077805153736889 226077805153736889 226077805153736889 endpoint_12_75_p6 endpoint_12_75_w6
private theorem endpoint_12_75_w8 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 8 2 226077805153736889 = some 226077805153736889 := by decide +kernel
private theorem endpoint_12_75_p10 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 10 226077805153736889 = some 226077805153736889 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 8 2 226077805153736889 226077805153736889 226077805153736889 endpoint_12_75_p8 endpoint_12_75_w8
private theorem endpoint_12_75_w10 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 10 1 226077805153736889 = some 226077805153736889 := by decide +kernel
private theorem endpoint_12_75_p11 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 11 226077805153736889 = some 226077805153736889 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 10 1 226077805153736889 226077805153736889 226077805153736889 endpoint_12_75_p10 endpoint_12_75_w10
def endpoint_12_75 : CertifiedEndpoint :=
  ⟨⟨12, 75, 2028⟩, 226077805153736889, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_12_75_flag endpoint_12_75_sources 11 226077805153736889 226077805153736889 rfl endpoint_12_75_base endpoint_12_75_p11) (by decide)⟩
private def endpoint_12_76_flag : Flag := ⟨12, 76, 1930⟩
private def endpoint_12_76_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_12_76_base : receiptBase endpoint_12_76_flag endpoint_12_76_sources = some 217813630877818589 := by decide +kernel
private theorem endpoint_12_76_w0 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 2 217813630877818589 = some 217813630877818589 := by decide +kernel
private theorem endpoint_12_76_w2 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 2 2 217813630877818589 = some 217813630877818589 := by decide +kernel
private theorem endpoint_12_76_p4 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 4 217813630877818589 = some 217813630877818589 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 2 2 217813630877818589 217813630877818589 217813630877818589 endpoint_12_76_w0 endpoint_12_76_w2
private theorem endpoint_12_76_w4 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 4 2 217813630877818589 = some 217813630877818589 := by decide +kernel
private theorem endpoint_12_76_p6 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 6 217813630877818589 = some 217813630877818589 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 4 2 217813630877818589 217813630877818589 217813630877818589 endpoint_12_76_p4 endpoint_12_76_w4
private theorem endpoint_12_76_w6 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 6 2 217813630877818589 = some 217813630877818589 := by decide +kernel
private theorem endpoint_12_76_p8 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 8 217813630877818589 = some 217813630877818589 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 6 2 217813630877818589 217813630877818589 217813630877818589 endpoint_12_76_p6 endpoint_12_76_w6
private theorem endpoint_12_76_w8 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 8 2 217813630877818589 = some 217813630877818589 := by decide +kernel
private theorem endpoint_12_76_p10 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 10 217813630877818589 = some 217813630877818589 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 8 2 217813630877818589 217813630877818589 217813630877818589 endpoint_12_76_p8 endpoint_12_76_w8
private theorem endpoint_12_76_w10 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 10 1 217813630877818589 = some 217813630877818589 := by decide +kernel
private theorem endpoint_12_76_p11 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 11 217813630877818589 = some 217813630877818589 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 10 1 217813630877818589 217813630877818589 217813630877818589 endpoint_12_76_p10 endpoint_12_76_w10
def endpoint_12_76 : CertifiedEndpoint :=
  ⟨⟨12, 76, 1930⟩, 217813630877818589, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_12_76_flag endpoint_12_76_sources 11 217813630877818589 217813630877818589 rfl endpoint_12_76_base endpoint_12_76_p11) (by decide)⟩
private def endpoint_12_77_flag : Flag := ⟨12, 77, 1828⟩
private def endpoint_12_77_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_12_77_base : receiptBase endpoint_12_77_flag endpoint_12_77_sources = some 208837775829021055 := by decide +kernel
private theorem endpoint_12_77_w0 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 2 208837775829021055 = some 208837775829021055 := by decide +kernel
private theorem endpoint_12_77_w2 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 2 2 208837775829021055 = some 208837775829021055 := by decide +kernel
private theorem endpoint_12_77_p4 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 4 208837775829021055 = some 208837775829021055 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 2 2 208837775829021055 208837775829021055 208837775829021055 endpoint_12_77_w0 endpoint_12_77_w2
private theorem endpoint_12_77_w4 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 4 2 208837775829021055 = some 208837775829021055 := by decide +kernel
private theorem endpoint_12_77_p6 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 6 208837775829021055 = some 208837775829021055 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 4 2 208837775829021055 208837775829021055 208837775829021055 endpoint_12_77_p4 endpoint_12_77_w4
private theorem endpoint_12_77_w6 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 6 2 208837775829021055 = some 208837775829021055 := by decide +kernel
private theorem endpoint_12_77_p8 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 8 208837775829021055 = some 208837775829021055 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 6 2 208837775829021055 208837775829021055 208837775829021055 endpoint_12_77_p6 endpoint_12_77_w6
private theorem endpoint_12_77_w8 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 8 2 208837775829021055 = some 208837775829021055 := by decide +kernel
private theorem endpoint_12_77_p10 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 10 208837775829021055 = some 208837775829021055 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 8 2 208837775829021055 208837775829021055 208837775829021055 endpoint_12_77_p8 endpoint_12_77_w8
private theorem endpoint_12_77_w10 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 10 1 208837775829021055 = some 208837775829021055 := by decide +kernel
private theorem endpoint_12_77_p11 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 11 208837775829021055 = some 208837775829021055 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 10 1 208837775829021055 208837775829021055 208837775829021055 endpoint_12_77_p10 endpoint_12_77_w10
def endpoint_12_77 : CertifiedEndpoint :=
  ⟨⟨12, 77, 1828⟩, 208837775829021055, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_12_77_flag endpoint_12_77_sources 11 208837775829021055 208837775829021055 rfl endpoint_12_77_base endpoint_12_77_p11) (by decide)⟩
private def endpoint_12_78_flag : Flag := ⟨12, 78, 1724⟩
private def endpoint_12_78_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_12_78_base : receiptBase endpoint_12_78_flag endpoint_12_78_sources = some 202778909024602352 := by decide +kernel
private theorem endpoint_12_78_w0 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 2 202778909024602352 = some 202778909024602352 := by decide +kernel
private theorem endpoint_12_78_w2 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 2 2 202778909024602352 = some 202778909024602352 := by decide +kernel
private theorem endpoint_12_78_p4 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 4 202778909024602352 = some 202778909024602352 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 2 2 202778909024602352 202778909024602352 202778909024602352 endpoint_12_78_w0 endpoint_12_78_w2
private theorem endpoint_12_78_w4 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 4 2 202778909024602352 = some 202778909024602352 := by decide +kernel
private theorem endpoint_12_78_p6 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 6 202778909024602352 = some 202778909024602352 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 4 2 202778909024602352 202778909024602352 202778909024602352 endpoint_12_78_p4 endpoint_12_78_w4
private theorem endpoint_12_78_w6 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 6 2 202778909024602352 = some 202778909024602352 := by decide +kernel
private theorem endpoint_12_78_p8 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 8 202778909024602352 = some 202778909024602352 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 6 2 202778909024602352 202778909024602352 202778909024602352 endpoint_12_78_p6 endpoint_12_78_w6
private theorem endpoint_12_78_w8 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 8 2 202778909024602352 = some 202778909024602352 := by decide +kernel
private theorem endpoint_12_78_p10 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 10 202778909024602352 = some 202778909024602352 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 8 2 202778909024602352 202778909024602352 202778909024602352 endpoint_12_78_p8 endpoint_12_78_w8
private theorem endpoint_12_78_w10 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 10 1 202778909024602352 = some 202778909024602352 := by decide +kernel
private theorem endpoint_12_78_p11 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 11 202778909024602352 = some 202778909024602352 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 10 1 202778909024602352 202778909024602352 202778909024602352 endpoint_12_78_p10 endpoint_12_78_w10
def endpoint_12_78 : CertifiedEndpoint :=
  ⟨⟨12, 78, 1724⟩, 202778909024602352, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_12_78_flag endpoint_12_78_sources 11 202778909024602352 202778909024602352 rfl endpoint_12_78_base endpoint_12_78_p11) (by decide)⟩
private def endpoint_12_79_flag : Flag := ⟨12, 79, 1616⟩
private def endpoint_12_79_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_12_79_base : receiptBase endpoint_12_79_flag endpoint_12_79_sources = some 192326766960130979 := by decide +kernel
private theorem endpoint_12_79_w0 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 2 192326766960130979 = some 192326766960130979 := by decide +kernel
private theorem endpoint_12_79_w2 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 2 2 192326766960130979 = some 192326766960130979 := by decide +kernel
private theorem endpoint_12_79_p4 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 4 192326766960130979 = some 192326766960130979 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 2 2 192326766960130979 192326766960130979 192326766960130979 endpoint_12_79_w0 endpoint_12_79_w2
private theorem endpoint_12_79_w4 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 4 2 192326766960130979 = some 192326766960130979 := by decide +kernel
private theorem endpoint_12_79_p6 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 6 192326766960130979 = some 192326766960130979 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 4 2 192326766960130979 192326766960130979 192326766960130979 endpoint_12_79_p4 endpoint_12_79_w4
private theorem endpoint_12_79_w6 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 6 2 192326766960130979 = some 192326766960130979 := by decide +kernel
private theorem endpoint_12_79_p8 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 8 192326766960130979 = some 192326766960130979 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 6 2 192326766960130979 192326766960130979 192326766960130979 endpoint_12_79_p6 endpoint_12_79_w6
private theorem endpoint_12_79_w8 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 8 2 192326766960130979 = some 192326766960130979 := by decide +kernel
private theorem endpoint_12_79_p10 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 10 192326766960130979 = some 192326766960130979 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 8 2 192326766960130979 192326766960130979 192326766960130979 endpoint_12_79_p8 endpoint_12_79_w8
private theorem endpoint_12_79_w10 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 10 1 192326766960130979 = some 192326766960130979 := by decide +kernel
private theorem endpoint_12_79_p11 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 11 192326766960130979 = some 192326766960130979 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 10 1 192326766960130979 192326766960130979 192326766960130979 endpoint_12_79_p10 endpoint_12_79_w10
def endpoint_12_79 : CertifiedEndpoint :=
  ⟨⟨12, 79, 1616⟩, 192326766960130979, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_12_79_flag endpoint_12_79_sources 11 192326766960130979 192326766960130979 rfl endpoint_12_79_base endpoint_12_79_p11) (by decide)⟩
private def endpoint_12_80_flag : Flag := ⟨12, 80, 1505⟩
private def endpoint_12_80_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_12_80_base : receiptBase endpoint_12_80_flag endpoint_12_80_sources = some 181573774232542736 := by decide +kernel
private theorem endpoint_12_80_w0 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 2 181573774232542736 = some 181573774232542736 := by decide +kernel
private theorem endpoint_12_80_w2 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 2 2 181573774232542736 = some 181573774232542736 := by decide +kernel
private theorem endpoint_12_80_p4 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 4 181573774232542736 = some 181573774232542736 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 2 2 181573774232542736 181573774232542736 181573774232542736 endpoint_12_80_w0 endpoint_12_80_w2
private theorem endpoint_12_80_w4 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 4 2 181573774232542736 = some 181573774232542736 := by decide +kernel
private theorem endpoint_12_80_p6 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 6 181573774232542736 = some 181573774232542736 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 4 2 181573774232542736 181573774232542736 181573774232542736 endpoint_12_80_p4 endpoint_12_80_w4
private theorem endpoint_12_80_w6 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 6 2 181573774232542736 = some 181573774232542736 := by decide +kernel
private theorem endpoint_12_80_p8 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 8 181573774232542736 = some 181573774232542736 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 6 2 181573774232542736 181573774232542736 181573774232542736 endpoint_12_80_p6 endpoint_12_80_w6
private theorem endpoint_12_80_w8 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 8 2 181573774232542736 = some 181573774232542736 := by decide +kernel
private theorem endpoint_12_80_p10 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 10 181573774232542736 = some 181573774232542736 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 8 2 181573774232542736 181573774232542736 181573774232542736 endpoint_12_80_p8 endpoint_12_80_w8
private theorem endpoint_12_80_w10 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 10 1 181573774232542736 = some 181573774232542736 := by decide +kernel
private theorem endpoint_12_80_p11 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 11 181573774232542736 = some 181573774232542736 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 10 1 181573774232542736 181573774232542736 181573774232542736 endpoint_12_80_p10 endpoint_12_80_w10
def endpoint_12_80 : CertifiedEndpoint :=
  ⟨⟨12, 80, 1505⟩, 181573774232542736, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_12_80_flag endpoint_12_80_sources 11 181573774232542736 181573774232542736 rfl endpoint_12_80_base endpoint_12_80_p11) (by decide)⟩
private def endpoint_12_81_flag : Flag := ⟨12, 81, 1392⟩
private def endpoint_12_81_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_12_81_base : receiptBase endpoint_12_81_flag endpoint_12_81_sources = some 170879121015886785 := by decide +kernel
private theorem endpoint_12_81_w0 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 2 170879121015886785 = some 170879121015886785 := by decide +kernel
private theorem endpoint_12_81_w2 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 2 2 170879121015886785 = some 170879121015886785 := by decide +kernel
private theorem endpoint_12_81_p4 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 4 170879121015886785 = some 170879121015886785 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 2 2 170879121015886785 170879121015886785 170879121015886785 endpoint_12_81_w0 endpoint_12_81_w2
private theorem endpoint_12_81_w4 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 4 2 170879121015886785 = some 170879121015886785 := by decide +kernel
private theorem endpoint_12_81_p6 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 6 170879121015886785 = some 170879121015886785 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 4 2 170879121015886785 170879121015886785 170879121015886785 endpoint_12_81_p4 endpoint_12_81_w4
private theorem endpoint_12_81_w6 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 6 2 170879121015886785 = some 170879121015886785 := by decide +kernel
private theorem endpoint_12_81_p8 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 8 170879121015886785 = some 170879121015886785 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 6 2 170879121015886785 170879121015886785 170879121015886785 endpoint_12_81_p6 endpoint_12_81_w6
private theorem endpoint_12_81_w8 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 8 2 170879121015886785 = some 170879121015886785 := by decide +kernel
private theorem endpoint_12_81_p10 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 10 170879121015886785 = some 170879121015886785 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 8 2 170879121015886785 170879121015886785 170879121015886785 endpoint_12_81_p8 endpoint_12_81_w8
private theorem endpoint_12_81_w10 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 10 1 170879121015886785 = some 170879121015886785 := by decide +kernel
private theorem endpoint_12_81_p11 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 11 170879121015886785 = some 170879121015886785 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 10 1 170879121015886785 170879121015886785 170879121015886785 endpoint_12_81_p10 endpoint_12_81_w10
def endpoint_12_81 : CertifiedEndpoint :=
  ⟨⟨12, 81, 1392⟩, 170879121015886785, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_12_81_flag endpoint_12_81_sources 11 170879121015886785 170879121015886785 rfl endpoint_12_81_base endpoint_12_81_p11) (by decide)⟩
private def endpoint_12_82_flag : Flag := ⟨12, 82, 1275⟩
private def endpoint_12_82_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_12_82_base : receiptBase endpoint_12_82_flag endpoint_12_82_sources = some 158386827851548480 := by decide +kernel
private theorem endpoint_12_82_w0 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 2 158386827851548480 = some 158386827851548480 := by decide +kernel
private theorem endpoint_12_82_w2 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 2 2 158386827851548480 = some 158386827851548480 := by decide +kernel
private theorem endpoint_12_82_p4 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 4 158386827851548480 = some 158386827851548480 :=
  join_receipt_window endpoint_12_82_flag endpoint_12_82_sources 0 2 2 158386827851548480 158386827851548480 158386827851548480 endpoint_12_82_w0 endpoint_12_82_w2
private theorem endpoint_12_82_w4 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 4 2 158386827851548480 = some 158386827851548480 := by decide +kernel
private theorem endpoint_12_82_p6 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 6 158386827851548480 = some 158386827851548480 :=
  join_receipt_window endpoint_12_82_flag endpoint_12_82_sources 0 4 2 158386827851548480 158386827851548480 158386827851548480 endpoint_12_82_p4 endpoint_12_82_w4
private theorem endpoint_12_82_w6 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 6 2 158386827851548480 = some 158386827851548480 := by decide +kernel
private theorem endpoint_12_82_p8 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 8 158386827851548480 = some 158386827851548480 :=
  join_receipt_window endpoint_12_82_flag endpoint_12_82_sources 0 6 2 158386827851548480 158386827851548480 158386827851548480 endpoint_12_82_p6 endpoint_12_82_w6
private theorem endpoint_12_82_w8 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 8 2 158386827851548480 = some 158386827851548480 := by decide +kernel
private theorem endpoint_12_82_p10 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 10 158386827851548480 = some 158386827851548480 :=
  join_receipt_window endpoint_12_82_flag endpoint_12_82_sources 0 8 2 158386827851548480 158386827851548480 158386827851548480 endpoint_12_82_p8 endpoint_12_82_w8
private theorem endpoint_12_82_w10 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 10 1 158386827851548480 = some 158386827851548480 := by decide +kernel
private theorem endpoint_12_82_p11 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 11 158386827851548480 = some 158386827851548480 :=
  join_receipt_window endpoint_12_82_flag endpoint_12_82_sources 0 10 1 158386827851548480 158386827851548480 158386827851548480 endpoint_12_82_p10 endpoint_12_82_w10
def endpoint_12_82 : CertifiedEndpoint :=
  ⟨⟨12, 82, 1275⟩, 158386827851548480, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_12_82_flag endpoint_12_82_sources 11 158386827851548480 158386827851548480 rfl endpoint_12_82_base endpoint_12_82_p11) (by decide)⟩
def endpoint_12_83 : CertifiedEndpoint :=
  ⟨⟨12, 83, 1155⟩, 252466839485081780, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_84 : CertifiedEndpoint :=
  ⟨⟨12, 84, 1032⟩, 227318064931392840, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_85 : CertifiedEndpoint :=
  ⟨⟨12, 85, 906⟩, 200735182018213079, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_86 : CertifiedEndpoint :=
  ⟨⟨12, 86, 777⟩, 172691441020358651, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_87 : CertifiedEndpoint :=
  ⟨⟨12, 87, 645⟩, 143160092212645710, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_88 : CertifiedEndpoint :=
  ⟨⟨12, 88, 510⟩, 112114385869890410, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_89 : CertifiedEndpoint :=
  ⟨⟨12, 89, 371⟩, 79282357829234328, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_90 : CertifiedEndpoint :=
  ⟨⟨12, 90, 230⟩, 45124715049155678, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_13 : CertifiedEndpoint :=
  ⟨⟨13, 13, 4563⟩, 108069562065212176, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_14 : CertifiedEndpoint :=
  ⟨⟨13, 14, 4540⟩, 112304729412302944, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_15 : CertifiedEndpoint :=
  ⟨⟨13, 15, 4517⟩, 116491293682499870, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_16 : CertifiedEndpoint :=
  ⟨⟨13, 16, 4493⟩, 130332806029173173, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_17 : CertifiedEndpoint :=
  ⟨⟨13, 17, 4469⟩, 144016053471045522, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_18 : CertifiedEndpoint :=
  ⟨⟨13, 18, 4445⟩, 157541036008116917, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_19 : CertifiedEndpoint :=
  ⟨⟨13, 19, 4421⟩, 170907753640387358, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_20 : CertifiedEndpoint :=
  ⟨⟨13, 20, 4396⟩, 184074209093336952, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_21 : CertifiedEndpoint :=
  ⟨⟨13, 21, 4371⟩, 197075939849452900, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_22 : CertifiedEndpoint :=
  ⟨⟨13, 22, 4346⟩, 209912945908735202, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_23 : CertifiedEndpoint :=
  ⟨⟨13, 23, 4320⟩, 222533540308614927, .intrinsic (by decide +kernel) (by decide)⟩

def endpointBlock08 : List CertifiedEndpoint := [
  endpoint_11_59, endpoint_11_60, endpoint_11_61, endpoint_11_62, endpoint_11_63, endpoint_11_64, endpoint_11_65,
  endpoint_11_66, endpoint_11_67, endpoint_11_68, endpoint_11_69, endpoint_11_70, endpoint_11_71, endpoint_11_72,
  endpoint_11_73, endpoint_11_74, endpoint_11_75, endpoint_11_76, endpoint_11_77, endpoint_11_78, endpoint_11_79,
  endpoint_11_80, endpoint_11_81, endpoint_11_82, endpoint_11_83, endpoint_11_84, endpoint_11_85, endpoint_11_86,
  endpoint_11_87, endpoint_11_88, endpoint_11_89, endpoint_11_90, endpoint_11_91, endpoint_11_92, endpoint_12_12,
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
  endpoint_12_90, endpoint_13_13, endpoint_13_14, endpoint_13_15, endpoint_13_16, endpoint_13_17, endpoint_13_18,
  endpoint_13_19, endpoint_13_20, endpoint_13_21, endpoint_13_22, endpoint_13_23
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
