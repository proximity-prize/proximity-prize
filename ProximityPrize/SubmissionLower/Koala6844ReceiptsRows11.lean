import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_16_63_flag : Flag := ⟨16, 63, 1894⟩
private def endpoint_16_63_sources : Sources := ⟨contact29, contact16, contact13⟩
private theorem endpoint_16_63_base : receiptBase endpoint_16_63_flag endpoint_16_63_sources = some 217670017638755132 := by decide +kernel
private theorem endpoint_16_63_w0 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 2 217670017638755132 = some 234181159743859033 := by decide +kernel
private theorem endpoint_16_63_w2 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 2 2 234181159743859033 = some 234181159743859033 := by decide +kernel
private theorem endpoint_16_63_p4 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 4 217670017638755132 = some 234181159743859033 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 2 2 217670017638755132 234181159743859033 234181159743859033 endpoint_16_63_w0 endpoint_16_63_w2
private theorem endpoint_16_63_w4 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 4 2 234181159743859033 = some 234181159743859033 := by decide +kernel
private theorem endpoint_16_63_p6 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 6 217670017638755132 = some 234181159743859033 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 4 2 217670017638755132 234181159743859033 234181159743859033 endpoint_16_63_p4 endpoint_16_63_w4
private theorem endpoint_16_63_w6 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 6 2 234181159743859033 = some 234181159743859033 := by decide +kernel
private theorem endpoint_16_63_p8 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 8 217670017638755132 = some 234181159743859033 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 6 2 217670017638755132 234181159743859033 234181159743859033 endpoint_16_63_p6 endpoint_16_63_w6
private theorem endpoint_16_63_w8 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 8 2 234181159743859033 = some 234181159743859033 := by decide +kernel
private theorem endpoint_16_63_p10 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 10 217670017638755132 = some 234181159743859033 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 8 2 217670017638755132 234181159743859033 234181159743859033 endpoint_16_63_p8 endpoint_16_63_w8
private theorem endpoint_16_63_w10 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 10 2 234181159743859033 = some 234181159743859033 := by decide +kernel
private theorem endpoint_16_63_p12 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 12 217670017638755132 = some 234181159743859033 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 10 2 217670017638755132 234181159743859033 234181159743859033 endpoint_16_63_p10 endpoint_16_63_w10
private theorem endpoint_16_63_w12 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 12 2 234181159743859033 = some 234181159743859033 := by decide +kernel
private theorem endpoint_16_63_p14 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 14 217670017638755132 = some 234181159743859033 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 12 2 217670017638755132 234181159743859033 234181159743859033 endpoint_16_63_p12 endpoint_16_63_w12
private theorem endpoint_16_63_w14 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 14 1 234181159743859033 = some 234181159743859033 := by decide +kernel
private theorem endpoint_16_63_p15 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 15 217670017638755132 = some 234181159743859033 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 14 1 217670017638755132 234181159743859033 234181159743859033 endpoint_16_63_p14 endpoint_16_63_w14
def endpoint_16_63 : CertifiedEndpoint :=
  ⟨⟨16, 63, 1894⟩, 234181159743859033, .terminal ⟨contact29, contact16, contact13⟩ (finish_receipt_window endpoint_16_63_flag endpoint_16_63_sources 15 217670017638755132 234181159743859033 rfl endpoint_16_63_base endpoint_16_63_p15) (by decide)⟩
private def endpoint_16_64_flag : Flag := ⟨16, 64, 1832⟩
private def endpoint_16_64_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_16_64_base : receiptBase endpoint_16_64_flag endpoint_16_64_sources = some 215498249444340168 := by decide +kernel
private theorem endpoint_16_64_w0 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 2 215498249444340168 = some 218946769498798456 := by decide +kernel
private theorem endpoint_16_64_w2 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 2 2 218946769498798456 = some 218946769498798456 := by decide +kernel
private theorem endpoint_16_64_p4 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 4 215498249444340168 = some 218946769498798456 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 2 2 215498249444340168 218946769498798456 218946769498798456 endpoint_16_64_w0 endpoint_16_64_w2
private theorem endpoint_16_64_w4 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 4 2 218946769498798456 = some 218946769498798456 := by decide +kernel
private theorem endpoint_16_64_p6 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 6 215498249444340168 = some 218946769498798456 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 4 2 215498249444340168 218946769498798456 218946769498798456 endpoint_16_64_p4 endpoint_16_64_w4
private theorem endpoint_16_64_w6 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 6 2 218946769498798456 = some 218946769498798456 := by decide +kernel
private theorem endpoint_16_64_p8 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 8 215498249444340168 = some 218946769498798456 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 6 2 215498249444340168 218946769498798456 218946769498798456 endpoint_16_64_p6 endpoint_16_64_w6
private theorem endpoint_16_64_w8 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 8 2 218946769498798456 = some 218946769498798456 := by decide +kernel
private theorem endpoint_16_64_p10 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 10 215498249444340168 = some 218946769498798456 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 8 2 215498249444340168 218946769498798456 218946769498798456 endpoint_16_64_p8 endpoint_16_64_w8
private theorem endpoint_16_64_w10 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 10 2 218946769498798456 = some 218946769498798456 := by decide +kernel
private theorem endpoint_16_64_p12 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 12 215498249444340168 = some 218946769498798456 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 10 2 215498249444340168 218946769498798456 218946769498798456 endpoint_16_64_p10 endpoint_16_64_w10
private theorem endpoint_16_64_w12 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 12 2 218946769498798456 = some 218946769498798456 := by decide +kernel
private theorem endpoint_16_64_p14 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 14 215498249444340168 = some 218946769498798456 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 12 2 215498249444340168 218946769498798456 218946769498798456 endpoint_16_64_p12 endpoint_16_64_w12
private theorem endpoint_16_64_w14 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 14 1 218946769498798456 = some 218946769498798456 := by decide +kernel
private theorem endpoint_16_64_p15 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 15 215498249444340168 = some 218946769498798456 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 14 1 215498249444340168 218946769498798456 218946769498798456 endpoint_16_64_p14 endpoint_16_64_w14
def endpoint_16_64 : CertifiedEndpoint :=
  ⟨⟨16, 64, 1832⟩, 218946769498798456, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_16_64_flag endpoint_16_64_sources 15 215498249444340168 218946769498798456 rfl endpoint_16_64_base endpoint_16_64_p15) (by decide)⟩
private def endpoint_16_65_flag : Flag := ⟨16, 65, 1769⟩
private def endpoint_16_65_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_16_65_base : receiptBase endpoint_16_65_flag endpoint_16_65_sources = some 211037298640592753 := by decide +kernel
private theorem endpoint_16_65_w0 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 2 211037298640592753 = some 218507252540026228 := by decide +kernel
private theorem endpoint_16_65_w2 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 2 2 218507252540026228 = some 218507252540026228 := by decide +kernel
private theorem endpoint_16_65_p4 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 4 211037298640592753 = some 218507252540026228 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 2 2 211037298640592753 218507252540026228 218507252540026228 endpoint_16_65_w0 endpoint_16_65_w2
private theorem endpoint_16_65_w4 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 4 2 218507252540026228 = some 218507252540026228 := by decide +kernel
private theorem endpoint_16_65_p6 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 6 211037298640592753 = some 218507252540026228 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 4 2 211037298640592753 218507252540026228 218507252540026228 endpoint_16_65_p4 endpoint_16_65_w4
private theorem endpoint_16_65_w6 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 6 2 218507252540026228 = some 218507252540026228 := by decide +kernel
private theorem endpoint_16_65_p8 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 8 211037298640592753 = some 218507252540026228 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 6 2 211037298640592753 218507252540026228 218507252540026228 endpoint_16_65_p6 endpoint_16_65_w6
private theorem endpoint_16_65_w8 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 8 2 218507252540026228 = some 218507252540026228 := by decide +kernel
private theorem endpoint_16_65_p10 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 10 211037298640592753 = some 218507252540026228 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 8 2 211037298640592753 218507252540026228 218507252540026228 endpoint_16_65_p8 endpoint_16_65_w8
private theorem endpoint_16_65_w10 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 10 2 218507252540026228 = some 218507252540026228 := by decide +kernel
private theorem endpoint_16_65_p12 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 12 211037298640592753 = some 218507252540026228 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 10 2 211037298640592753 218507252540026228 218507252540026228 endpoint_16_65_p10 endpoint_16_65_w10
private theorem endpoint_16_65_w12 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 12 2 218507252540026228 = some 218507252540026228 := by decide +kernel
private theorem endpoint_16_65_p14 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 14 211037298640592753 = some 218507252540026228 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 12 2 211037298640592753 218507252540026228 218507252540026228 endpoint_16_65_p12 endpoint_16_65_w12
private theorem endpoint_16_65_w14 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 14 1 218507252540026228 = some 218507252540026228 := by decide +kernel
private theorem endpoint_16_65_p15 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 15 211037298640592753 = some 218507252540026228 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 14 1 211037298640592753 218507252540026228 218507252540026228 endpoint_16_65_p14 endpoint_16_65_w14
def endpoint_16_65 : CertifiedEndpoint :=
  ⟨⟨16, 65, 1769⟩, 218507252540026228, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_16_65_flag endpoint_16_65_sources 15 211037298640592753 218507252540026228 rfl endpoint_16_65_base endpoint_16_65_p15) (by decide)⟩
private def endpoint_16_66_flag : Flag := ⟨16, 66, 1704⟩
private def endpoint_16_66_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_16_66_base : receiptBase endpoint_16_66_flag endpoint_16_66_sources = some 206131686119454362 := by decide +kernel
private theorem endpoint_16_66_w0 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 2 206131686119454362 = some 217769743222223528 := by decide +kernel
private theorem endpoint_16_66_w2 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 2 2 217769743222223528 = some 217769743222223528 := by decide +kernel
private theorem endpoint_16_66_p4 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 4 206131686119454362 = some 217769743222223528 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 2 2 206131686119454362 217769743222223528 217769743222223528 endpoint_16_66_w0 endpoint_16_66_w2
private theorem endpoint_16_66_w4 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 4 2 217769743222223528 = some 217769743222223528 := by decide +kernel
private theorem endpoint_16_66_p6 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 6 206131686119454362 = some 217769743222223528 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 4 2 206131686119454362 217769743222223528 217769743222223528 endpoint_16_66_p4 endpoint_16_66_w4
private theorem endpoint_16_66_w6 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 6 2 217769743222223528 = some 217769743222223528 := by decide +kernel
private theorem endpoint_16_66_p8 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 8 206131686119454362 = some 217769743222223528 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 6 2 206131686119454362 217769743222223528 217769743222223528 endpoint_16_66_p6 endpoint_16_66_w6
private theorem endpoint_16_66_w8 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 8 2 217769743222223528 = some 217769743222223528 := by decide +kernel
private theorem endpoint_16_66_p10 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 10 206131686119454362 = some 217769743222223528 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 8 2 206131686119454362 217769743222223528 217769743222223528 endpoint_16_66_p8 endpoint_16_66_w8
private theorem endpoint_16_66_w10 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 10 2 217769743222223528 = some 217769743222223528 := by decide +kernel
private theorem endpoint_16_66_p12 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 12 206131686119454362 = some 217769743222223528 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 10 2 206131686119454362 217769743222223528 217769743222223528 endpoint_16_66_p10 endpoint_16_66_w10
private theorem endpoint_16_66_w12 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 12 2 217769743222223528 = some 217769743222223528 := by decide +kernel
private theorem endpoint_16_66_p14 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 14 206131686119454362 = some 217769743222223528 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 12 2 206131686119454362 217769743222223528 217769743222223528 endpoint_16_66_p12 endpoint_16_66_w12
private theorem endpoint_16_66_w14 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 14 1 217769743222223528 = some 217769743222223528 := by decide +kernel
private theorem endpoint_16_66_p15 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 15 206131686119454362 = some 217769743222223528 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 14 1 206131686119454362 217769743222223528 217769743222223528 endpoint_16_66_p14 endpoint_16_66_w14
def endpoint_16_66 : CertifiedEndpoint :=
  ⟨⟨16, 66, 1704⟩, 217769743222223528, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_16_66_flag endpoint_16_66_sources 15 206131686119454362 217769743222223528 rfl endpoint_16_66_base endpoint_16_66_p15) (by decide)⟩
private def endpoint_16_67_flag : Flag := ⟨16, 67, 1637⟩
private def endpoint_16_67_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_16_67_base : receiptBase endpoint_16_67_flag endpoint_16_67_sources = some 202391276347412344 := by decide +kernel
private theorem endpoint_16_67_w0 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 2 202391276347412344 = some 202391276347412344 := by decide +kernel
private theorem endpoint_16_67_w2 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 2 2 202391276347412344 = some 202391276347412344 := by decide +kernel
private theorem endpoint_16_67_p4 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 4 202391276347412344 = some 202391276347412344 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 2 2 202391276347412344 202391276347412344 202391276347412344 endpoint_16_67_w0 endpoint_16_67_w2
private theorem endpoint_16_67_w4 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 4 2 202391276347412344 = some 202391276347412344 := by decide +kernel
private theorem endpoint_16_67_p6 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 6 202391276347412344 = some 202391276347412344 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 4 2 202391276347412344 202391276347412344 202391276347412344 endpoint_16_67_p4 endpoint_16_67_w4
private theorem endpoint_16_67_w6 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 6 2 202391276347412344 = some 202391276347412344 := by decide +kernel
private theorem endpoint_16_67_p8 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 8 202391276347412344 = some 202391276347412344 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 6 2 202391276347412344 202391276347412344 202391276347412344 endpoint_16_67_p6 endpoint_16_67_w6
private theorem endpoint_16_67_w8 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 8 2 202391276347412344 = some 202391276347412344 := by decide +kernel
private theorem endpoint_16_67_p10 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 10 202391276347412344 = some 202391276347412344 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 8 2 202391276347412344 202391276347412344 202391276347412344 endpoint_16_67_p8 endpoint_16_67_w8
private theorem endpoint_16_67_w10 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 10 2 202391276347412344 = some 202391276347412344 := by decide +kernel
private theorem endpoint_16_67_p12 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 12 202391276347412344 = some 202391276347412344 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 10 2 202391276347412344 202391276347412344 202391276347412344 endpoint_16_67_p10 endpoint_16_67_w10
private theorem endpoint_16_67_w12 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 12 2 202391276347412344 = some 202391276347412344 := by decide +kernel
private theorem endpoint_16_67_p14 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 14 202391276347412344 = some 202391276347412344 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 12 2 202391276347412344 202391276347412344 202391276347412344 endpoint_16_67_p12 endpoint_16_67_w12
private theorem endpoint_16_67_w14 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 14 1 202391276347412344 = some 202391276347412344 := by decide +kernel
private theorem endpoint_16_67_p15 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 15 202391276347412344 = some 202391276347412344 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 14 1 202391276347412344 202391276347412344 202391276347412344 endpoint_16_67_p14 endpoint_16_67_w14
def endpoint_16_67 : CertifiedEndpoint :=
  ⟨⟨16, 67, 1637⟩, 202391276347412344, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_16_67_flag endpoint_16_67_sources 15 202391276347412344 202391276347412344 rfl endpoint_16_67_base endpoint_16_67_p15) (by decide)⟩
private def endpoint_16_68_flag : Flag := ⟨16, 68, 1568⟩
private def endpoint_16_68_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_16_68_base : receiptBase endpoint_16_68_flag endpoint_16_68_sources = some 196506802173190748 := by decide +kernel
private theorem endpoint_16_68_w0 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 2 196506802173190748 = some 199564018187599816 := by decide +kernel
private theorem endpoint_16_68_w2 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 2 2 199564018187599816 = some 199564018187599816 := by decide +kernel
private theorem endpoint_16_68_p4 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 4 196506802173190748 = some 199564018187599816 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 2 2 196506802173190748 199564018187599816 199564018187599816 endpoint_16_68_w0 endpoint_16_68_w2
private theorem endpoint_16_68_w4 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 4 2 199564018187599816 = some 199564018187599816 := by decide +kernel
private theorem endpoint_16_68_p6 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 6 196506802173190748 = some 199564018187599816 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 4 2 196506802173190748 199564018187599816 199564018187599816 endpoint_16_68_p4 endpoint_16_68_w4
private theorem endpoint_16_68_w6 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 6 2 199564018187599816 = some 199564018187599816 := by decide +kernel
private theorem endpoint_16_68_p8 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 8 196506802173190748 = some 199564018187599816 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 6 2 196506802173190748 199564018187599816 199564018187599816 endpoint_16_68_p6 endpoint_16_68_w6
private theorem endpoint_16_68_w8 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 8 2 199564018187599816 = some 199564018187599816 := by decide +kernel
private theorem endpoint_16_68_p10 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 10 196506802173190748 = some 199564018187599816 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 8 2 196506802173190748 199564018187599816 199564018187599816 endpoint_16_68_p8 endpoint_16_68_w8
private theorem endpoint_16_68_w10 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 10 2 199564018187599816 = some 199564018187599816 := by decide +kernel
private theorem endpoint_16_68_p12 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 12 196506802173190748 = some 199564018187599816 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 10 2 196506802173190748 199564018187599816 199564018187599816 endpoint_16_68_p10 endpoint_16_68_w10
private theorem endpoint_16_68_w12 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 12 2 199564018187599816 = some 199564018187599816 := by decide +kernel
private theorem endpoint_16_68_p14 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 14 196506802173190748 = some 199564018187599816 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 12 2 196506802173190748 199564018187599816 199564018187599816 endpoint_16_68_p12 endpoint_16_68_w12
private theorem endpoint_16_68_w14 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 14 1 199564018187599816 = some 199564018187599816 := by decide +kernel
private theorem endpoint_16_68_p15 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 15 196506802173190748 = some 199564018187599816 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 14 1 196506802173190748 199564018187599816 199564018187599816 endpoint_16_68_p14 endpoint_16_68_w14
def endpoint_16_68 : CertifiedEndpoint :=
  ⟨⟨16, 68, 1568⟩, 199564018187599816, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_16_68_flag endpoint_16_68_sources 15 196506802173190748 199564018187599816 rfl endpoint_16_68_base endpoint_16_68_p15) (by decide)⟩
private def endpoint_16_69_flag : Flag := ⟨16, 69, 1496⟩
private def endpoint_16_69_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_16_69_base : receiptBase endpoint_16_69_flag endpoint_16_69_sources = some 190019878117734028 := by decide +kernel
private theorem endpoint_16_69_w0 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 2 190019878117734028 = some 197548096866852139 := by decide +kernel
private theorem endpoint_16_69_w2 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 2 2 197548096866852139 = some 197548096866852139 := by decide +kernel
private theorem endpoint_16_69_p4 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 4 190019878117734028 = some 197548096866852139 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 2 2 190019878117734028 197548096866852139 197548096866852139 endpoint_16_69_w0 endpoint_16_69_w2
private theorem endpoint_16_69_w4 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 4 2 197548096866852139 = some 197548096866852139 := by decide +kernel
private theorem endpoint_16_69_p6 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 6 190019878117734028 = some 197548096866852139 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 4 2 190019878117734028 197548096866852139 197548096866852139 endpoint_16_69_p4 endpoint_16_69_w4
private theorem endpoint_16_69_w6 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 6 2 197548096866852139 = some 197548096866852139 := by decide +kernel
private theorem endpoint_16_69_p8 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 8 190019878117734028 = some 197548096866852139 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 6 2 190019878117734028 197548096866852139 197548096866852139 endpoint_16_69_p6 endpoint_16_69_w6
private theorem endpoint_16_69_w8 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 8 2 197548096866852139 = some 197548096866852139 := by decide +kernel
private theorem endpoint_16_69_p10 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 10 190019878117734028 = some 197548096866852139 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 8 2 190019878117734028 197548096866852139 197548096866852139 endpoint_16_69_p8 endpoint_16_69_w8
private theorem endpoint_16_69_w10 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 10 2 197548096866852139 = some 197548096866852139 := by decide +kernel
private theorem endpoint_16_69_p12 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 12 190019878117734028 = some 197548096866852139 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 10 2 190019878117734028 197548096866852139 197548096866852139 endpoint_16_69_p10 endpoint_16_69_w10
private theorem endpoint_16_69_w12 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 12 2 197548096866852139 = some 197548096866852139 := by decide +kernel
private theorem endpoint_16_69_p14 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 14 190019878117734028 = some 197548096866852139 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 12 2 190019878117734028 197548096866852139 197548096866852139 endpoint_16_69_p12 endpoint_16_69_w12
private theorem endpoint_16_69_w14 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 14 1 197548096866852139 = some 197548096866852139 := by decide +kernel
private theorem endpoint_16_69_p15 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 15 190019878117734028 = some 197548096866852139 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 14 1 190019878117734028 197548096866852139 197548096866852139 endpoint_16_69_p14 endpoint_16_69_w14
def endpoint_16_69 : CertifiedEndpoint :=
  ⟨⟨16, 69, 1496⟩, 197548096866852139, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_16_69_flag endpoint_16_69_sources 15 190019878117734028 197548096866852139 rfl endpoint_16_69_base endpoint_16_69_p15) (by decide)⟩
private def endpoint_16_70_flag : Flag := ⟨16, 70, 1423⟩
private def endpoint_16_70_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_16_70_base : receiptBase endpoint_16_70_flag endpoint_16_70_sources = some 183523582491868745 := by decide +kernel
private theorem endpoint_16_70_w0 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 2 183523582491868745 = some 192193717300513806 := by decide +kernel
private theorem endpoint_16_70_w2 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 2 2 192193717300513806 = some 192193717300513806 := by decide +kernel
private theorem endpoint_16_70_p4 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 4 183523582491868745 = some 192193717300513806 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 2 2 183523582491868745 192193717300513806 192193717300513806 endpoint_16_70_w0 endpoint_16_70_w2
private theorem endpoint_16_70_w4 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 4 2 192193717300513806 = some 192193717300513806 := by decide +kernel
private theorem endpoint_16_70_p6 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 6 183523582491868745 = some 192193717300513806 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 4 2 183523582491868745 192193717300513806 192193717300513806 endpoint_16_70_p4 endpoint_16_70_w4
private theorem endpoint_16_70_w6 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 6 2 192193717300513806 = some 192193717300513806 := by decide +kernel
private theorem endpoint_16_70_p8 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 8 183523582491868745 = some 192193717300513806 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 6 2 183523582491868745 192193717300513806 192193717300513806 endpoint_16_70_p6 endpoint_16_70_w6
private theorem endpoint_16_70_w8 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 8 2 192193717300513806 = some 192193717300513806 := by decide +kernel
private theorem endpoint_16_70_p10 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 10 183523582491868745 = some 192193717300513806 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 8 2 183523582491868745 192193717300513806 192193717300513806 endpoint_16_70_p8 endpoint_16_70_w8
private theorem endpoint_16_70_w10 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 10 2 192193717300513806 = some 192193717300513806 := by decide +kernel
private theorem endpoint_16_70_p12 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 12 183523582491868745 = some 192193717300513806 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 10 2 183523582491868745 192193717300513806 192193717300513806 endpoint_16_70_p10 endpoint_16_70_w10
private theorem endpoint_16_70_w12 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 12 2 192193717300513806 = some 192193717300513806 := by decide +kernel
private theorem endpoint_16_70_p14 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 14 183523582491868745 = some 192193717300513806 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 12 2 183523582491868745 192193717300513806 192193717300513806 endpoint_16_70_p12 endpoint_16_70_w12
private theorem endpoint_16_70_w14 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 14 1 192193717300513806 = some 192193717300513806 := by decide +kernel
private theorem endpoint_16_70_p15 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 15 183523582491868745 = some 192193717300513806 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 14 1 183523582491868745 192193717300513806 192193717300513806 endpoint_16_70_p14 endpoint_16_70_w14
def endpoint_16_70 : CertifiedEndpoint :=
  ⟨⟨16, 70, 1423⟩, 192193717300513806, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_16_70_flag endpoint_16_70_sources 15 183523582491868745 192193717300513806 rfl endpoint_16_70_base endpoint_16_70_p15) (by decide)⟩
private def endpoint_16_71_flag : Flag := ⟨16, 71, 1347⟩
private def endpoint_16_71_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_16_71_base : receiptBase endpoint_16_71_flag endpoint_16_71_sources = some 177257035694529921 := by decide +kernel
private theorem endpoint_16_71_w0 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 2 177257035694529921 = some 181627668686594220 := by decide +kernel
private theorem endpoint_16_71_w2 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 2 2 181627668686594220 = some 181627668686594220 := by decide +kernel
private theorem endpoint_16_71_p4 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 4 177257035694529921 = some 181627668686594220 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 2 2 177257035694529921 181627668686594220 181627668686594220 endpoint_16_71_w0 endpoint_16_71_w2
private theorem endpoint_16_71_w4 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 4 2 181627668686594220 = some 181627668686594220 := by decide +kernel
private theorem endpoint_16_71_p6 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 6 177257035694529921 = some 181627668686594220 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 4 2 177257035694529921 181627668686594220 181627668686594220 endpoint_16_71_p4 endpoint_16_71_w4
private theorem endpoint_16_71_w6 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 6 2 181627668686594220 = some 181627668686594220 := by decide +kernel
private theorem endpoint_16_71_p8 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 8 177257035694529921 = some 181627668686594220 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 6 2 177257035694529921 181627668686594220 181627668686594220 endpoint_16_71_p6 endpoint_16_71_w6
private theorem endpoint_16_71_w8 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 8 2 181627668686594220 = some 181627668686594220 := by decide +kernel
private theorem endpoint_16_71_p10 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 10 177257035694529921 = some 181627668686594220 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 8 2 177257035694529921 181627668686594220 181627668686594220 endpoint_16_71_p8 endpoint_16_71_w8
private theorem endpoint_16_71_w10 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 10 2 181627668686594220 = some 181627668686594220 := by decide +kernel
private theorem endpoint_16_71_p12 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 12 177257035694529921 = some 181627668686594220 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 10 2 177257035694529921 181627668686594220 181627668686594220 endpoint_16_71_p10 endpoint_16_71_w10
private theorem endpoint_16_71_w12 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 12 2 181627668686594220 = some 181627668686594220 := by decide +kernel
private theorem endpoint_16_71_p14 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 14 177257035694529921 = some 181627668686594220 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 12 2 177257035694529921 181627668686594220 181627668686594220 endpoint_16_71_p12 endpoint_16_71_w12
private theorem endpoint_16_71_w14 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 14 1 181627668686594220 = some 181627668686594220 := by decide +kernel
private theorem endpoint_16_71_p15 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 15 177257035694529921 = some 181627668686594220 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 14 1 177257035694529921 181627668686594220 181627668686594220 endpoint_16_71_p14 endpoint_16_71_w14
def endpoint_16_71 : CertifiedEndpoint :=
  ⟨⟨16, 71, 1347⟩, 181627668686594220, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_16_71_flag endpoint_16_71_sources 15 177257035694529921 181627668686594220 rfl endpoint_16_71_base endpoint_16_71_p15) (by decide)⟩
private def endpoint_16_72_flag : Flag := ⟨16, 72, 1269⟩
private def endpoint_16_72_sources : Sources := ⟨contact31, contact21, contact22⟩
private theorem endpoint_16_72_base : receiptBase endpoint_16_72_flag endpoint_16_72_sources = some 169934992672295628 := by decide +kernel
private theorem endpoint_16_72_w0 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 2 169934992672295628 = some 176832962842935692 := by decide +kernel
private theorem endpoint_16_72_w2 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 2 2 176832962842935692 = some 176832962842935692 := by decide +kernel
private theorem endpoint_16_72_p4 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 4 169934992672295628 = some 176832962842935692 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 2 2 169934992672295628 176832962842935692 176832962842935692 endpoint_16_72_w0 endpoint_16_72_w2
private theorem endpoint_16_72_w4 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 4 2 176832962842935692 = some 176832962842935692 := by decide +kernel
private theorem endpoint_16_72_p6 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 6 169934992672295628 = some 176832962842935692 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 4 2 169934992672295628 176832962842935692 176832962842935692 endpoint_16_72_p4 endpoint_16_72_w4
private theorem endpoint_16_72_w6 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 6 2 176832962842935692 = some 176832962842935692 := by decide +kernel
private theorem endpoint_16_72_p8 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 8 169934992672295628 = some 176832962842935692 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 6 2 169934992672295628 176832962842935692 176832962842935692 endpoint_16_72_p6 endpoint_16_72_w6
private theorem endpoint_16_72_w8 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 8 2 176832962842935692 = some 176832962842935692 := by decide +kernel
private theorem endpoint_16_72_p10 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 10 169934992672295628 = some 176832962842935692 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 8 2 169934992672295628 176832962842935692 176832962842935692 endpoint_16_72_p8 endpoint_16_72_w8
private theorem endpoint_16_72_w10 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 10 2 176832962842935692 = some 176832962842935692 := by decide +kernel
private theorem endpoint_16_72_p12 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 12 169934992672295628 = some 176832962842935692 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 10 2 169934992672295628 176832962842935692 176832962842935692 endpoint_16_72_p10 endpoint_16_72_w10
private theorem endpoint_16_72_w12 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 12 2 176832962842935692 = some 176832962842935692 := by decide +kernel
private theorem endpoint_16_72_p14 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 14 169934992672295628 = some 176832962842935692 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 12 2 169934992672295628 176832962842935692 176832962842935692 endpoint_16_72_p12 endpoint_16_72_w12
private theorem endpoint_16_72_w14 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 14 1 176832962842935692 = some 176832962842935692 := by decide +kernel
private theorem endpoint_16_72_p15 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 15 169934992672295628 = some 176832962842935692 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 14 1 169934992672295628 176832962842935692 176832962842935692 endpoint_16_72_p14 endpoint_16_72_w14
def endpoint_16_72 : CertifiedEndpoint :=
  ⟨⟨16, 72, 1269⟩, 176832962842935692, .terminal ⟨contact31, contact21, contact22⟩ (finish_receipt_window endpoint_16_72_flag endpoint_16_72_sources 15 169934992672295628 176832962842935692 rfl endpoint_16_72_base endpoint_16_72_p15) (by decide)⟩
private def endpoint_16_73_flag : Flag := ⟨16, 73, 1189⟩
private def endpoint_16_73_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_16_73_base : receiptBase endpoint_16_73_flag endpoint_16_73_sources = some 162103247210826382 := by decide +kernel
private theorem endpoint_16_73_w0 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 2 162103247210826382 = some 165329204847326983 := by decide +kernel
private theorem endpoint_16_73_w2 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 2 2 165329204847326983 = some 165329204847326983 := by decide +kernel
private theorem endpoint_16_73_p4 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 4 162103247210826382 = some 165329204847326983 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 2 2 162103247210826382 165329204847326983 165329204847326983 endpoint_16_73_w0 endpoint_16_73_w2
private theorem endpoint_16_73_w4 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 4 2 165329204847326983 = some 165329204847326983 := by decide +kernel
private theorem endpoint_16_73_p6 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 6 162103247210826382 = some 165329204847326983 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 4 2 162103247210826382 165329204847326983 165329204847326983 endpoint_16_73_p4 endpoint_16_73_w4
private theorem endpoint_16_73_w6 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 6 2 165329204847326983 = some 165329204847326983 := by decide +kernel
private theorem endpoint_16_73_p8 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 8 162103247210826382 = some 165329204847326983 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 6 2 162103247210826382 165329204847326983 165329204847326983 endpoint_16_73_p6 endpoint_16_73_w6
private theorem endpoint_16_73_w8 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 8 2 165329204847326983 = some 165329204847326983 := by decide +kernel
private theorem endpoint_16_73_p10 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 10 162103247210826382 = some 165329204847326983 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 8 2 162103247210826382 165329204847326983 165329204847326983 endpoint_16_73_p8 endpoint_16_73_w8
private theorem endpoint_16_73_w10 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 10 2 165329204847326983 = some 165329204847326983 := by decide +kernel
private theorem endpoint_16_73_p12 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 12 162103247210826382 = some 165329204847326983 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 10 2 162103247210826382 165329204847326983 165329204847326983 endpoint_16_73_p10 endpoint_16_73_w10
private theorem endpoint_16_73_w12 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 12 2 165329204847326983 = some 165329204847326983 := by decide +kernel
private theorem endpoint_16_73_p14 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 14 162103247210826382 = some 165329204847326983 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 12 2 162103247210826382 165329204847326983 165329204847326983 endpoint_16_73_p12 endpoint_16_73_w12
private theorem endpoint_16_73_w14 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 14 1 165329204847326983 = some 165329204847326983 := by decide +kernel
private theorem endpoint_16_73_p15 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 15 162103247210826382 = some 165329204847326983 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 14 1 162103247210826382 165329204847326983 165329204847326983 endpoint_16_73_p14 endpoint_16_73_w14
def endpoint_16_73 : CertifiedEndpoint :=
  ⟨⟨16, 73, 1189⟩, 165329204847326983, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_16_73_flag endpoint_16_73_sources 15 162103247210826382 165329204847326983 rfl endpoint_16_73_base endpoint_16_73_p15) (by decide)⟩
private def endpoint_16_74_flag : Flag := ⟨16, 74, 1106⟩
private def endpoint_16_74_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_16_74_base : receiptBase endpoint_16_74_flag endpoint_16_74_sources = some 152751764283111545 := by decide +kernel
private theorem endpoint_16_74_w0 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 2 152751764283111545 = some 161186911943622010 := by decide +kernel
private theorem endpoint_16_74_w2 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 2 2 161186911943622010 = some 161186911943622010 := by decide +kernel
private theorem endpoint_16_74_p4 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 4 152751764283111545 = some 161186911943622010 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 2 2 152751764283111545 161186911943622010 161186911943622010 endpoint_16_74_w0 endpoint_16_74_w2
private theorem endpoint_16_74_w4 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 4 2 161186911943622010 = some 161186911943622010 := by decide +kernel
private theorem endpoint_16_74_p6 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 6 152751764283111545 = some 161186911943622010 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 4 2 152751764283111545 161186911943622010 161186911943622010 endpoint_16_74_p4 endpoint_16_74_w4
private theorem endpoint_16_74_w6 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 6 2 161186911943622010 = some 161186911943622010 := by decide +kernel
private theorem endpoint_16_74_p8 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 8 152751764283111545 = some 161186911943622010 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 6 2 152751764283111545 161186911943622010 161186911943622010 endpoint_16_74_p6 endpoint_16_74_w6
private theorem endpoint_16_74_w8 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 8 2 161186911943622010 = some 161186911943622010 := by decide +kernel
private theorem endpoint_16_74_p10 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 10 152751764283111545 = some 161186911943622010 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 8 2 152751764283111545 161186911943622010 161186911943622010 endpoint_16_74_p8 endpoint_16_74_w8
private theorem endpoint_16_74_w10 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 10 2 161186911943622010 = some 161186911943622010 := by decide +kernel
private theorem endpoint_16_74_p12 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 12 152751764283111545 = some 161186911943622010 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 10 2 152751764283111545 161186911943622010 161186911943622010 endpoint_16_74_p10 endpoint_16_74_w10
private theorem endpoint_16_74_w12 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 12 2 161186911943622010 = some 161186911943622010 := by decide +kernel
private theorem endpoint_16_74_p14 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 14 152751764283111545 = some 161186911943622010 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 12 2 152751764283111545 161186911943622010 161186911943622010 endpoint_16_74_p12 endpoint_16_74_w12
private theorem endpoint_16_74_w14 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 14 1 161186911943622010 = some 161186911943622010 := by decide +kernel
private theorem endpoint_16_74_p15 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 15 152751764283111545 = some 161186911943622010 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 14 1 152751764283111545 161186911943622010 161186911943622010 endpoint_16_74_p14 endpoint_16_74_w14
def endpoint_16_74 : CertifiedEndpoint :=
  ⟨⟨16, 74, 1106⟩, 161186911943622010, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_16_74_flag endpoint_16_74_sources 15 152751764283111545 161186911943622010 rfl endpoint_16_74_base endpoint_16_74_p15) (by decide)⟩
private def endpoint_16_75_flag : Flag := ⟨16, 75, 1020⟩
private def endpoint_16_75_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_16_75_base : receiptBase endpoint_16_75_flag endpoint_16_75_sources = some 142716177141742384 := by decide +kernel
private theorem endpoint_16_75_w0 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 2 142716177141742384 = some 156594589587651574 := by decide +kernel
private theorem endpoint_16_75_w2 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 2 2 156594589587651574 = some 156594589587651574 := by decide +kernel
private theorem endpoint_16_75_p4 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 4 142716177141742384 = some 156594589587651574 :=
  join_receipt_window endpoint_16_75_flag endpoint_16_75_sources 0 2 2 142716177141742384 156594589587651574 156594589587651574 endpoint_16_75_w0 endpoint_16_75_w2
private theorem endpoint_16_75_w4 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 4 2 156594589587651574 = some 156594589587651574 := by decide +kernel
private theorem endpoint_16_75_p6 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 6 142716177141742384 = some 156594589587651574 :=
  join_receipt_window endpoint_16_75_flag endpoint_16_75_sources 0 4 2 142716177141742384 156594589587651574 156594589587651574 endpoint_16_75_p4 endpoint_16_75_w4
private theorem endpoint_16_75_w6 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 6 2 156594589587651574 = some 156594589587651574 := by decide +kernel
private theorem endpoint_16_75_p8 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 8 142716177141742384 = some 156594589587651574 :=
  join_receipt_window endpoint_16_75_flag endpoint_16_75_sources 0 6 2 142716177141742384 156594589587651574 156594589587651574 endpoint_16_75_p6 endpoint_16_75_w6
private theorem endpoint_16_75_w8 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 8 2 156594589587651574 = some 156594589587651574 := by decide +kernel
private theorem endpoint_16_75_p10 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 10 142716177141742384 = some 156594589587651574 :=
  join_receipt_window endpoint_16_75_flag endpoint_16_75_sources 0 8 2 142716177141742384 156594589587651574 156594589587651574 endpoint_16_75_p8 endpoint_16_75_w8
private theorem endpoint_16_75_w10 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 10 2 156594589587651574 = some 156594589587651574 := by decide +kernel
private theorem endpoint_16_75_p12 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 12 142716177141742384 = some 156594589587651574 :=
  join_receipt_window endpoint_16_75_flag endpoint_16_75_sources 0 10 2 142716177141742384 156594589587651574 156594589587651574 endpoint_16_75_p10 endpoint_16_75_w10
private theorem endpoint_16_75_w12 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 12 2 156594589587651574 = some 156594589587651574 := by decide +kernel
private theorem endpoint_16_75_p14 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 14 142716177141742384 = some 156594589587651574 :=
  join_receipt_window endpoint_16_75_flag endpoint_16_75_sources 0 12 2 142716177141742384 156594589587651574 156594589587651574 endpoint_16_75_p12 endpoint_16_75_w12
private theorem endpoint_16_75_w14 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 14 1 156594589587651574 = some 156594589587651574 := by decide +kernel
private theorem endpoint_16_75_p15 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 15 142716177141742384 = some 156594589587651574 :=
  join_receipt_window endpoint_16_75_flag endpoint_16_75_sources 0 14 1 142716177141742384 156594589587651574 156594589587651574 endpoint_16_75_p14 endpoint_16_75_w14
def endpoint_16_75 : CertifiedEndpoint :=
  ⟨⟨16, 75, 1020⟩, 156594589587651574, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_16_75_flag endpoint_16_75_sources 15 142716177141742384 156594589587651574 rfl endpoint_16_75_base endpoint_16_75_p15) (by decide)⟩
def endpoint_16_76 : CertifiedEndpoint :=
  ⟨⟨16, 76, 932⟩, 240461376254840636, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_77 : CertifiedEndpoint :=
  ⟨⟨16, 77, 841⟩, 218932408067473206, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_78 : CertifiedEndpoint :=
  ⟨⟨16, 78, 748⟩, 196114453711261704, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_79 : CertifiedEndpoint :=
  ⟨⟨16, 79, 652⟩, 171701274362630713, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_80 : CertifiedEndpoint :=
  ⟨⟨16, 80, 554⟩, 145943066719098222, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_81 : CertifiedEndpoint :=
  ⟨⟨16, 81, 453⟩, 118525585939080610, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_82 : CertifiedEndpoint :=
  ⟨⟨16, 82, 349⟩, 89412804941540959, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_83 : CertifiedEndpoint :=
  ⟨⟨16, 83, 243⟩, 58866929451009564, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_84 : CertifiedEndpoint :=
  ⟨⟨16, 84, 133⟩, 26259469784319183, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_17 : CertifiedEndpoint :=
  ⟨⟨17, 17, 3439⟩, 136430194533965924, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_18 : CertifiedEndpoint :=
  ⟨⟨17, 18, 3413⟩, 140147254394217520, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_19 : CertifiedEndpoint :=
  ⟨⟨17, 19, 3387⟩, 143791504145645040, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_20 : CertifiedEndpoint :=
  ⟨⟨17, 20, 3361⟩, 156920667705303529, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_21 : CertifiedEndpoint :=
  ⟨⟨17, 21, 3335⟩, 169824013458294256, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_22 : CertifiedEndpoint :=
  ⟨⟨17, 22, 3308⟩, 182446143493703932, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_23 : CertifiedEndpoint :=
  ⟨⟨17, 23, 3280⟩, 194774275671532495, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_24 : CertifiedEndpoint :=
  ⟨⟨17, 24, 3252⟩, 206859547189359880, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_25 : CertifiedEndpoint :=
  ⟨⟨17, 25, 3223⟩, 218633777996272736, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_26 : CertifiedEndpoint :=
  ⟨⟨17, 26, 3194⟩, 230156626716517706, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_27 : CertifiedEndpoint :=
  ⟨⟨17, 27, 3165⟩, 241428093350094790, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_28 : CertifiedEndpoint :=
  ⟨⟨17, 28, 3135⟩, 252367215706090575, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_17_29_flag : Flag := ⟨17, 29, 3104⟩
private def endpoint_17_29_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_29_base : receiptBase endpoint_17_29_flag endpoint_17_29_sources = some 181362670926083623 := by decide +kernel
private theorem endpoint_17_29_w0 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 2 181362670926083623 = some 181362670926083623 := by decide +kernel
private theorem endpoint_17_29_w2 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 2 2 181362670926083623 = some 181362670926083623 := by decide +kernel
private theorem endpoint_17_29_p4 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 4 181362670926083623 = some 181362670926083623 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 2 2 181362670926083623 181362670926083623 181362670926083623 endpoint_17_29_w0 endpoint_17_29_w2
private theorem endpoint_17_29_w4 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 4 2 181362670926083623 = some 181362670926083623 := by decide +kernel
private theorem endpoint_17_29_p6 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 6 181362670926083623 = some 181362670926083623 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 4 2 181362670926083623 181362670926083623 181362670926083623 endpoint_17_29_p4 endpoint_17_29_w4
private theorem endpoint_17_29_w6 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 6 2 181362670926083623 = some 181362670926083623 := by decide +kernel
private theorem endpoint_17_29_p8 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 8 181362670926083623 = some 181362670926083623 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 6 2 181362670926083623 181362670926083623 181362670926083623 endpoint_17_29_p6 endpoint_17_29_w6
private theorem endpoint_17_29_w8 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 8 2 181362670926083623 = some 181362670926083623 := by decide +kernel
private theorem endpoint_17_29_p10 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 10 181362670926083623 = some 181362670926083623 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 8 2 181362670926083623 181362670926083623 181362670926083623 endpoint_17_29_p8 endpoint_17_29_w8
private theorem endpoint_17_29_w10 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 10 2 181362670926083623 = some 181362670926083623 := by decide +kernel
private theorem endpoint_17_29_p12 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 12 181362670926083623 = some 181362670926083623 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 10 2 181362670926083623 181362670926083623 181362670926083623 endpoint_17_29_p10 endpoint_17_29_w10
private theorem endpoint_17_29_w12 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 12 2 181362670926083623 = some 181362670926083623 := by decide +kernel
private theorem endpoint_17_29_p14 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 14 181362670926083623 = some 181362670926083623 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 12 2 181362670926083623 181362670926083623 181362670926083623 endpoint_17_29_p12 endpoint_17_29_w12
private theorem endpoint_17_29_w14 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 14 2 181362670926083623 = some 181362670926083623 := by decide +kernel
private theorem endpoint_17_29_p16 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 16 181362670926083623 = some 181362670926083623 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 14 2 181362670926083623 181362670926083623 181362670926083623 endpoint_17_29_p14 endpoint_17_29_w14
def endpoint_17_29 : CertifiedEndpoint :=
  ⟨⟨17, 29, 3104⟩, 181362670926083623, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_29_flag endpoint_17_29_sources 16 181362670926083623 181362670926083623 rfl endpoint_17_29_base endpoint_17_29_p16) (by decide)⟩
private def endpoint_17_30_flag : Flag := ⟨17, 30, 3073⟩
private def endpoint_17_30_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_30_base : receiptBase endpoint_17_30_flag endpoint_17_30_sources = some 184622647484729566 := by decide +kernel
private theorem endpoint_17_30_w0 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 2 184622647484729566 = some 184622647484729566 := by decide +kernel
private theorem endpoint_17_30_w2 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 2 2 184622647484729566 = some 184622647484729566 := by decide +kernel
private theorem endpoint_17_30_p4 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 4 184622647484729566 = some 184622647484729566 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 2 2 184622647484729566 184622647484729566 184622647484729566 endpoint_17_30_w0 endpoint_17_30_w2
private theorem endpoint_17_30_w4 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 4 2 184622647484729566 = some 184622647484729566 := by decide +kernel
private theorem endpoint_17_30_p6 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 6 184622647484729566 = some 184622647484729566 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 4 2 184622647484729566 184622647484729566 184622647484729566 endpoint_17_30_p4 endpoint_17_30_w4
private theorem endpoint_17_30_w6 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 6 2 184622647484729566 = some 184622647484729566 := by decide +kernel
private theorem endpoint_17_30_p8 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 8 184622647484729566 = some 184622647484729566 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 6 2 184622647484729566 184622647484729566 184622647484729566 endpoint_17_30_p6 endpoint_17_30_w6
private theorem endpoint_17_30_w8 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 8 2 184622647484729566 = some 184622647484729566 := by decide +kernel
private theorem endpoint_17_30_p10 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 10 184622647484729566 = some 184622647484729566 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 8 2 184622647484729566 184622647484729566 184622647484729566 endpoint_17_30_p8 endpoint_17_30_w8
private theorem endpoint_17_30_w10 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 10 2 184622647484729566 = some 184622647484729566 := by decide +kernel
private theorem endpoint_17_30_p12 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 12 184622647484729566 = some 184622647484729566 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 10 2 184622647484729566 184622647484729566 184622647484729566 endpoint_17_30_p10 endpoint_17_30_w10
private theorem endpoint_17_30_w12 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 12 2 184622647484729566 = some 184622647484729566 := by decide +kernel
private theorem endpoint_17_30_p14 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 14 184622647484729566 = some 184622647484729566 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 12 2 184622647484729566 184622647484729566 184622647484729566 endpoint_17_30_p12 endpoint_17_30_w12
private theorem endpoint_17_30_w14 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 14 2 184622647484729566 = some 184622647484729566 := by decide +kernel
private theorem endpoint_17_30_p16 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 16 184622647484729566 = some 184622647484729566 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 14 2 184622647484729566 184622647484729566 184622647484729566 endpoint_17_30_p14 endpoint_17_30_w14
def endpoint_17_30 : CertifiedEndpoint :=
  ⟨⟨17, 30, 3073⟩, 184622647484729566, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_30_flag endpoint_17_30_sources 16 184622647484729566 184622647484729566 rfl endpoint_17_30_base endpoint_17_30_p16) (by decide)⟩
private def endpoint_17_31_flag : Flag := ⟨17, 31, 3042⟩
private def endpoint_17_31_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_31_base : receiptBase endpoint_17_31_flag endpoint_17_31_sources = some 187781032478391054 := by decide +kernel
private theorem endpoint_17_31_w0 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 2 187781032478391054 = some 187781032478391054 := by decide +kernel
private theorem endpoint_17_31_w2 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 2 2 187781032478391054 = some 187781032478391054 := by decide +kernel
private theorem endpoint_17_31_p4 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 4 187781032478391054 = some 187781032478391054 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 2 2 187781032478391054 187781032478391054 187781032478391054 endpoint_17_31_w0 endpoint_17_31_w2
private theorem endpoint_17_31_w4 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 4 2 187781032478391054 = some 187781032478391054 := by decide +kernel
private theorem endpoint_17_31_p6 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 6 187781032478391054 = some 187781032478391054 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 4 2 187781032478391054 187781032478391054 187781032478391054 endpoint_17_31_p4 endpoint_17_31_w4
private theorem endpoint_17_31_w6 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 6 2 187781032478391054 = some 187781032478391054 := by decide +kernel
private theorem endpoint_17_31_p8 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 8 187781032478391054 = some 187781032478391054 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 6 2 187781032478391054 187781032478391054 187781032478391054 endpoint_17_31_p6 endpoint_17_31_w6
private theorem endpoint_17_31_w8 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 8 2 187781032478391054 = some 187781032478391054 := by decide +kernel
private theorem endpoint_17_31_p10 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 10 187781032478391054 = some 187781032478391054 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 8 2 187781032478391054 187781032478391054 187781032478391054 endpoint_17_31_p8 endpoint_17_31_w8
private theorem endpoint_17_31_w10 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 10 2 187781032478391054 = some 187781032478391054 := by decide +kernel
private theorem endpoint_17_31_p12 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 12 187781032478391054 = some 187781032478391054 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 10 2 187781032478391054 187781032478391054 187781032478391054 endpoint_17_31_p10 endpoint_17_31_w10
private theorem endpoint_17_31_w12 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 12 2 187781032478391054 = some 187781032478391054 := by decide +kernel
private theorem endpoint_17_31_p14 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 14 187781032478391054 = some 187781032478391054 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 12 2 187781032478391054 187781032478391054 187781032478391054 endpoint_17_31_p12 endpoint_17_31_w12
private theorem endpoint_17_31_w14 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 14 2 187781032478391054 = some 187781032478391054 := by decide +kernel
private theorem endpoint_17_31_p16 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 16 187781032478391054 = some 187781032478391054 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 14 2 187781032478391054 187781032478391054 187781032478391054 endpoint_17_31_p14 endpoint_17_31_w14
def endpoint_17_31 : CertifiedEndpoint :=
  ⟨⟨17, 31, 3042⟩, 187781032478391054, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_31_flag endpoint_17_31_sources 16 187781032478391054 187781032478391054 rfl endpoint_17_31_base endpoint_17_31_p16) (by decide)⟩
private def endpoint_17_32_flag : Flag := ⟨17, 32, 3010⟩
private def endpoint_17_32_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_32_base : receiptBase endpoint_17_32_flag endpoint_17_32_sources = some 190775206687468766 := by decide +kernel
private theorem endpoint_17_32_w0 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 2 190775206687468766 = some 190775206687468766 := by decide +kernel
private theorem endpoint_17_32_w2 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 2 2 190775206687468766 = some 190775206687468766 := by decide +kernel
private theorem endpoint_17_32_p4 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 4 190775206687468766 = some 190775206687468766 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 2 2 190775206687468766 190775206687468766 190775206687468766 endpoint_17_32_w0 endpoint_17_32_w2
private theorem endpoint_17_32_w4 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 4 2 190775206687468766 = some 190775206687468766 := by decide +kernel
private theorem endpoint_17_32_p6 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 6 190775206687468766 = some 190775206687468766 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 4 2 190775206687468766 190775206687468766 190775206687468766 endpoint_17_32_p4 endpoint_17_32_w4
private theorem endpoint_17_32_w6 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 6 2 190775206687468766 = some 190775206687468766 := by decide +kernel
private theorem endpoint_17_32_p8 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 8 190775206687468766 = some 190775206687468766 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 6 2 190775206687468766 190775206687468766 190775206687468766 endpoint_17_32_p6 endpoint_17_32_w6
private theorem endpoint_17_32_w8 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 8 2 190775206687468766 = some 190775206687468766 := by decide +kernel
private theorem endpoint_17_32_p10 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 10 190775206687468766 = some 190775206687468766 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 8 2 190775206687468766 190775206687468766 190775206687468766 endpoint_17_32_p8 endpoint_17_32_w8
private theorem endpoint_17_32_w10 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 10 2 190775206687468766 = some 190775206687468766 := by decide +kernel
private theorem endpoint_17_32_p12 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 12 190775206687468766 = some 190775206687468766 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 10 2 190775206687468766 190775206687468766 190775206687468766 endpoint_17_32_p10 endpoint_17_32_w10
private theorem endpoint_17_32_w12 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 12 2 190775206687468766 = some 190775206687468766 := by decide +kernel
private theorem endpoint_17_32_p14 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 14 190775206687468766 = some 190775206687468766 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 12 2 190775206687468766 190775206687468766 190775206687468766 endpoint_17_32_p12 endpoint_17_32_w12
private theorem endpoint_17_32_w14 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 14 2 190775206687468766 = some 190775206687468766 := by decide +kernel
private theorem endpoint_17_32_p16 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 16 190775206687468766 = some 190775206687468766 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 14 2 190775206687468766 190775206687468766 190775206687468766 endpoint_17_32_p14 endpoint_17_32_w14
def endpoint_17_32 : CertifiedEndpoint :=
  ⟨⟨17, 32, 3010⟩, 190775206687468766, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_32_flag endpoint_17_32_sources 16 190775206687468766 190775206687468766 rfl endpoint_17_32_base endpoint_17_32_p16) (by decide)⟩
private def endpoint_17_33_flag : Flag := ⟨17, 33, 2977⟩
private def endpoint_17_33_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_33_base : receiptBase endpoint_17_33_flag endpoint_17_33_sources = some 193600332761219062 := by decide +kernel
private theorem endpoint_17_33_w0 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 2 193600332761219062 = some 193600332761219062 := by decide +kernel
private theorem endpoint_17_33_w2 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 2 2 193600332761219062 = some 193600332761219062 := by decide +kernel
private theorem endpoint_17_33_p4 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 4 193600332761219062 = some 193600332761219062 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 2 2 193600332761219062 193600332761219062 193600332761219062 endpoint_17_33_w0 endpoint_17_33_w2
private theorem endpoint_17_33_w4 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 4 2 193600332761219062 = some 193600332761219062 := by decide +kernel
private theorem endpoint_17_33_p6 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 6 193600332761219062 = some 193600332761219062 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 4 2 193600332761219062 193600332761219062 193600332761219062 endpoint_17_33_p4 endpoint_17_33_w4
private theorem endpoint_17_33_w6 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 6 2 193600332761219062 = some 193600332761219062 := by decide +kernel
private theorem endpoint_17_33_p8 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 8 193600332761219062 = some 193600332761219062 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 6 2 193600332761219062 193600332761219062 193600332761219062 endpoint_17_33_p6 endpoint_17_33_w6
private theorem endpoint_17_33_w8 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 8 2 193600332761219062 = some 193600332761219062 := by decide +kernel
private theorem endpoint_17_33_p10 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 10 193600332761219062 = some 193600332761219062 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 8 2 193600332761219062 193600332761219062 193600332761219062 endpoint_17_33_p8 endpoint_17_33_w8
private theorem endpoint_17_33_w10 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 10 2 193600332761219062 = some 193600332761219062 := by decide +kernel
private theorem endpoint_17_33_p12 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 12 193600332761219062 = some 193600332761219062 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 10 2 193600332761219062 193600332761219062 193600332761219062 endpoint_17_33_p10 endpoint_17_33_w10
private theorem endpoint_17_33_w12 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 12 2 193600332761219062 = some 193600332761219062 := by decide +kernel
private theorem endpoint_17_33_p14 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 14 193600332761219062 = some 193600332761219062 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 12 2 193600332761219062 193600332761219062 193600332761219062 endpoint_17_33_p12 endpoint_17_33_w12
private theorem endpoint_17_33_w14 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 14 2 193600332761219062 = some 193600332761219062 := by decide +kernel
private theorem endpoint_17_33_p16 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 16 193600332761219062 = some 193600332761219062 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 14 2 193600332761219062 193600332761219062 193600332761219062 endpoint_17_33_p14 endpoint_17_33_w14
def endpoint_17_33 : CertifiedEndpoint :=
  ⟨⟨17, 33, 2977⟩, 193600332761219062, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_33_flag endpoint_17_33_sources 16 193600332761219062 193600332761219062 rfl endpoint_17_33_base endpoint_17_33_p16) (by decide)⟩
private def endpoint_17_34_flag : Flag := ⟨17, 34, 2943⟩
private def endpoint_17_34_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_17_34_base : receiptBase endpoint_17_34_flag endpoint_17_34_sources = some 195816640625673875 := by decide +kernel
private theorem endpoint_17_34_w0 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 2 195816640625673875 = some 195816640625673875 := by decide +kernel
private theorem endpoint_17_34_w2 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 2 2 195816640625673875 = some 195816640625673875 := by decide +kernel
private theorem endpoint_17_34_p4 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 4 195816640625673875 = some 195816640625673875 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 2 2 195816640625673875 195816640625673875 195816640625673875 endpoint_17_34_w0 endpoint_17_34_w2
private theorem endpoint_17_34_w4 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 4 2 195816640625673875 = some 195816640625673875 := by decide +kernel
private theorem endpoint_17_34_p6 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 6 195816640625673875 = some 195816640625673875 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 4 2 195816640625673875 195816640625673875 195816640625673875 endpoint_17_34_p4 endpoint_17_34_w4
private theorem endpoint_17_34_w6 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 6 2 195816640625673875 = some 195816640625673875 := by decide +kernel
private theorem endpoint_17_34_p8 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 8 195816640625673875 = some 195816640625673875 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 6 2 195816640625673875 195816640625673875 195816640625673875 endpoint_17_34_p6 endpoint_17_34_w6
private theorem endpoint_17_34_w8 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 8 2 195816640625673875 = some 195816640625673875 := by decide +kernel
private theorem endpoint_17_34_p10 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 10 195816640625673875 = some 195816640625673875 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 8 2 195816640625673875 195816640625673875 195816640625673875 endpoint_17_34_p8 endpoint_17_34_w8
private theorem endpoint_17_34_w10 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 10 2 195816640625673875 = some 195816640625673875 := by decide +kernel
private theorem endpoint_17_34_p12 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 12 195816640625673875 = some 195816640625673875 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 10 2 195816640625673875 195816640625673875 195816640625673875 endpoint_17_34_p10 endpoint_17_34_w10
private theorem endpoint_17_34_w12 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 12 2 195816640625673875 = some 195816640625673875 := by decide +kernel
private theorem endpoint_17_34_p14 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 14 195816640625673875 = some 195816640625673875 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 12 2 195816640625673875 195816640625673875 195816640625673875 endpoint_17_34_p12 endpoint_17_34_w12
private theorem endpoint_17_34_w14 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 14 2 195816640625673875 = some 195816640625673875 := by decide +kernel
private theorem endpoint_17_34_p16 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 16 195816640625673875 = some 195816640625673875 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 14 2 195816640625673875 195816640625673875 195816640625673875 endpoint_17_34_p14 endpoint_17_34_w14
def endpoint_17_34 : CertifiedEndpoint :=
  ⟨⟨17, 34, 2943⟩, 195816640625673875, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_17_34_flag endpoint_17_34_sources 16 195816640625673875 195816640625673875 rfl endpoint_17_34_base endpoint_17_34_p16) (by decide)⟩
private def endpoint_17_35_flag : Flag := ⟨17, 35, 2909⟩
private def endpoint_17_35_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_35_base : receiptBase endpoint_17_35_flag endpoint_17_35_sources = some 198791547670105809 := by decide +kernel
private theorem endpoint_17_35_w0 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 2 198791547670105809 = some 198791547670105809 := by decide +kernel
private theorem endpoint_17_35_w2 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 2 2 198791547670105809 = some 198791547670105809 := by decide +kernel
private theorem endpoint_17_35_p4 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 4 198791547670105809 = some 198791547670105809 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 2 2 198791547670105809 198791547670105809 198791547670105809 endpoint_17_35_w0 endpoint_17_35_w2
private theorem endpoint_17_35_w4 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 4 2 198791547670105809 = some 198791547670105809 := by decide +kernel
private theorem endpoint_17_35_p6 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 6 198791547670105809 = some 198791547670105809 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 4 2 198791547670105809 198791547670105809 198791547670105809 endpoint_17_35_p4 endpoint_17_35_w4
private theorem endpoint_17_35_w6 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 6 2 198791547670105809 = some 198791547670105809 := by decide +kernel
private theorem endpoint_17_35_p8 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 8 198791547670105809 = some 198791547670105809 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 6 2 198791547670105809 198791547670105809 198791547670105809 endpoint_17_35_p6 endpoint_17_35_w6
private theorem endpoint_17_35_w8 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 8 2 198791547670105809 = some 198791547670105809 := by decide +kernel
private theorem endpoint_17_35_p10 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 10 198791547670105809 = some 198791547670105809 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 8 2 198791547670105809 198791547670105809 198791547670105809 endpoint_17_35_p8 endpoint_17_35_w8
private theorem endpoint_17_35_w10 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 10 2 198791547670105809 = some 198791547670105809 := by decide +kernel
private theorem endpoint_17_35_p12 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 12 198791547670105809 = some 198791547670105809 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 10 2 198791547670105809 198791547670105809 198791547670105809 endpoint_17_35_p10 endpoint_17_35_w10
private theorem endpoint_17_35_w12 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 12 2 198791547670105809 = some 198791547670105809 := by decide +kernel
private theorem endpoint_17_35_p14 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 14 198791547670105809 = some 198791547670105809 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 12 2 198791547670105809 198791547670105809 198791547670105809 endpoint_17_35_p12 endpoint_17_35_w12
private theorem endpoint_17_35_w14 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 14 2 198791547670105809 = some 198791547670105809 := by decide +kernel
private theorem endpoint_17_35_p16 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 16 198791547670105809 = some 198791547670105809 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 14 2 198791547670105809 198791547670105809 198791547670105809 endpoint_17_35_p14 endpoint_17_35_w14
def endpoint_17_35 : CertifiedEndpoint :=
  ⟨⟨17, 35, 2909⟩, 198791547670105809, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_35_flag endpoint_17_35_sources 16 198791547670105809 198791547670105809 rfl endpoint_17_35_base endpoint_17_35_p16) (by decide)⟩
private def endpoint_17_36_flag : Flag := ⟨17, 36, 2875⟩
private def endpoint_17_36_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_36_base : receiptBase endpoint_17_36_flag endpoint_17_36_sources = some 201220255724841582 := by decide +kernel
private theorem endpoint_17_36_w0 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 2 201220255724841582 = some 201220255724841582 := by decide +kernel
private theorem endpoint_17_36_w2 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 2 2 201220255724841582 = some 201220255724841582 := by decide +kernel
private theorem endpoint_17_36_p4 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 4 201220255724841582 = some 201220255724841582 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 2 2 201220255724841582 201220255724841582 201220255724841582 endpoint_17_36_w0 endpoint_17_36_w2
private theorem endpoint_17_36_w4 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 4 2 201220255724841582 = some 201220255724841582 := by decide +kernel
private theorem endpoint_17_36_p6 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 6 201220255724841582 = some 201220255724841582 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 4 2 201220255724841582 201220255724841582 201220255724841582 endpoint_17_36_p4 endpoint_17_36_w4
private theorem endpoint_17_36_w6 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 6 2 201220255724841582 = some 201220255724841582 := by decide +kernel
private theorem endpoint_17_36_p8 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 8 201220255724841582 = some 201220255724841582 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 6 2 201220255724841582 201220255724841582 201220255724841582 endpoint_17_36_p6 endpoint_17_36_w6
private theorem endpoint_17_36_w8 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 8 2 201220255724841582 = some 201220255724841582 := by decide +kernel
private theorem endpoint_17_36_p10 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 10 201220255724841582 = some 201220255724841582 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 8 2 201220255724841582 201220255724841582 201220255724841582 endpoint_17_36_p8 endpoint_17_36_w8
private theorem endpoint_17_36_w10 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 10 2 201220255724841582 = some 201220255724841582 := by decide +kernel
private theorem endpoint_17_36_p12 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 12 201220255724841582 = some 201220255724841582 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 10 2 201220255724841582 201220255724841582 201220255724841582 endpoint_17_36_p10 endpoint_17_36_w10
private theorem endpoint_17_36_w12 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 12 2 201220255724841582 = some 201220255724841582 := by decide +kernel
private theorem endpoint_17_36_p14 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 14 201220255724841582 = some 201220255724841582 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 12 2 201220255724841582 201220255724841582 201220255724841582 endpoint_17_36_p12 endpoint_17_36_w12
private theorem endpoint_17_36_w14 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 14 2 201220255724841582 = some 201220255724841582 := by decide +kernel
private theorem endpoint_17_36_p16 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 16 201220255724841582 = some 201220255724841582 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 14 2 201220255724841582 201220255724841582 201220255724841582 endpoint_17_36_p14 endpoint_17_36_w14
def endpoint_17_36 : CertifiedEndpoint :=
  ⟨⟨17, 36, 2875⟩, 201220255724841582, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_36_flag endpoint_17_36_sources 16 201220255724841582 201220255724841582 rfl endpoint_17_36_base endpoint_17_36_p16) (by decide)⟩
private def endpoint_17_37_flag : Flag := ⟨17, 37, 2839⟩
private def endpoint_17_37_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_37_base : receiptBase endpoint_17_37_flag endpoint_17_37_sources = some 203396334571428180 := by decide +kernel
private theorem endpoint_17_37_w0 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 2 203396334571428180 = some 203396334571428180 := by decide +kernel
private theorem endpoint_17_37_w2 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 2 2 203396334571428180 = some 203396334571428180 := by decide +kernel
private theorem endpoint_17_37_p4 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 4 203396334571428180 = some 203396334571428180 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 2 2 203396334571428180 203396334571428180 203396334571428180 endpoint_17_37_w0 endpoint_17_37_w2
private theorem endpoint_17_37_w4 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 4 2 203396334571428180 = some 203396334571428180 := by decide +kernel
private theorem endpoint_17_37_p6 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 6 203396334571428180 = some 203396334571428180 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 4 2 203396334571428180 203396334571428180 203396334571428180 endpoint_17_37_p4 endpoint_17_37_w4
private theorem endpoint_17_37_w6 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 6 2 203396334571428180 = some 203396334571428180 := by decide +kernel
private theorem endpoint_17_37_p8 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 8 203396334571428180 = some 203396334571428180 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 6 2 203396334571428180 203396334571428180 203396334571428180 endpoint_17_37_p6 endpoint_17_37_w6
private theorem endpoint_17_37_w8 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 8 2 203396334571428180 = some 203396334571428180 := by decide +kernel
private theorem endpoint_17_37_p10 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 10 203396334571428180 = some 203396334571428180 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 8 2 203396334571428180 203396334571428180 203396334571428180 endpoint_17_37_p8 endpoint_17_37_w8
private theorem endpoint_17_37_w10 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 10 2 203396334571428180 = some 203396334571428180 := by decide +kernel
private theorem endpoint_17_37_p12 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 12 203396334571428180 = some 203396334571428180 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 10 2 203396334571428180 203396334571428180 203396334571428180 endpoint_17_37_p10 endpoint_17_37_w10
private theorem endpoint_17_37_w12 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 12 2 203396334571428180 = some 203396334571428180 := by decide +kernel
private theorem endpoint_17_37_p14 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 14 203396334571428180 = some 203396334571428180 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 12 2 203396334571428180 203396334571428180 203396334571428180 endpoint_17_37_p12 endpoint_17_37_w12
private theorem endpoint_17_37_w14 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 14 2 203396334571428180 = some 203396334571428180 := by decide +kernel
private theorem endpoint_17_37_p16 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 16 203396334571428180 = some 203396334571428180 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 14 2 203396334571428180 203396334571428180 203396334571428180 endpoint_17_37_p14 endpoint_17_37_w14
def endpoint_17_37 : CertifiedEndpoint :=
  ⟨⟨17, 37, 2839⟩, 203396334571428180, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_37_flag endpoint_17_37_sources 16 203396334571428180 203396334571428180 rfl endpoint_17_37_base endpoint_17_37_p16) (by decide)⟩
private def endpoint_17_38_flag : Flag := ⟨17, 38, 2803⟩
private def endpoint_17_38_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_38_base : receiptBase endpoint_17_38_flag endpoint_17_38_sources = some 205454697350551525 := by decide +kernel
private theorem endpoint_17_38_w0 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 2 205454697350551525 = some 205454697350551525 := by decide +kernel
private theorem endpoint_17_38_w2 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 2 2 205454697350551525 = some 205454697350551525 := by decide +kernel
private theorem endpoint_17_38_p4 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 4 205454697350551525 = some 205454697350551525 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 2 2 205454697350551525 205454697350551525 205454697350551525 endpoint_17_38_w0 endpoint_17_38_w2
private theorem endpoint_17_38_w4 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 4 2 205454697350551525 = some 205454697350551525 := by decide +kernel
private theorem endpoint_17_38_p6 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 6 205454697350551525 = some 205454697350551525 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 4 2 205454697350551525 205454697350551525 205454697350551525 endpoint_17_38_p4 endpoint_17_38_w4
private theorem endpoint_17_38_w6 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 6 2 205454697350551525 = some 205454697350551525 := by decide +kernel
private theorem endpoint_17_38_p8 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 8 205454697350551525 = some 205454697350551525 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 6 2 205454697350551525 205454697350551525 205454697350551525 endpoint_17_38_p6 endpoint_17_38_w6
private theorem endpoint_17_38_w8 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 8 2 205454697350551525 = some 205454697350551525 := by decide +kernel
private theorem endpoint_17_38_p10 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 10 205454697350551525 = some 205454697350551525 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 8 2 205454697350551525 205454697350551525 205454697350551525 endpoint_17_38_p8 endpoint_17_38_w8
private theorem endpoint_17_38_w10 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 10 2 205454697350551525 = some 205454697350551525 := by decide +kernel
private theorem endpoint_17_38_p12 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 12 205454697350551525 = some 205454697350551525 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 10 2 205454697350551525 205454697350551525 205454697350551525 endpoint_17_38_p10 endpoint_17_38_w10
private theorem endpoint_17_38_w12 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 12 2 205454697350551525 = some 205454697350551525 := by decide +kernel
private theorem endpoint_17_38_p14 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 14 205454697350551525 = some 205454697350551525 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 12 2 205454697350551525 205454697350551525 205454697350551525 endpoint_17_38_p12 endpoint_17_38_w12
private theorem endpoint_17_38_w14 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 14 2 205454697350551525 = some 205454697350551525 := by decide +kernel
private theorem endpoint_17_38_p16 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 16 205454697350551525 = some 205454697350551525 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 14 2 205454697350551525 205454697350551525 205454697350551525 endpoint_17_38_p14 endpoint_17_38_w14
def endpoint_17_38 : CertifiedEndpoint :=
  ⟨⟨17, 38, 2803⟩, 205454697350551525, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_38_flag endpoint_17_38_sources 16 205454697350551525 205454697350551525 rfl endpoint_17_38_base endpoint_17_38_p16) (by decide)⟩
private def endpoint_17_39_flag : Flag := ⟨17, 39, 2767⟩
private def endpoint_17_39_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_39_base : receiptBase endpoint_17_39_flag endpoint_17_39_sources = some 207395344062211617 := by decide +kernel
private theorem endpoint_17_39_w0 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 2 207395344062211617 = some 207395344062211617 := by decide +kernel
private theorem endpoint_17_39_w2 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 2 2 207395344062211617 = some 207395344062211617 := by decide +kernel
private theorem endpoint_17_39_p4 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 4 207395344062211617 = some 207395344062211617 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 2 2 207395344062211617 207395344062211617 207395344062211617 endpoint_17_39_w0 endpoint_17_39_w2
private theorem endpoint_17_39_w4 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 4 2 207395344062211617 = some 207395344062211617 := by decide +kernel
private theorem endpoint_17_39_p6 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 6 207395344062211617 = some 207395344062211617 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 4 2 207395344062211617 207395344062211617 207395344062211617 endpoint_17_39_p4 endpoint_17_39_w4
private theorem endpoint_17_39_w6 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 6 2 207395344062211617 = some 207395344062211617 := by decide +kernel
private theorem endpoint_17_39_p8 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 8 207395344062211617 = some 207395344062211617 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 6 2 207395344062211617 207395344062211617 207395344062211617 endpoint_17_39_p6 endpoint_17_39_w6
private theorem endpoint_17_39_w8 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 8 2 207395344062211617 = some 207395344062211617 := by decide +kernel
private theorem endpoint_17_39_p10 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 10 207395344062211617 = some 207395344062211617 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 8 2 207395344062211617 207395344062211617 207395344062211617 endpoint_17_39_p8 endpoint_17_39_w8
private theorem endpoint_17_39_w10 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 10 2 207395344062211617 = some 207395344062211617 := by decide +kernel
private theorem endpoint_17_39_p12 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 12 207395344062211617 = some 207395344062211617 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 10 2 207395344062211617 207395344062211617 207395344062211617 endpoint_17_39_p10 endpoint_17_39_w10
private theorem endpoint_17_39_w12 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 12 2 207395344062211617 = some 207395344062211617 := by decide +kernel
private theorem endpoint_17_39_p14 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 14 207395344062211617 = some 207395344062211617 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 12 2 207395344062211617 207395344062211617 207395344062211617 endpoint_17_39_p12 endpoint_17_39_w12
private theorem endpoint_17_39_w14 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 14 2 207395344062211617 = some 207395344062211617 := by decide +kernel
private theorem endpoint_17_39_p16 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 16 207395344062211617 = some 207395344062211617 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 14 2 207395344062211617 207395344062211617 207395344062211617 endpoint_17_39_p14 endpoint_17_39_w14
def endpoint_17_39 : CertifiedEndpoint :=
  ⟨⟨17, 39, 2767⟩, 207395344062211617, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_39_flag endpoint_17_39_sources 16 207395344062211617 207395344062211617 rfl endpoint_17_39_base endpoint_17_39_p16) (by decide)⟩
private def endpoint_17_40_flag : Flag := ⟨17, 40, 2729⟩
private def endpoint_17_40_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_40_base : receiptBase endpoint_17_40_flag endpoint_17_40_sources = some 209067237063243736 := by decide +kernel
private theorem endpoint_17_40_w0 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 2 209067237063243736 = some 209067237063243736 := by decide +kernel
private theorem endpoint_17_40_w2 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 2 2 209067237063243736 = some 209067237063243736 := by decide +kernel
private theorem endpoint_17_40_p4 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 4 209067237063243736 = some 209067237063243736 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 2 2 209067237063243736 209067237063243736 209067237063243736 endpoint_17_40_w0 endpoint_17_40_w2
private theorem endpoint_17_40_w4 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 4 2 209067237063243736 = some 209067237063243736 := by decide +kernel
private theorem endpoint_17_40_p6 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 6 209067237063243736 = some 209067237063243736 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 4 2 209067237063243736 209067237063243736 209067237063243736 endpoint_17_40_p4 endpoint_17_40_w4
private theorem endpoint_17_40_w6 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 6 2 209067237063243736 = some 209067237063243736 := by decide +kernel
private theorem endpoint_17_40_p8 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 8 209067237063243736 = some 209067237063243736 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 6 2 209067237063243736 209067237063243736 209067237063243736 endpoint_17_40_p6 endpoint_17_40_w6
private theorem endpoint_17_40_w8 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 8 2 209067237063243736 = some 209067237063243736 := by decide +kernel
private theorem endpoint_17_40_p10 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 10 209067237063243736 = some 209067237063243736 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 8 2 209067237063243736 209067237063243736 209067237063243736 endpoint_17_40_p8 endpoint_17_40_w8
private theorem endpoint_17_40_w10 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 10 2 209067237063243736 = some 209067237063243736 := by decide +kernel
private theorem endpoint_17_40_p12 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 12 209067237063243736 = some 209067237063243736 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 10 2 209067237063243736 209067237063243736 209067237063243736 endpoint_17_40_p10 endpoint_17_40_w10
private theorem endpoint_17_40_w12 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 12 2 209067237063243736 = some 209067237063243736 := by decide +kernel
private theorem endpoint_17_40_p14 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 14 209067237063243736 = some 209067237063243736 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 12 2 209067237063243736 209067237063243736 209067237063243736 endpoint_17_40_p12 endpoint_17_40_w12
private theorem endpoint_17_40_w14 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 14 2 209067237063243736 = some 209067237063243736 := by decide +kernel
private theorem endpoint_17_40_p16 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 16 209067237063243736 = some 209067237063243736 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 14 2 209067237063243736 209067237063243736 209067237063243736 endpoint_17_40_p14 endpoint_17_40_w14
def endpoint_17_40 : CertifiedEndpoint :=
  ⟨⟨17, 40, 2729⟩, 209067237063243736, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_40_flag endpoint_17_40_sources 16 209067237063243736 209067237063243736 rfl endpoint_17_40_base endpoint_17_40_p16) (by decide)⟩
private def endpoint_17_41_flag : Flag := ⟨17, 41, 2691⟩
private def endpoint_17_41_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_41_base : receiptBase endpoint_17_41_flag endpoint_17_41_sources = some 211253689543259776 := by decide +kernel
private theorem endpoint_17_41_w0 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 2 211253689543259776 = some 211253689543259776 := by decide +kernel
private theorem endpoint_17_41_w2 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 2 2 211253689543259776 = some 211253689543259776 := by decide +kernel
private theorem endpoint_17_41_p4 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 4 211253689543259776 = some 211253689543259776 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 2 2 211253689543259776 211253689543259776 211253689543259776 endpoint_17_41_w0 endpoint_17_41_w2
private theorem endpoint_17_41_w4 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 4 2 211253689543259776 = some 211253689543259776 := by decide +kernel
private theorem endpoint_17_41_p6 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 6 211253689543259776 = some 211253689543259776 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 4 2 211253689543259776 211253689543259776 211253689543259776 endpoint_17_41_p4 endpoint_17_41_w4
private theorem endpoint_17_41_w6 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 6 2 211253689543259776 = some 211253689543259776 := by decide +kernel
private theorem endpoint_17_41_p8 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 8 211253689543259776 = some 211253689543259776 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 6 2 211253689543259776 211253689543259776 211253689543259776 endpoint_17_41_p6 endpoint_17_41_w6
private theorem endpoint_17_41_w8 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 8 2 211253689543259776 = some 211253689543259776 := by decide +kernel
private theorem endpoint_17_41_p10 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 10 211253689543259776 = some 211253689543259776 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 8 2 211253689543259776 211253689543259776 211253689543259776 endpoint_17_41_p8 endpoint_17_41_w8
private theorem endpoint_17_41_w10 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 10 2 211253689543259776 = some 211253689543259776 := by decide +kernel
private theorem endpoint_17_41_p12 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 12 211253689543259776 = some 211253689543259776 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 10 2 211253689543259776 211253689543259776 211253689543259776 endpoint_17_41_p10 endpoint_17_41_w10
private theorem endpoint_17_41_w12 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 12 2 211253689543259776 = some 211253689543259776 := by decide +kernel
private theorem endpoint_17_41_p14 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 14 211253689543259776 = some 211253689543259776 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 12 2 211253689543259776 211253689543259776 211253689543259776 endpoint_17_41_p12 endpoint_17_41_w12
private theorem endpoint_17_41_w14 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 14 2 211253689543259776 = some 211253689543259776 := by decide +kernel
private theorem endpoint_17_41_p16 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 16 211253689543259776 = some 211253689543259776 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 14 2 211253689543259776 211253689543259776 211253689543259776 endpoint_17_41_p14 endpoint_17_41_w14
def endpoint_17_41 : CertifiedEndpoint :=
  ⟨⟨17, 41, 2691⟩, 211253689543259776, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_41_flag endpoint_17_41_sources 16 211253689543259776 211253689543259776 rfl endpoint_17_41_base endpoint_17_41_p16) (by decide)⟩
private def endpoint_17_42_flag : Flag := ⟨17, 42, 2652⟩
private def endpoint_17_42_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_42_base : receiptBase endpoint_17_42_flag endpoint_17_42_sources = some 212586823168365486 := by decide +kernel
private theorem endpoint_17_42_w0 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 2 212586823168365486 = some 212586823168365486 := by decide +kernel
private theorem endpoint_17_42_w2 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 2 2 212586823168365486 = some 212586823168365486 := by decide +kernel
private theorem endpoint_17_42_p4 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 4 212586823168365486 = some 212586823168365486 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 2 2 212586823168365486 212586823168365486 212586823168365486 endpoint_17_42_w0 endpoint_17_42_w2
private theorem endpoint_17_42_w4 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 4 2 212586823168365486 = some 212586823168365486 := by decide +kernel
private theorem endpoint_17_42_p6 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 6 212586823168365486 = some 212586823168365486 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 4 2 212586823168365486 212586823168365486 212586823168365486 endpoint_17_42_p4 endpoint_17_42_w4
private theorem endpoint_17_42_w6 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 6 2 212586823168365486 = some 212586823168365486 := by decide +kernel
private theorem endpoint_17_42_p8 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 8 212586823168365486 = some 212586823168365486 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 6 2 212586823168365486 212586823168365486 212586823168365486 endpoint_17_42_p6 endpoint_17_42_w6
private theorem endpoint_17_42_w8 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 8 2 212586823168365486 = some 212586823168365486 := by decide +kernel
private theorem endpoint_17_42_p10 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 10 212586823168365486 = some 212586823168365486 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 8 2 212586823168365486 212586823168365486 212586823168365486 endpoint_17_42_p8 endpoint_17_42_w8
private theorem endpoint_17_42_w10 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 10 2 212586823168365486 = some 212586823168365486 := by decide +kernel
private theorem endpoint_17_42_p12 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 12 212586823168365486 = some 212586823168365486 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 10 2 212586823168365486 212586823168365486 212586823168365486 endpoint_17_42_p10 endpoint_17_42_w10
private theorem endpoint_17_42_w12 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 12 2 212586823168365486 = some 212586823168365486 := by decide +kernel
private theorem endpoint_17_42_p14 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 14 212586823168365486 = some 212586823168365486 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 12 2 212586823168365486 212586823168365486 212586823168365486 endpoint_17_42_p12 endpoint_17_42_w12
private theorem endpoint_17_42_w14 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 14 2 212586823168365486 = some 212586823168365486 := by decide +kernel
private theorem endpoint_17_42_p16 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 16 212586823168365486 = some 212586823168365486 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 14 2 212586823168365486 212586823168365486 212586823168365486 endpoint_17_42_p14 endpoint_17_42_w14
def endpoint_17_42 : CertifiedEndpoint :=
  ⟨⟨17, 42, 2652⟩, 212586823168365486, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_42_flag endpoint_17_42_sources 16 212586823168365486 212586823168365486 rfl endpoint_17_42_base endpoint_17_42_p16) (by decide)⟩
private def endpoint_17_43_flag : Flag := ⟨17, 43, 2612⟩
private def endpoint_17_43_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_43_base : receiptBase endpoint_17_43_flag endpoint_17_43_sources = some 213711784374654398 := by decide +kernel
private theorem endpoint_17_43_w0 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 2 213711784374654398 = some 213711784374654398 := by decide +kernel
private theorem endpoint_17_43_w2 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 2 2 213711784374654398 = some 213711784374654398 := by decide +kernel
private theorem endpoint_17_43_p4 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 4 213711784374654398 = some 213711784374654398 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 2 2 213711784374654398 213711784374654398 213711784374654398 endpoint_17_43_w0 endpoint_17_43_w2
private theorem endpoint_17_43_w4 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 4 2 213711784374654398 = some 213711784374654398 := by decide +kernel
private theorem endpoint_17_43_p6 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 6 213711784374654398 = some 213711784374654398 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 4 2 213711784374654398 213711784374654398 213711784374654398 endpoint_17_43_p4 endpoint_17_43_w4
private theorem endpoint_17_43_w6 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 6 2 213711784374654398 = some 213711784374654398 := by decide +kernel
private theorem endpoint_17_43_p8 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 8 213711784374654398 = some 213711784374654398 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 6 2 213711784374654398 213711784374654398 213711784374654398 endpoint_17_43_p6 endpoint_17_43_w6
private theorem endpoint_17_43_w8 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 8 2 213711784374654398 = some 213711784374654398 := by decide +kernel
private theorem endpoint_17_43_p10 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 10 213711784374654398 = some 213711784374654398 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 8 2 213711784374654398 213711784374654398 213711784374654398 endpoint_17_43_p8 endpoint_17_43_w8
private theorem endpoint_17_43_w10 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 10 2 213711784374654398 = some 213711784374654398 := by decide +kernel
private theorem endpoint_17_43_p12 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 12 213711784374654398 = some 213711784374654398 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 10 2 213711784374654398 213711784374654398 213711784374654398 endpoint_17_43_p10 endpoint_17_43_w10
private theorem endpoint_17_43_w12 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 12 2 213711784374654398 = some 213711784374654398 := by decide +kernel
private theorem endpoint_17_43_p14 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 14 213711784374654398 = some 213711784374654398 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 12 2 213711784374654398 213711784374654398 213711784374654398 endpoint_17_43_p12 endpoint_17_43_w12
private theorem endpoint_17_43_w14 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 14 2 213711784374654398 = some 213711784374654398 := by decide +kernel
private theorem endpoint_17_43_p16 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 16 213711784374654398 = some 213711784374654398 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 14 2 213711784374654398 213711784374654398 213711784374654398 endpoint_17_43_p14 endpoint_17_43_w14
def endpoint_17_43 : CertifiedEndpoint :=
  ⟨⟨17, 43, 2612⟩, 213711784374654398, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_43_flag endpoint_17_43_sources 16 213711784374654398 213711784374654398 rfl endpoint_17_43_base endpoint_17_43_p16) (by decide)⟩
private def endpoint_17_44_flag : Flag := ⟨17, 44, 2572⟩
private def endpoint_17_44_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_44_base : receiptBase endpoint_17_44_flag endpoint_17_44_sources = some 214705990216321291 := by decide +kernel
private theorem endpoint_17_44_w0 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 2 214705990216321291 = some 217361537248558776 := by decide +kernel
private theorem endpoint_17_44_w2 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 2 2 217361537248558776 = some 217361537248558776 := by decide +kernel
private theorem endpoint_17_44_p4 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 4 214705990216321291 = some 217361537248558776 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 2 2 214705990216321291 217361537248558776 217361537248558776 endpoint_17_44_w0 endpoint_17_44_w2
private theorem endpoint_17_44_w4 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 4 2 217361537248558776 = some 217361537248558776 := by decide +kernel
private theorem endpoint_17_44_p6 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 6 214705990216321291 = some 217361537248558776 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 4 2 214705990216321291 217361537248558776 217361537248558776 endpoint_17_44_p4 endpoint_17_44_w4
private theorem endpoint_17_44_w6 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 6 2 217361537248558776 = some 217361537248558776 := by decide +kernel
private theorem endpoint_17_44_p8 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 8 214705990216321291 = some 217361537248558776 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 6 2 214705990216321291 217361537248558776 217361537248558776 endpoint_17_44_p6 endpoint_17_44_w6
private theorem endpoint_17_44_w8 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 8 2 217361537248558776 = some 217361537248558776 := by decide +kernel
private theorem endpoint_17_44_p10 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 10 214705990216321291 = some 217361537248558776 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 8 2 214705990216321291 217361537248558776 217361537248558776 endpoint_17_44_p8 endpoint_17_44_w8
private theorem endpoint_17_44_w10 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 10 2 217361537248558776 = some 217361537248558776 := by decide +kernel
private theorem endpoint_17_44_p12 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 12 214705990216321291 = some 217361537248558776 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 10 2 214705990216321291 217361537248558776 217361537248558776 endpoint_17_44_p10 endpoint_17_44_w10
private theorem endpoint_17_44_w12 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 12 2 217361537248558776 = some 217361537248558776 := by decide +kernel
private theorem endpoint_17_44_p14 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 14 214705990216321291 = some 217361537248558776 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 12 2 214705990216321291 217361537248558776 217361537248558776 endpoint_17_44_p12 endpoint_17_44_w12
private theorem endpoint_17_44_w14 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 14 2 217361537248558776 = some 217361537248558776 := by decide +kernel
private theorem endpoint_17_44_p16 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 16 214705990216321291 = some 217361537248558776 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 14 2 214705990216321291 217361537248558776 217361537248558776 endpoint_17_44_p14 endpoint_17_44_w14
def endpoint_17_44 : CertifiedEndpoint :=
  ⟨⟨17, 44, 2572⟩, 217361537248558776, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_44_flag endpoint_17_44_sources 16 214705990216321291 217361537248558776 rfl endpoint_17_44_base endpoint_17_44_p16) (by decide)⟩
private def endpoint_17_45_flag : Flag := ⟨17, 45, 2531⟩
private def endpoint_17_45_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_45_base : receiptBase endpoint_17_45_flag endpoint_17_45_sources = some 215485566584128322 := by decide +kernel
private theorem endpoint_17_45_w0 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 2 215485566584128322 = some 221690807771462252 := by decide +kernel
private theorem endpoint_17_45_w2 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 2 2 221690807771462252 = some 221690807771462252 := by decide +kernel
private theorem endpoint_17_45_p4 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 4 215485566584128322 = some 221690807771462252 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 2 2 215485566584128322 221690807771462252 221690807771462252 endpoint_17_45_w0 endpoint_17_45_w2
private theorem endpoint_17_45_w4 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 4 2 221690807771462252 = some 221690807771462252 := by decide +kernel
private theorem endpoint_17_45_p6 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 6 215485566584128322 = some 221690807771462252 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 4 2 215485566584128322 221690807771462252 221690807771462252 endpoint_17_45_p4 endpoint_17_45_w4
private theorem endpoint_17_45_w6 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 6 2 221690807771462252 = some 221690807771462252 := by decide +kernel
private theorem endpoint_17_45_p8 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 8 215485566584128322 = some 221690807771462252 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 6 2 215485566584128322 221690807771462252 221690807771462252 endpoint_17_45_p6 endpoint_17_45_w6
private theorem endpoint_17_45_w8 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 8 2 221690807771462252 = some 221690807771462252 := by decide +kernel
private theorem endpoint_17_45_p10 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 10 215485566584128322 = some 221690807771462252 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 8 2 215485566584128322 221690807771462252 221690807771462252 endpoint_17_45_p8 endpoint_17_45_w8
private theorem endpoint_17_45_w10 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 10 2 221690807771462252 = some 221690807771462252 := by decide +kernel
private theorem endpoint_17_45_p12 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 12 215485566584128322 = some 221690807771462252 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 10 2 215485566584128322 221690807771462252 221690807771462252 endpoint_17_45_p10 endpoint_17_45_w10
private theorem endpoint_17_45_w12 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 12 2 221690807771462252 = some 221690807771462252 := by decide +kernel
private theorem endpoint_17_45_p14 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 14 215485566584128322 = some 221690807771462252 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 12 2 215485566584128322 221690807771462252 221690807771462252 endpoint_17_45_p12 endpoint_17_45_w12
private theorem endpoint_17_45_w14 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 14 2 221690807771462252 = some 221690807771462252 := by decide +kernel
private theorem endpoint_17_45_p16 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 16 215485566584128322 = some 221690807771462252 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 14 2 215485566584128322 221690807771462252 221690807771462252 endpoint_17_45_p14 endpoint_17_45_w14
def endpoint_17_45 : CertifiedEndpoint :=
  ⟨⟨17, 45, 2531⟩, 221690807771462252, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_45_flag endpoint_17_45_sources 16 215485566584128322 221690807771462252 rfl endpoint_17_45_base endpoint_17_45_p16) (by decide)⟩
private def endpoint_17_46_flag : Flag := ⟨17, 46, 2488⟩
private def endpoint_17_46_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_46_base : receiptBase endpoint_17_46_flag endpoint_17_46_sources = some 215960182313794588 := by decide +kernel
private theorem endpoint_17_46_w0 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 2 215960182313794588 = some 225812969733946528 := by decide +kernel
private theorem endpoint_17_46_w2 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 2 2 225812969733946528 = some 225812969733946528 := by decide +kernel
private theorem endpoint_17_46_p4 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 4 215960182313794588 = some 225812969733946528 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 2 2 215960182313794588 225812969733946528 225812969733946528 endpoint_17_46_w0 endpoint_17_46_w2
private theorem endpoint_17_46_w4 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 4 2 225812969733946528 = some 225812969733946528 := by decide +kernel
private theorem endpoint_17_46_p6 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 6 215960182313794588 = some 225812969733946528 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 4 2 215960182313794588 225812969733946528 225812969733946528 endpoint_17_46_p4 endpoint_17_46_w4
private theorem endpoint_17_46_w6 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 6 2 225812969733946528 = some 225812969733946528 := by decide +kernel
private theorem endpoint_17_46_p8 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 8 215960182313794588 = some 225812969733946528 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 6 2 215960182313794588 225812969733946528 225812969733946528 endpoint_17_46_p6 endpoint_17_46_w6
private theorem endpoint_17_46_w8 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 8 2 225812969733946528 = some 225812969733946528 := by decide +kernel
private theorem endpoint_17_46_p10 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 10 215960182313794588 = some 225812969733946528 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 8 2 215960182313794588 225812969733946528 225812969733946528 endpoint_17_46_p8 endpoint_17_46_w8
private theorem endpoint_17_46_w10 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 10 2 225812969733946528 = some 225812969733946528 := by decide +kernel
private theorem endpoint_17_46_p12 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 12 215960182313794588 = some 225812969733946528 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 10 2 215960182313794588 225812969733946528 225812969733946528 endpoint_17_46_p10 endpoint_17_46_w10
private theorem endpoint_17_46_w12 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 12 2 225812969733946528 = some 225812969733946528 := by decide +kernel
private theorem endpoint_17_46_p14 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 14 215960182313794588 = some 225812969733946528 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 12 2 215960182313794588 225812969733946528 225812969733946528 endpoint_17_46_p12 endpoint_17_46_w12
private theorem endpoint_17_46_w14 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 14 2 225812969733946528 = some 225812969733946528 := by decide +kernel
private theorem endpoint_17_46_p16 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 16 215960182313794588 = some 225812969733946528 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 14 2 215960182313794588 225812969733946528 225812969733946528 endpoint_17_46_p14 endpoint_17_46_w14
def endpoint_17_46 : CertifiedEndpoint :=
  ⟨⟨17, 46, 2488⟩, 225812969733946528, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_46_flag endpoint_17_46_sources 16 215960182313794588 225812969733946528 rfl endpoint_17_46_base endpoint_17_46_p16) (by decide)⟩
private def endpoint_17_47_flag : Flag := ⟨17, 47, 2445⟩
private def endpoint_17_47_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_47_base : receiptBase endpoint_17_47_flag endpoint_17_47_sources = some 216294357096274240 := by decide +kernel
private theorem endpoint_17_47_w0 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 2 216294357096274240 = some 229818099493092108 := by decide +kernel
private theorem endpoint_17_47_w2 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 2 2 229818099493092108 = some 229818099493092108 := by decide +kernel
private theorem endpoint_17_47_p4 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 4 216294357096274240 = some 229818099493092108 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 2 2 216294357096274240 229818099493092108 229818099493092108 endpoint_17_47_w0 endpoint_17_47_w2
private theorem endpoint_17_47_w4 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 4 2 229818099493092108 = some 229818099493092108 := by decide +kernel
private theorem endpoint_17_47_p6 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 6 216294357096274240 = some 229818099493092108 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 4 2 216294357096274240 229818099493092108 229818099493092108 endpoint_17_47_p4 endpoint_17_47_w4
private theorem endpoint_17_47_w6 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 6 2 229818099493092108 = some 229818099493092108 := by decide +kernel
private theorem endpoint_17_47_p8 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 8 216294357096274240 = some 229818099493092108 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 6 2 216294357096274240 229818099493092108 229818099493092108 endpoint_17_47_p6 endpoint_17_47_w6
private theorem endpoint_17_47_w8 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 8 2 229818099493092108 = some 229818099493092108 := by decide +kernel
private theorem endpoint_17_47_p10 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 10 216294357096274240 = some 229818099493092108 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 8 2 216294357096274240 229818099493092108 229818099493092108 endpoint_17_47_p8 endpoint_17_47_w8
private theorem endpoint_17_47_w10 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 10 2 229818099493092108 = some 229818099493092108 := by decide +kernel
private theorem endpoint_17_47_p12 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 12 216294357096274240 = some 229818099493092108 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 10 2 216294357096274240 229818099493092108 229818099493092108 endpoint_17_47_p10 endpoint_17_47_w10
private theorem endpoint_17_47_w12 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 12 2 229818099493092108 = some 229818099493092108 := by decide +kernel
private theorem endpoint_17_47_p14 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 14 216294357096274240 = some 229818099493092108 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 12 2 216294357096274240 229818099493092108 229818099493092108 endpoint_17_47_p12 endpoint_17_47_w12
private theorem endpoint_17_47_w14 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 14 2 229818099493092108 = some 229818099493092108 := by decide +kernel
private theorem endpoint_17_47_p16 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 16 216294357096274240 = some 229818099493092108 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 14 2 216294357096274240 229818099493092108 229818099493092108 endpoint_17_47_p14 endpoint_17_47_w14
def endpoint_17_47 : CertifiedEndpoint :=
  ⟨⟨17, 47, 2445⟩, 229818099493092108, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_47_flag endpoint_17_47_sources 16 216294357096274240 229818099493092108 rfl endpoint_17_47_base endpoint_17_47_p16) (by decide)⟩
private def endpoint_17_48_flag : Flag := ⟨17, 48, 2401⟩
private def endpoint_17_48_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_48_base : receiptBase endpoint_17_48_flag endpoint_17_48_sources = some 216399374031047139 := by decide +kernel
private theorem endpoint_17_48_w0 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 2 216399374031047139 = some 233655901698529224 := by decide +kernel
private theorem endpoint_17_48_w2 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 2 2 233655901698529224 = some 233655901698529224 := by decide +kernel
private theorem endpoint_17_48_p4 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 4 216399374031047139 = some 233655901698529224 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 2 2 216399374031047139 233655901698529224 233655901698529224 endpoint_17_48_w0 endpoint_17_48_w2
private theorem endpoint_17_48_w4 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 4 2 233655901698529224 = some 233655901698529224 := by decide +kernel
private theorem endpoint_17_48_p6 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 6 216399374031047139 = some 233655901698529224 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 4 2 216399374031047139 233655901698529224 233655901698529224 endpoint_17_48_p4 endpoint_17_48_w4
private theorem endpoint_17_48_w6 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 6 2 233655901698529224 = some 233655901698529224 := by decide +kernel
private theorem endpoint_17_48_p8 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 8 216399374031047139 = some 233655901698529224 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 6 2 216399374031047139 233655901698529224 233655901698529224 endpoint_17_48_p6 endpoint_17_48_w6
private theorem endpoint_17_48_w8 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 8 2 233655901698529224 = some 233655901698529224 := by decide +kernel
private theorem endpoint_17_48_p10 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 10 216399374031047139 = some 233655901698529224 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 8 2 216399374031047139 233655901698529224 233655901698529224 endpoint_17_48_p8 endpoint_17_48_w8
private theorem endpoint_17_48_w10 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 10 2 233655901698529224 = some 233655901698529224 := by decide +kernel
private theorem endpoint_17_48_p12 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 12 216399374031047139 = some 233655901698529224 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 10 2 216399374031047139 233655901698529224 233655901698529224 endpoint_17_48_p10 endpoint_17_48_w10
private theorem endpoint_17_48_w12 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 12 2 233655901698529224 = some 233655901698529224 := by decide +kernel
private theorem endpoint_17_48_p14 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 14 216399374031047139 = some 233655901698529224 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 12 2 216399374031047139 233655901698529224 233655901698529224 endpoint_17_48_p12 endpoint_17_48_w12
private theorem endpoint_17_48_w14 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 14 2 233655901698529224 = some 233655901698529224 := by decide +kernel
private theorem endpoint_17_48_p16 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 16 216399374031047139 = some 233655901698529224 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 14 2 216399374031047139 233655901698529224 233655901698529224 endpoint_17_48_p14 endpoint_17_48_w14
def endpoint_17_48 : CertifiedEndpoint :=
  ⟨⟨17, 48, 2401⟩, 233655901698529224, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_48_flag endpoint_17_48_sources 16 216399374031047139 233655901698529224 rfl endpoint_17_48_base endpoint_17_48_p16) (by decide)⟩
private def endpoint_17_49_flag : Flag := ⟨17, 49, 2356⟩
private def endpoint_17_49_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_17_49_base : receiptBase endpoint_17_49_flag endpoint_17_49_sources = some 221704018251161375 := by decide +kernel
private theorem endpoint_17_49_w0 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 2 221704018251161375 = some 229842732951299749 := by decide +kernel
private theorem endpoint_17_49_w2 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 2 2 229842732951299749 = some 229842732951299749 := by decide +kernel
private theorem endpoint_17_49_p4 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 4 221704018251161375 = some 229842732951299749 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 2 2 221704018251161375 229842732951299749 229842732951299749 endpoint_17_49_w0 endpoint_17_49_w2
private theorem endpoint_17_49_w4 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 4 2 229842732951299749 = some 229842732951299749 := by decide +kernel
private theorem endpoint_17_49_p6 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 6 221704018251161375 = some 229842732951299749 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 4 2 221704018251161375 229842732951299749 229842732951299749 endpoint_17_49_p4 endpoint_17_49_w4
private theorem endpoint_17_49_w6 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 6 2 229842732951299749 = some 229842732951299749 := by decide +kernel
private theorem endpoint_17_49_p8 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 8 221704018251161375 = some 229842732951299749 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 6 2 221704018251161375 229842732951299749 229842732951299749 endpoint_17_49_p6 endpoint_17_49_w6
private theorem endpoint_17_49_w8 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 8 2 229842732951299749 = some 229842732951299749 := by decide +kernel
private theorem endpoint_17_49_p10 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 10 221704018251161375 = some 229842732951299749 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 8 2 221704018251161375 229842732951299749 229842732951299749 endpoint_17_49_p8 endpoint_17_49_w8
private theorem endpoint_17_49_w10 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 10 2 229842732951299749 = some 229842732951299749 := by decide +kernel
private theorem endpoint_17_49_p12 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 12 221704018251161375 = some 229842732951299749 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 10 2 221704018251161375 229842732951299749 229842732951299749 endpoint_17_49_p10 endpoint_17_49_w10
private theorem endpoint_17_49_w12 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 12 2 229842732951299749 = some 229842732951299749 := by decide +kernel
private theorem endpoint_17_49_p14 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 14 221704018251161375 = some 229842732951299749 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 12 2 221704018251161375 229842732951299749 229842732951299749 endpoint_17_49_p12 endpoint_17_49_w12
private theorem endpoint_17_49_w14 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 14 2 229842732951299749 = some 229842732951299749 := by decide +kernel
private theorem endpoint_17_49_p16 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 16 221704018251161375 = some 229842732951299749 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 14 2 221704018251161375 229842732951299749 229842732951299749 endpoint_17_49_p14 endpoint_17_49_w14
def endpoint_17_49 : CertifiedEndpoint :=
  ⟨⟨17, 49, 2356⟩, 229842732951299749, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_17_49_flag endpoint_17_49_sources 16 221704018251161375 229842732951299749 rfl endpoint_17_49_base endpoint_17_49_p16) (by decide)⟩
private def endpoint_17_50_flag : Flag := ⟨17, 50, 2310⟩
private def endpoint_17_50_sources : Sources := ⟨contact11, contact11, contact29⟩
private theorem endpoint_17_50_base : receiptBase endpoint_17_50_flag endpoint_17_50_sources = some 221703334711306072 := by decide +kernel
private theorem endpoint_17_50_w0 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 2 221703334711306072 = some 228545094903418956 := by decide +kernel
private theorem endpoint_17_50_w2 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 2 2 228545094903418956 = some 228545094903418956 := by decide +kernel
private theorem endpoint_17_50_p4 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 4 221703334711306072 = some 228545094903418956 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 2 2 221703334711306072 228545094903418956 228545094903418956 endpoint_17_50_w0 endpoint_17_50_w2
private theorem endpoint_17_50_w4 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 4 2 228545094903418956 = some 228545094903418956 := by decide +kernel
private theorem endpoint_17_50_p6 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 6 221703334711306072 = some 228545094903418956 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 4 2 221703334711306072 228545094903418956 228545094903418956 endpoint_17_50_p4 endpoint_17_50_w4
private theorem endpoint_17_50_w6 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 6 2 228545094903418956 = some 228545094903418956 := by decide +kernel
private theorem endpoint_17_50_p8 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 8 221703334711306072 = some 228545094903418956 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 6 2 221703334711306072 228545094903418956 228545094903418956 endpoint_17_50_p6 endpoint_17_50_w6
private theorem endpoint_17_50_w8 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 8 2 228545094903418956 = some 228545094903418956 := by decide +kernel
private theorem endpoint_17_50_p10 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 10 221703334711306072 = some 228545094903418956 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 8 2 221703334711306072 228545094903418956 228545094903418956 endpoint_17_50_p8 endpoint_17_50_w8
private theorem endpoint_17_50_w10 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 10 2 228545094903418956 = some 228545094903418956 := by decide +kernel
private theorem endpoint_17_50_p12 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 12 221703334711306072 = some 228545094903418956 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 10 2 221703334711306072 228545094903418956 228545094903418956 endpoint_17_50_p10 endpoint_17_50_w10
private theorem endpoint_17_50_w12 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 12 2 228545094903418956 = some 228545094903418956 := by decide +kernel
private theorem endpoint_17_50_p14 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 14 221703334711306072 = some 228545094903418956 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 12 2 221703334711306072 228545094903418956 228545094903418956 endpoint_17_50_p12 endpoint_17_50_w12
private theorem endpoint_17_50_w14 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 14 2 228545094903418956 = some 228545094903418956 := by decide +kernel
private theorem endpoint_17_50_p16 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 16 221703334711306072 = some 228545094903418956 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 14 2 221703334711306072 228545094903418956 228545094903418956 endpoint_17_50_p14 endpoint_17_50_w14
def endpoint_17_50 : CertifiedEndpoint :=
  ⟨⟨17, 50, 2310⟩, 228545094903418956, .terminal ⟨contact11, contact11, contact29⟩ (finish_receipt_window endpoint_17_50_flag endpoint_17_50_sources 16 221703334711306072 228545094903418956 rfl endpoint_17_50_base endpoint_17_50_p16) (by decide)⟩
private def endpoint_17_51_flag : Flag := ⟨17, 51, 2264⟩
private def endpoint_17_51_sources : Sources := ⟨contact11, contact11, contact29⟩
private theorem endpoint_17_51_base : receiptBase endpoint_17_51_flag endpoint_17_51_sources = some 221207157460033175 := by decide +kernel
private theorem endpoint_17_51_w0 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 2 221207157460033175 = some 231610359206506787 := by decide +kernel
private theorem endpoint_17_51_w2 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 2 2 231610359206506787 = some 231610359206506787 := by decide +kernel
private theorem endpoint_17_51_p4 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 4 221207157460033175 = some 231610359206506787 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 2 2 221207157460033175 231610359206506787 231610359206506787 endpoint_17_51_w0 endpoint_17_51_w2
private theorem endpoint_17_51_w4 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 4 2 231610359206506787 = some 231610359206506787 := by decide +kernel
private theorem endpoint_17_51_p6 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 6 221207157460033175 = some 231610359206506787 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 4 2 221207157460033175 231610359206506787 231610359206506787 endpoint_17_51_p4 endpoint_17_51_w4
private theorem endpoint_17_51_w6 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 6 2 231610359206506787 = some 231610359206506787 := by decide +kernel
private theorem endpoint_17_51_p8 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 8 221207157460033175 = some 231610359206506787 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 6 2 221207157460033175 231610359206506787 231610359206506787 endpoint_17_51_p6 endpoint_17_51_w6
private theorem endpoint_17_51_w8 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 8 2 231610359206506787 = some 231610359206506787 := by decide +kernel
private theorem endpoint_17_51_p10 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 10 221207157460033175 = some 231610359206506787 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 8 2 221207157460033175 231610359206506787 231610359206506787 endpoint_17_51_p8 endpoint_17_51_w8
private theorem endpoint_17_51_w10 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 10 2 231610359206506787 = some 231610359206506787 := by decide +kernel
private theorem endpoint_17_51_p12 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 12 221207157460033175 = some 231610359206506787 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 10 2 221207157460033175 231610359206506787 231610359206506787 endpoint_17_51_p10 endpoint_17_51_w10
private theorem endpoint_17_51_w12 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 12 2 231610359206506787 = some 231610359206506787 := by decide +kernel
private theorem endpoint_17_51_p14 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 14 221207157460033175 = some 231610359206506787 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 12 2 221207157460033175 231610359206506787 231610359206506787 endpoint_17_51_p12 endpoint_17_51_w12
private theorem endpoint_17_51_w14 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 14 2 231610359206506787 = some 231610359206506787 := by decide +kernel
private theorem endpoint_17_51_p16 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 16 221207157460033175 = some 231610359206506787 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 14 2 221207157460033175 231610359206506787 231610359206506787 endpoint_17_51_p14 endpoint_17_51_w14
def endpoint_17_51 : CertifiedEndpoint :=
  ⟨⟨17, 51, 2264⟩, 231610359206506787, .terminal ⟨contact11, contact11, contact29⟩ (finish_receipt_window endpoint_17_51_flag endpoint_17_51_sources 16 221207157460033175 231610359206506787 rfl endpoint_17_51_base endpoint_17_51_p16) (by decide)⟩
private def endpoint_17_52_flag : Flag := ⟨17, 52, 2216⟩
private def endpoint_17_52_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_17_52_base : receiptBase endpoint_17_52_flag endpoint_17_52_sources = some 221089658607550926 := by decide +kernel
private theorem endpoint_17_52_w0 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 2 221089658607550926 = some 222717861207404828 := by decide +kernel
private theorem endpoint_17_52_w2 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 2 2 222717861207404828 = some 222717861207404828 := by decide +kernel
private theorem endpoint_17_52_p4 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 4 221089658607550926 = some 222717861207404828 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 2 2 221089658607550926 222717861207404828 222717861207404828 endpoint_17_52_w0 endpoint_17_52_w2
private theorem endpoint_17_52_w4 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 4 2 222717861207404828 = some 222717861207404828 := by decide +kernel
private theorem endpoint_17_52_p6 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 6 221089658607550926 = some 222717861207404828 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 4 2 221089658607550926 222717861207404828 222717861207404828 endpoint_17_52_p4 endpoint_17_52_w4
private theorem endpoint_17_52_w6 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 6 2 222717861207404828 = some 222717861207404828 := by decide +kernel
private theorem endpoint_17_52_p8 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 8 221089658607550926 = some 222717861207404828 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 6 2 221089658607550926 222717861207404828 222717861207404828 endpoint_17_52_p6 endpoint_17_52_w6
private theorem endpoint_17_52_w8 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 8 2 222717861207404828 = some 222717861207404828 := by decide +kernel
private theorem endpoint_17_52_p10 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 10 221089658607550926 = some 222717861207404828 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 8 2 221089658607550926 222717861207404828 222717861207404828 endpoint_17_52_p8 endpoint_17_52_w8
private theorem endpoint_17_52_w10 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 10 2 222717861207404828 = some 222717861207404828 := by decide +kernel
private theorem endpoint_17_52_p12 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 12 221089658607550926 = some 222717861207404828 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 10 2 221089658607550926 222717861207404828 222717861207404828 endpoint_17_52_p10 endpoint_17_52_w10
private theorem endpoint_17_52_w12 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 12 2 222717861207404828 = some 222717861207404828 := by decide +kernel
private theorem endpoint_17_52_p14 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 14 221089658607550926 = some 222717861207404828 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 12 2 221089658607550926 222717861207404828 222717861207404828 endpoint_17_52_p12 endpoint_17_52_w12
private theorem endpoint_17_52_w14 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 14 2 222717861207404828 = some 222717861207404828 := by decide +kernel
private theorem endpoint_17_52_p16 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 16 221089658607550926 = some 222717861207404828 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 14 2 221089658607550926 222717861207404828 222717861207404828 endpoint_17_52_p14 endpoint_17_52_w14
def endpoint_17_52 : CertifiedEndpoint :=
  ⟨⟨17, 52, 2216⟩, 222717861207404828, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_17_52_flag endpoint_17_52_sources 16 221089658607550926 222717861207404828 rfl endpoint_17_52_base endpoint_17_52_p16) (by decide)⟩
private def endpoint_17_53_flag : Flag := ⟨17, 53, 2167⟩
private def endpoint_17_53_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_17_53_base : receiptBase endpoint_17_53_flag endpoint_17_53_sources = some 219988322231391155 := by decide +kernel
private theorem endpoint_17_53_w0 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 2 219988322231391155 = some 225085811520176226 := by decide +kernel
private theorem endpoint_17_53_w2 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 2 2 225085811520176226 = some 225085811520176226 := by decide +kernel
private theorem endpoint_17_53_p4 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 4 219988322231391155 = some 225085811520176226 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 2 2 219988322231391155 225085811520176226 225085811520176226 endpoint_17_53_w0 endpoint_17_53_w2
private theorem endpoint_17_53_w4 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 4 2 225085811520176226 = some 225085811520176226 := by decide +kernel
private theorem endpoint_17_53_p6 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 6 219988322231391155 = some 225085811520176226 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 4 2 219988322231391155 225085811520176226 225085811520176226 endpoint_17_53_p4 endpoint_17_53_w4
private theorem endpoint_17_53_w6 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 6 2 225085811520176226 = some 225085811520176226 := by decide +kernel
private theorem endpoint_17_53_p8 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 8 219988322231391155 = some 225085811520176226 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 6 2 219988322231391155 225085811520176226 225085811520176226 endpoint_17_53_p6 endpoint_17_53_w6
private theorem endpoint_17_53_w8 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 8 2 225085811520176226 = some 225085811520176226 := by decide +kernel
private theorem endpoint_17_53_p10 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 10 219988322231391155 = some 225085811520176226 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 8 2 219988322231391155 225085811520176226 225085811520176226 endpoint_17_53_p8 endpoint_17_53_w8
private theorem endpoint_17_53_w10 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 10 2 225085811520176226 = some 225085811520176226 := by decide +kernel
private theorem endpoint_17_53_p12 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 12 219988322231391155 = some 225085811520176226 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 10 2 219988322231391155 225085811520176226 225085811520176226 endpoint_17_53_p10 endpoint_17_53_w10
private theorem endpoint_17_53_w12 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 12 2 225085811520176226 = some 225085811520176226 := by decide +kernel
private theorem endpoint_17_53_p14 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 14 219988322231391155 = some 225085811520176226 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 12 2 219988322231391155 225085811520176226 225085811520176226 endpoint_17_53_p12 endpoint_17_53_w12
private theorem endpoint_17_53_w14 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 14 2 225085811520176226 = some 225085811520176226 := by decide +kernel
private theorem endpoint_17_53_p16 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 16 219988322231391155 = some 225085811520176226 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 14 2 219988322231391155 225085811520176226 225085811520176226 endpoint_17_53_p14 endpoint_17_53_w14
def endpoint_17_53 : CertifiedEndpoint :=
  ⟨⟨17, 53, 2167⟩, 225085811520176226, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_17_53_flag endpoint_17_53_sources 16 219988322231391155 225085811520176226 rfl endpoint_17_53_base endpoint_17_53_p16) (by decide)⟩
private def endpoint_17_54_flag : Flag := ⟨17, 54, 2117⟩
private def endpoint_17_54_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_17_54_base : receiptBase endpoint_17_54_flag endpoint_17_54_sources = some 218657123273053237 := by decide +kernel
private theorem endpoint_17_54_w0 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 2 218657123273053237 = some 227262777006006338 := by decide +kernel
private theorem endpoint_17_54_w2 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 2 2 227262777006006338 = some 227262777006006338 := by decide +kernel
private theorem endpoint_17_54_p4 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 4 218657123273053237 = some 227262777006006338 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 2 2 218657123273053237 227262777006006338 227262777006006338 endpoint_17_54_w0 endpoint_17_54_w2
private theorem endpoint_17_54_w4 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 4 2 227262777006006338 = some 227262777006006338 := by decide +kernel
private theorem endpoint_17_54_p6 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 6 218657123273053237 = some 227262777006006338 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 4 2 218657123273053237 227262777006006338 227262777006006338 endpoint_17_54_p4 endpoint_17_54_w4
private theorem endpoint_17_54_w6 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 6 2 227262777006006338 = some 227262777006006338 := by decide +kernel
private theorem endpoint_17_54_p8 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 8 218657123273053237 = some 227262777006006338 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 6 2 218657123273053237 227262777006006338 227262777006006338 endpoint_17_54_p6 endpoint_17_54_w6
private theorem endpoint_17_54_w8 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 8 2 227262777006006338 = some 227262777006006338 := by decide +kernel
private theorem endpoint_17_54_p10 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 10 218657123273053237 = some 227262777006006338 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 8 2 218657123273053237 227262777006006338 227262777006006338 endpoint_17_54_p8 endpoint_17_54_w8
private theorem endpoint_17_54_w10 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 10 2 227262777006006338 = some 227262777006006338 := by decide +kernel
private theorem endpoint_17_54_p12 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 12 218657123273053237 = some 227262777006006338 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 10 2 218657123273053237 227262777006006338 227262777006006338 endpoint_17_54_p10 endpoint_17_54_w10
private theorem endpoint_17_54_w12 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 12 2 227262777006006338 = some 227262777006006338 := by decide +kernel
private theorem endpoint_17_54_p14 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 14 218657123273053237 = some 227262777006006338 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 12 2 218657123273053237 227262777006006338 227262777006006338 endpoint_17_54_p12 endpoint_17_54_w12
private theorem endpoint_17_54_w14 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 14 2 227262777006006338 = some 227262777006006338 := by decide +kernel
private theorem endpoint_17_54_p16 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 16 218657123273053237 = some 227262777006006338 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 14 2 218657123273053237 227262777006006338 227262777006006338 endpoint_17_54_p14 endpoint_17_54_w14
def endpoint_17_54 : CertifiedEndpoint :=
  ⟨⟨17, 54, 2117⟩, 227262777006006338, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_17_54_flag endpoint_17_54_sources 16 218657123273053237 227262777006006338 rfl endpoint_17_54_base endpoint_17_54_p16) (by decide)⟩
private def endpoint_17_55_flag : Flag := ⟨17, 55, 2065⟩
private def endpoint_17_55_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_17_55_base : receiptBase endpoint_17_55_flag endpoint_17_55_sources = some 216890847268254116 := by decide +kernel
private theorem endpoint_17_55_w0 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 2 216890847268254116 = some 229185319384951606 := by decide +kernel
private theorem endpoint_17_55_w2 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 2 2 229185319384951606 = some 229185319384951606 := by decide +kernel
private theorem endpoint_17_55_p4 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 4 216890847268254116 = some 229185319384951606 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 2 2 216890847268254116 229185319384951606 229185319384951606 endpoint_17_55_w0 endpoint_17_55_w2
private theorem endpoint_17_55_w4 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 4 2 229185319384951606 = some 229185319384951606 := by decide +kernel
private theorem endpoint_17_55_p6 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 6 216890847268254116 = some 229185319384951606 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 4 2 216890847268254116 229185319384951606 229185319384951606 endpoint_17_55_p4 endpoint_17_55_w4
private theorem endpoint_17_55_w6 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 6 2 229185319384951606 = some 229185319384951606 := by decide +kernel
private theorem endpoint_17_55_p8 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 8 216890847268254116 = some 229185319384951606 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 6 2 216890847268254116 229185319384951606 229185319384951606 endpoint_17_55_p6 endpoint_17_55_w6
private theorem endpoint_17_55_w8 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 8 2 229185319384951606 = some 229185319384951606 := by decide +kernel
private theorem endpoint_17_55_p10 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 10 216890847268254116 = some 229185319384951606 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 8 2 216890847268254116 229185319384951606 229185319384951606 endpoint_17_55_p8 endpoint_17_55_w8
private theorem endpoint_17_55_w10 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 10 2 229185319384951606 = some 229185319384951606 := by decide +kernel
private theorem endpoint_17_55_p12 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 12 216890847268254116 = some 229185319384951606 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 10 2 216890847268254116 229185319384951606 229185319384951606 endpoint_17_55_p10 endpoint_17_55_w10
private theorem endpoint_17_55_w12 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 12 2 229185319384951606 = some 229185319384951606 := by decide +kernel
private theorem endpoint_17_55_p14 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 14 216890847268254116 = some 229185319384951606 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 12 2 216890847268254116 229185319384951606 229185319384951606 endpoint_17_55_p12 endpoint_17_55_w12
private theorem endpoint_17_55_w14 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 14 2 229185319384951606 = some 229185319384951606 := by decide +kernel
private theorem endpoint_17_55_p16 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 16 216890847268254116 = some 229185319384951606 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 14 2 216890847268254116 229185319384951606 229185319384951606 endpoint_17_55_p14 endpoint_17_55_w14
def endpoint_17_55 : CertifiedEndpoint :=
  ⟨⟨17, 55, 2065⟩, 229185319384951606, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_17_55_flag endpoint_17_55_sources 16 216890847268254116 229185319384951606 rfl endpoint_17_55_base endpoint_17_55_p16) (by decide)⟩
private def endpoint_17_56_flag : Flag := ⟨17, 56, 2013⟩
private def endpoint_17_56_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_17_56_base : receiptBase endpoint_17_56_flag endpoint_17_56_sources = some 215917154539317009 := by decide +kernel
private theorem endpoint_17_56_w0 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 2 215917154539317009 = some 224683478442339456 := by decide +kernel
private theorem endpoint_17_56_w2 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 2 2 224683478442339456 = some 224683478442339456 := by decide +kernel
private theorem endpoint_17_56_p4 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 4 215917154539317009 = some 224683478442339456 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 2 2 215917154539317009 224683478442339456 224683478442339456 endpoint_17_56_w0 endpoint_17_56_w2
private theorem endpoint_17_56_w4 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 4 2 224683478442339456 = some 224683478442339456 := by decide +kernel
private theorem endpoint_17_56_p6 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 6 215917154539317009 = some 224683478442339456 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 4 2 215917154539317009 224683478442339456 224683478442339456 endpoint_17_56_p4 endpoint_17_56_w4
private theorem endpoint_17_56_w6 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 6 2 224683478442339456 = some 224683478442339456 := by decide +kernel
private theorem endpoint_17_56_p8 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 8 215917154539317009 = some 224683478442339456 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 6 2 215917154539317009 224683478442339456 224683478442339456 endpoint_17_56_p6 endpoint_17_56_w6
private theorem endpoint_17_56_w8 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 8 2 224683478442339456 = some 224683478442339456 := by decide +kernel
private theorem endpoint_17_56_p10 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 10 215917154539317009 = some 224683478442339456 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 8 2 215917154539317009 224683478442339456 224683478442339456 endpoint_17_56_p8 endpoint_17_56_w8
private theorem endpoint_17_56_w10 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 10 2 224683478442339456 = some 224683478442339456 := by decide +kernel
private theorem endpoint_17_56_p12 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 12 215917154539317009 = some 224683478442339456 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 10 2 215917154539317009 224683478442339456 224683478442339456 endpoint_17_56_p10 endpoint_17_56_w10
private theorem endpoint_17_56_w12 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 12 2 224683478442339456 = some 224683478442339456 := by decide +kernel
private theorem endpoint_17_56_p14 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 14 215917154539317009 = some 224683478442339456 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 12 2 215917154539317009 224683478442339456 224683478442339456 endpoint_17_56_p12 endpoint_17_56_w12
private theorem endpoint_17_56_w14 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 14 2 224683478442339456 = some 224683478442339456 := by decide +kernel
private theorem endpoint_17_56_p16 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 16 215917154539317009 = some 224683478442339456 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 14 2 215917154539317009 224683478442339456 224683478442339456 endpoint_17_56_p14 endpoint_17_56_w14
def endpoint_17_56 : CertifiedEndpoint :=
  ⟨⟨17, 56, 2013⟩, 224683478442339456, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_17_56_flag endpoint_17_56_sources 16 215917154539317009 224683478442339456 rfl endpoint_17_56_base endpoint_17_56_p16) (by decide)⟩
private def endpoint_17_57_flag : Flag := ⟨17, 57, 1959⟩
private def endpoint_17_57_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_17_57_base : receiptBase endpoint_17_57_flag endpoint_17_57_sources = some 213571208702496071 := by decide +kernel
private theorem endpoint_17_57_w0 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 2 213571208702496071 = some 226065958091833180 := by decide +kernel
private theorem endpoint_17_57_w2 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 2 2 226065958091833180 = some 226065958091833180 := by decide +kernel
private theorem endpoint_17_57_p4 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 4 213571208702496071 = some 226065958091833180 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 2 2 213571208702496071 226065958091833180 226065958091833180 endpoint_17_57_w0 endpoint_17_57_w2
private theorem endpoint_17_57_w4 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 4 2 226065958091833180 = some 226065958091833180 := by decide +kernel
private theorem endpoint_17_57_p6 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 6 213571208702496071 = some 226065958091833180 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 4 2 213571208702496071 226065958091833180 226065958091833180 endpoint_17_57_p4 endpoint_17_57_w4
private theorem endpoint_17_57_w6 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 6 2 226065958091833180 = some 226065958091833180 := by decide +kernel
private theorem endpoint_17_57_p8 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 8 213571208702496071 = some 226065958091833180 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 6 2 213571208702496071 226065958091833180 226065958091833180 endpoint_17_57_p6 endpoint_17_57_w6
private theorem endpoint_17_57_w8 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 8 2 226065958091833180 = some 226065958091833180 := by decide +kernel
private theorem endpoint_17_57_p10 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 10 213571208702496071 = some 226065958091833180 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 8 2 213571208702496071 226065958091833180 226065958091833180 endpoint_17_57_p8 endpoint_17_57_w8
private theorem endpoint_17_57_w10 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 10 2 226065958091833180 = some 226065958091833180 := by decide +kernel
private theorem endpoint_17_57_p12 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 12 213571208702496071 = some 226065958091833180 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 10 2 213571208702496071 226065958091833180 226065958091833180 endpoint_17_57_p10 endpoint_17_57_w10
private theorem endpoint_17_57_w12 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 12 2 226065958091833180 = some 226065958091833180 := by decide +kernel
private theorem endpoint_17_57_p14 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 14 213571208702496071 = some 226065958091833180 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 12 2 213571208702496071 226065958091833180 226065958091833180 endpoint_17_57_p12 endpoint_17_57_w12
private theorem endpoint_17_57_w14 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 14 2 226065958091833180 = some 226065958091833180 := by decide +kernel
private theorem endpoint_17_57_p16 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 16 213571208702496071 = some 226065958091833180 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 14 2 213571208702496071 226065958091833180 226065958091833180 endpoint_17_57_p14 endpoint_17_57_w14
def endpoint_17_57 : CertifiedEndpoint :=
  ⟨⟨17, 57, 1959⟩, 226065958091833180, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_17_57_flag endpoint_17_57_sources 16 213571208702496071 226065958091833180 rfl endpoint_17_57_base endpoint_17_57_p16) (by decide)⟩
private def endpoint_17_58_flag : Flag := ⟨17, 58, 1905⟩
private def endpoint_17_58_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_17_58_base : receiptBase endpoint_17_58_flag endpoint_17_58_sources = some 211044785472159863 := by decide +kernel
private theorem endpoint_17_58_w0 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 2 211044785472159863 = some 227302491092925870 := by decide +kernel
private theorem endpoint_17_58_w2 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 2 2 227302491092925870 = some 227302491092925870 := by decide +kernel
private theorem endpoint_17_58_p4 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 4 211044785472159863 = some 227302491092925870 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 2 2 211044785472159863 227302491092925870 227302491092925870 endpoint_17_58_w0 endpoint_17_58_w2
private theorem endpoint_17_58_w4 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 4 2 227302491092925870 = some 227302491092925870 := by decide +kernel
private theorem endpoint_17_58_p6 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 6 211044785472159863 = some 227302491092925870 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 4 2 211044785472159863 227302491092925870 227302491092925870 endpoint_17_58_p4 endpoint_17_58_w4
private theorem endpoint_17_58_w6 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 6 2 227302491092925870 = some 227302491092925870 := by decide +kernel
private theorem endpoint_17_58_p8 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 8 211044785472159863 = some 227302491092925870 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 6 2 211044785472159863 227302491092925870 227302491092925870 endpoint_17_58_p6 endpoint_17_58_w6
private theorem endpoint_17_58_w8 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 8 2 227302491092925870 = some 227302491092925870 := by decide +kernel
private theorem endpoint_17_58_p10 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 10 211044785472159863 = some 227302491092925870 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 8 2 211044785472159863 227302491092925870 227302491092925870 endpoint_17_58_p8 endpoint_17_58_w8
private theorem endpoint_17_58_w10 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 10 2 227302491092925870 = some 227302491092925870 := by decide +kernel
private theorem endpoint_17_58_p12 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 12 211044785472159863 = some 227302491092925870 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 10 2 211044785472159863 227302491092925870 227302491092925870 endpoint_17_58_p10 endpoint_17_58_w10
private theorem endpoint_17_58_w12 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 12 2 227302491092925870 = some 227302491092925870 := by decide +kernel
private theorem endpoint_17_58_p14 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 14 211044785472159863 = some 227302491092925870 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 12 2 211044785472159863 227302491092925870 227302491092925870 endpoint_17_58_p12 endpoint_17_58_w12
private theorem endpoint_17_58_w14 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 14 2 227302491092925870 = some 227302491092925870 := by decide +kernel
private theorem endpoint_17_58_p16 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 16 211044785472159863 = some 227302491092925870 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 14 2 211044785472159863 227302491092925870 227302491092925870 endpoint_17_58_p14 endpoint_17_58_w14
def endpoint_17_58 : CertifiedEndpoint :=
  ⟨⟨17, 58, 1905⟩, 227302491092925870, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_17_58_flag endpoint_17_58_sources 16 211044785472159863 227302491092925870 rfl endpoint_17_58_base endpoint_17_58_p16) (by decide)⟩
private def endpoint_17_59_flag : Flag := ⟨17, 59, 1848⟩
private def endpoint_17_59_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_59_base : receiptBase endpoint_17_59_flag endpoint_17_59_sources = some 210491305662531765 := by decide +kernel
private theorem endpoint_17_59_w0 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 2 210491305662531765 = some 212150016722128275 := by decide +kernel
private theorem endpoint_17_59_w2 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 2 2 212150016722128275 = some 212150016722128275 := by decide +kernel
private theorem endpoint_17_59_p4 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 4 210491305662531765 = some 212150016722128275 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 2 2 210491305662531765 212150016722128275 212150016722128275 endpoint_17_59_w0 endpoint_17_59_w2
private theorem endpoint_17_59_w4 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 4 2 212150016722128275 = some 212150016722128275 := by decide +kernel
private theorem endpoint_17_59_p6 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 6 210491305662531765 = some 212150016722128275 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 4 2 210491305662531765 212150016722128275 212150016722128275 endpoint_17_59_p4 endpoint_17_59_w4
private theorem endpoint_17_59_w6 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 6 2 212150016722128275 = some 212150016722128275 := by decide +kernel
private theorem endpoint_17_59_p8 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 8 210491305662531765 = some 212150016722128275 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 6 2 210491305662531765 212150016722128275 212150016722128275 endpoint_17_59_p6 endpoint_17_59_w6
private theorem endpoint_17_59_w8 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 8 2 212150016722128275 = some 212150016722128275 := by decide +kernel
private theorem endpoint_17_59_p10 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 10 210491305662531765 = some 212150016722128275 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 8 2 210491305662531765 212150016722128275 212150016722128275 endpoint_17_59_p8 endpoint_17_59_w8
private theorem endpoint_17_59_w10 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 10 2 212150016722128275 = some 212150016722128275 := by decide +kernel
private theorem endpoint_17_59_p12 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 12 210491305662531765 = some 212150016722128275 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 10 2 210491305662531765 212150016722128275 212150016722128275 endpoint_17_59_p10 endpoint_17_59_w10
private theorem endpoint_17_59_w12 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 12 2 212150016722128275 = some 212150016722128275 := by decide +kernel
private theorem endpoint_17_59_p14 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 14 210491305662531765 = some 212150016722128275 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 12 2 210491305662531765 212150016722128275 212150016722128275 endpoint_17_59_p12 endpoint_17_59_w12
private theorem endpoint_17_59_w14 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 14 2 212150016722128275 = some 212150016722128275 := by decide +kernel
private theorem endpoint_17_59_p16 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 16 210491305662531765 = some 212150016722128275 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 14 2 210491305662531765 212150016722128275 212150016722128275 endpoint_17_59_p14 endpoint_17_59_w14
def endpoint_17_59 : CertifiedEndpoint :=
  ⟨⟨17, 59, 1848⟩, 212150016722128275, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_59_flag endpoint_17_59_sources 16 210491305662531765 212150016722128275 rfl endpoint_17_59_base endpoint_17_59_p16) (by decide)⟩
private def endpoint_17_60_flag : Flag := ⟨17, 60, 1791⟩
private def endpoint_17_60_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_60_base : receiptBase endpoint_17_60_flag endpoint_17_60_sources = some 207112627985165346 := by decide +kernel
private theorem endpoint_17_60_w0 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 2 207112627985165346 = some 212569867024365052 := by decide +kernel
private theorem endpoint_17_60_w2 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 2 2 212569867024365052 = some 212569867024365052 := by decide +kernel
private theorem endpoint_17_60_p4 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 4 207112627985165346 = some 212569867024365052 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 2 2 207112627985165346 212569867024365052 212569867024365052 endpoint_17_60_w0 endpoint_17_60_w2
private theorem endpoint_17_60_w4 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 4 2 212569867024365052 = some 212569867024365052 := by decide +kernel
private theorem endpoint_17_60_p6 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 6 207112627985165346 = some 212569867024365052 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 4 2 207112627985165346 212569867024365052 212569867024365052 endpoint_17_60_p4 endpoint_17_60_w4
private theorem endpoint_17_60_w6 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 6 2 212569867024365052 = some 212569867024365052 := by decide +kernel
private theorem endpoint_17_60_p8 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 8 207112627985165346 = some 212569867024365052 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 6 2 207112627985165346 212569867024365052 212569867024365052 endpoint_17_60_p6 endpoint_17_60_w6
private theorem endpoint_17_60_w8 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 8 2 212569867024365052 = some 212569867024365052 := by decide +kernel
private theorem endpoint_17_60_p10 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 10 207112627985165346 = some 212569867024365052 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 8 2 207112627985165346 212569867024365052 212569867024365052 endpoint_17_60_p8 endpoint_17_60_w8
private theorem endpoint_17_60_w10 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 10 2 212569867024365052 = some 212569867024365052 := by decide +kernel
private theorem endpoint_17_60_p12 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 12 207112627985165346 = some 212569867024365052 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 10 2 207112627985165346 212569867024365052 212569867024365052 endpoint_17_60_p10 endpoint_17_60_w10
private theorem endpoint_17_60_w12 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 12 2 212569867024365052 = some 212569867024365052 := by decide +kernel
private theorem endpoint_17_60_p14 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 14 207112627985165346 = some 212569867024365052 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 12 2 207112627985165346 212569867024365052 212569867024365052 endpoint_17_60_p12 endpoint_17_60_w12
private theorem endpoint_17_60_w14 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 14 2 212569867024365052 = some 212569867024365052 := by decide +kernel
private theorem endpoint_17_60_p16 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 16 207112627985165346 = some 212569867024365052 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 14 2 207112627985165346 212569867024365052 212569867024365052 endpoint_17_60_p14 endpoint_17_60_w14
def endpoint_17_60 : CertifiedEndpoint :=
  ⟨⟨17, 60, 1791⟩, 212569867024365052, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_60_flag endpoint_17_60_sources 16 207112627985165346 212569867024365052 rfl endpoint_17_60_base endpoint_17_60_p16) (by decide)⟩
private def endpoint_17_61_flag : Flag := ⟨17, 61, 1732⟩
private def endpoint_17_61_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_61_base : receiptBase endpoint_17_61_flag endpoint_17_61_sources = some 203308073807450381 := by decide +kernel
private theorem endpoint_17_61_w0 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 2 203308073807450381 = some 212701122602825131 := by decide +kernel
private theorem endpoint_17_61_w2 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 2 2 212701122602825131 = some 212701122602825131 := by decide +kernel
private theorem endpoint_17_61_p4 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 4 203308073807450381 = some 212701122602825131 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 2 2 203308073807450381 212701122602825131 212701122602825131 endpoint_17_61_w0 endpoint_17_61_w2
private theorem endpoint_17_61_w4 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 4 2 212701122602825131 = some 212701122602825131 := by decide +kernel
private theorem endpoint_17_61_p6 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 6 203308073807450381 = some 212701122602825131 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 4 2 203308073807450381 212701122602825131 212701122602825131 endpoint_17_61_p4 endpoint_17_61_w4
private theorem endpoint_17_61_w6 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 6 2 212701122602825131 = some 212701122602825131 := by decide +kernel
private theorem endpoint_17_61_p8 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 8 203308073807450381 = some 212701122602825131 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 6 2 203308073807450381 212701122602825131 212701122602825131 endpoint_17_61_p6 endpoint_17_61_w6
private theorem endpoint_17_61_w8 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 8 2 212701122602825131 = some 212701122602825131 := by decide +kernel
private theorem endpoint_17_61_p10 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 10 203308073807450381 = some 212701122602825131 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 8 2 203308073807450381 212701122602825131 212701122602825131 endpoint_17_61_p8 endpoint_17_61_w8
private theorem endpoint_17_61_w10 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 10 2 212701122602825131 = some 212701122602825131 := by decide +kernel
private theorem endpoint_17_61_p12 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 12 203308073807450381 = some 212701122602825131 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 10 2 203308073807450381 212701122602825131 212701122602825131 endpoint_17_61_p10 endpoint_17_61_w10
private theorem endpoint_17_61_w12 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 12 2 212701122602825131 = some 212701122602825131 := by decide +kernel
private theorem endpoint_17_61_p14 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 14 203308073807450381 = some 212701122602825131 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 12 2 203308073807450381 212701122602825131 212701122602825131 endpoint_17_61_p12 endpoint_17_61_w12
private theorem endpoint_17_61_w14 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 14 2 212701122602825131 = some 212701122602825131 := by decide +kernel
private theorem endpoint_17_61_p16 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 16 203308073807450381 = some 212701122602825131 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 14 2 203308073807450381 212701122602825131 212701122602825131 endpoint_17_61_p14 endpoint_17_61_w14
def endpoint_17_61 : CertifiedEndpoint :=
  ⟨⟨17, 61, 1732⟩, 212701122602825131, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_61_flag endpoint_17_61_sources 16 203308073807450381 212701122602825131 rfl endpoint_17_61_base endpoint_17_61_p16) (by decide)⟩
private def endpoint_17_62_flag : Flag := ⟨17, 62, 1672⟩
private def endpoint_17_62_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_62_base : receiptBase endpoint_17_62_flag endpoint_17_62_sources = some 199185126626017309 := by decide +kernel
private theorem endpoint_17_62_w0 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 2 199185126626017309 = some 212604593151537312 := by decide +kernel
private theorem endpoint_17_62_w2 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 2 2 212604593151537312 = some 212604593151537312 := by decide +kernel
private theorem endpoint_17_62_p4 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 4 199185126626017309 = some 212604593151537312 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 2 2 199185126626017309 212604593151537312 212604593151537312 endpoint_17_62_w0 endpoint_17_62_w2
private theorem endpoint_17_62_w4 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 4 2 212604593151537312 = some 212604593151537312 := by decide +kernel
private theorem endpoint_17_62_p6 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 6 199185126626017309 = some 212604593151537312 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 4 2 199185126626017309 212604593151537312 212604593151537312 endpoint_17_62_p4 endpoint_17_62_w4
private theorem endpoint_17_62_w6 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 6 2 212604593151537312 = some 212604593151537312 := by decide +kernel
private theorem endpoint_17_62_p8 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 8 199185126626017309 = some 212604593151537312 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 6 2 199185126626017309 212604593151537312 212604593151537312 endpoint_17_62_p6 endpoint_17_62_w6
private theorem endpoint_17_62_w8 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 8 2 212604593151537312 = some 212604593151537312 := by decide +kernel
private theorem endpoint_17_62_p10 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 10 199185126626017309 = some 212604593151537312 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 8 2 199185126626017309 212604593151537312 212604593151537312 endpoint_17_62_p8 endpoint_17_62_w8
private theorem endpoint_17_62_w10 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 10 2 212604593151537312 = some 212604593151537312 := by decide +kernel
private theorem endpoint_17_62_p12 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 12 199185126626017309 = some 212604593151537312 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 10 2 199185126626017309 212604593151537312 212604593151537312 endpoint_17_62_p10 endpoint_17_62_w10
private theorem endpoint_17_62_w12 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 12 2 212604593151537312 = some 212604593151537312 := by decide +kernel
private theorem endpoint_17_62_p14 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 14 199185126626017309 = some 212604593151537312 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 12 2 199185126626017309 212604593151537312 212604593151537312 endpoint_17_62_p12 endpoint_17_62_w12
private theorem endpoint_17_62_w14 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 14 2 212604593151537312 = some 212604593151537312 := by decide +kernel
private theorem endpoint_17_62_p16 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 16 199185126626017309 = some 212604593151537312 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 14 2 199185126626017309 212604593151537312 212604593151537312 endpoint_17_62_p14 endpoint_17_62_w14
def endpoint_17_62 : CertifiedEndpoint :=
  ⟨⟨17, 62, 1672⟩, 212604593151537312, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_62_flag endpoint_17_62_sources 16 199185126626017309 212604593151537312 rfl endpoint_17_62_base endpoint_17_62_p16) (by decide)⟩
private def endpoint_17_63_flag : Flag := ⟨17, 63, 1610⟩
private def endpoint_17_63_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_63_base : receiptBase endpoint_17_63_flag endpoint_17_63_sources = some 196215279493444557 := by decide +kernel
private theorem endpoint_17_63_w0 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 2 196215279493444557 = some 196889867788860431 := by decide +kernel
private theorem endpoint_17_63_w2 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 2 2 196889867788860431 = some 196889867788860431 := by decide +kernel
private theorem endpoint_17_63_p4 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 4 196215279493444557 = some 196889867788860431 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 2 2 196215279493444557 196889867788860431 196889867788860431 endpoint_17_63_w0 endpoint_17_63_w2
private theorem endpoint_17_63_w4 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 4 2 196889867788860431 = some 196889867788860431 := by decide +kernel
private theorem endpoint_17_63_p6 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 6 196215279493444557 = some 196889867788860431 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 4 2 196215279493444557 196889867788860431 196889867788860431 endpoint_17_63_p4 endpoint_17_63_w4
private theorem endpoint_17_63_w6 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 6 2 196889867788860431 = some 196889867788860431 := by decide +kernel
private theorem endpoint_17_63_p8 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 8 196215279493444557 = some 196889867788860431 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 6 2 196215279493444557 196889867788860431 196889867788860431 endpoint_17_63_p6 endpoint_17_63_w6
private theorem endpoint_17_63_w8 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 8 2 196889867788860431 = some 196889867788860431 := by decide +kernel
private theorem endpoint_17_63_p10 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 10 196215279493444557 = some 196889867788860431 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 8 2 196215279493444557 196889867788860431 196889867788860431 endpoint_17_63_p8 endpoint_17_63_w8
private theorem endpoint_17_63_w10 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 10 2 196889867788860431 = some 196889867788860431 := by decide +kernel
private theorem endpoint_17_63_p12 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 12 196215279493444557 = some 196889867788860431 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 10 2 196215279493444557 196889867788860431 196889867788860431 endpoint_17_63_p10 endpoint_17_63_w10
private theorem endpoint_17_63_w12 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 12 2 196889867788860431 = some 196889867788860431 := by decide +kernel
private theorem endpoint_17_63_p14 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 14 196215279493444557 = some 196889867788860431 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 12 2 196215279493444557 196889867788860431 196889867788860431 endpoint_17_63_p12 endpoint_17_63_w12
private theorem endpoint_17_63_w14 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 14 2 196889867788860431 = some 196889867788860431 := by decide +kernel
private theorem endpoint_17_63_p16 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 16 196215279493444557 = some 196889867788860431 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 14 2 196215279493444557 196889867788860431 196889867788860431 endpoint_17_63_p14 endpoint_17_63_w14
def endpoint_17_63 : CertifiedEndpoint :=
  ⟨⟨17, 63, 1610⟩, 196889867788860431, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_63_flag endpoint_17_63_sources 16 196215279493444557 196889867788860431 rfl endpoint_17_63_base endpoint_17_63_p16) (by decide)⟩
private def endpoint_17_64_flag : Flag := ⟨17, 64, 1546⟩
private def endpoint_17_64_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_64_base : receiptBase endpoint_17_64_flag endpoint_17_64_sources = some 191141321720650594 := by decide +kernel
private theorem endpoint_17_64_w0 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 2 191141321720650594 = some 195896973372174724 := by decide +kernel
private theorem endpoint_17_64_w2 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 2 2 195896973372174724 = some 195896973372174724 := by decide +kernel
private theorem endpoint_17_64_p4 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 4 191141321720650594 = some 195896973372174724 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 2 2 191141321720650594 195896973372174724 195896973372174724 endpoint_17_64_w0 endpoint_17_64_w2
private theorem endpoint_17_64_w4 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 4 2 195896973372174724 = some 195896973372174724 := by decide +kernel
private theorem endpoint_17_64_p6 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 6 191141321720650594 = some 195896973372174724 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 4 2 191141321720650594 195896973372174724 195896973372174724 endpoint_17_64_p4 endpoint_17_64_w4
private theorem endpoint_17_64_w6 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 6 2 195896973372174724 = some 195896973372174724 := by decide +kernel
private theorem endpoint_17_64_p8 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 8 191141321720650594 = some 195896973372174724 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 6 2 191141321720650594 195896973372174724 195896973372174724 endpoint_17_64_p6 endpoint_17_64_w6
private theorem endpoint_17_64_w8 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 8 2 195896973372174724 = some 195896973372174724 := by decide +kernel
private theorem endpoint_17_64_p10 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 10 191141321720650594 = some 195896973372174724 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 8 2 191141321720650594 195896973372174724 195896973372174724 endpoint_17_64_p8 endpoint_17_64_w8
private theorem endpoint_17_64_w10 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 10 2 195896973372174724 = some 195896973372174724 := by decide +kernel
private theorem endpoint_17_64_p12 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 12 191141321720650594 = some 195896973372174724 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 10 2 191141321720650594 195896973372174724 195896973372174724 endpoint_17_64_p10 endpoint_17_64_w10
private theorem endpoint_17_64_w12 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 12 2 195896973372174724 = some 195896973372174724 := by decide +kernel
private theorem endpoint_17_64_p14 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 14 191141321720650594 = some 195896973372174724 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 12 2 191141321720650594 195896973372174724 195896973372174724 endpoint_17_64_p12 endpoint_17_64_w12
private theorem endpoint_17_64_w14 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 14 2 195896973372174724 = some 195896973372174724 := by decide +kernel
private theorem endpoint_17_64_p16 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 16 191141321720650594 = some 195896973372174724 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 14 2 191141321720650594 195896973372174724 195896973372174724 endpoint_17_64_p14 endpoint_17_64_w14
def endpoint_17_64 : CertifiedEndpoint :=
  ⟨⟨17, 64, 1546⟩, 195896973372174724, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_64_flag endpoint_17_64_sources 16 191141321720650594 195896973372174724 rfl endpoint_17_64_base endpoint_17_64_p16) (by decide)⟩
private def endpoint_17_65_flag : Flag := ⟨17, 65, 1481⟩
private def endpoint_17_65_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_65_base : receiptBase endpoint_17_65_flag endpoint_17_65_sources = some 185724964396175798 := by decide +kernel
private theorem endpoint_17_65_w0 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 2 185724964396175798 = some 194659208117295192 := by decide +kernel
private theorem endpoint_17_65_w2 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 2 2 194659208117295192 = some 194659208117295192 := by decide +kernel
private theorem endpoint_17_65_p4 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 4 185724964396175798 = some 194659208117295192 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 2 2 185724964396175798 194659208117295192 194659208117295192 endpoint_17_65_w0 endpoint_17_65_w2
private theorem endpoint_17_65_w4 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 4 2 194659208117295192 = some 194659208117295192 := by decide +kernel
private theorem endpoint_17_65_p6 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 6 185724964396175798 = some 194659208117295192 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 4 2 185724964396175798 194659208117295192 194659208117295192 endpoint_17_65_p4 endpoint_17_65_w4
private theorem endpoint_17_65_w6 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 6 2 194659208117295192 = some 194659208117295192 := by decide +kernel
private theorem endpoint_17_65_p8 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 8 185724964396175798 = some 194659208117295192 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 6 2 185724964396175798 194659208117295192 194659208117295192 endpoint_17_65_p6 endpoint_17_65_w6
private theorem endpoint_17_65_w8 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 8 2 194659208117295192 = some 194659208117295192 := by decide +kernel
private theorem endpoint_17_65_p10 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 10 185724964396175798 = some 194659208117295192 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 8 2 185724964396175798 194659208117295192 194659208117295192 endpoint_17_65_p8 endpoint_17_65_w8
private theorem endpoint_17_65_w10 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 10 2 194659208117295192 = some 194659208117295192 := by decide +kernel
private theorem endpoint_17_65_p12 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 12 185724964396175798 = some 194659208117295192 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 10 2 185724964396175798 194659208117295192 194659208117295192 endpoint_17_65_p10 endpoint_17_65_w10
private theorem endpoint_17_65_w12 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 12 2 194659208117295192 = some 194659208117295192 := by decide +kernel
private theorem endpoint_17_65_p14 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 14 185724964396175798 = some 194659208117295192 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 12 2 185724964396175798 194659208117295192 194659208117295192 endpoint_17_65_p12 endpoint_17_65_w12
private theorem endpoint_17_65_w14 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 14 2 194659208117295192 = some 194659208117295192 := by decide +kernel
private theorem endpoint_17_65_p16 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 16 185724964396175798 = some 194659208117295192 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 14 2 185724964396175798 194659208117295192 194659208117295192 endpoint_17_65_p14 endpoint_17_65_w14
def endpoint_17_65 : CertifiedEndpoint :=
  ⟨⟨17, 65, 1481⟩, 194659208117295192, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_65_flag endpoint_17_65_sources 16 185724964396175798 194659208117295192 rfl endpoint_17_65_base endpoint_17_65_p16) (by decide)⟩
private def endpoint_17_66_flag : Flag := ⟨17, 66, 1414⟩
private def endpoint_17_66_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_66_base : receiptBase endpoint_17_66_flag endpoint_17_66_sources = some 179835709733269868 := by decide +kernel
private theorem endpoint_17_66_w0 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 2 179835709733269868 = some 193098676521747108 := by decide +kernel
private theorem endpoint_17_66_w2 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 2 2 193098676521747108 = some 193098676521747108 := by decide +kernel
private theorem endpoint_17_66_p4 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 4 179835709733269868 = some 193098676521747108 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 2 2 179835709733269868 193098676521747108 193098676521747108 endpoint_17_66_w0 endpoint_17_66_w2
private theorem endpoint_17_66_w4 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 4 2 193098676521747108 = some 193098676521747108 := by decide +kernel
private theorem endpoint_17_66_p6 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 6 179835709733269868 = some 193098676521747108 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 4 2 179835709733269868 193098676521747108 193098676521747108 endpoint_17_66_p4 endpoint_17_66_w4
private theorem endpoint_17_66_w6 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 6 2 193098676521747108 = some 193098676521747108 := by decide +kernel
private theorem endpoint_17_66_p8 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 8 179835709733269868 = some 193098676521747108 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 6 2 179835709733269868 193098676521747108 193098676521747108 endpoint_17_66_p6 endpoint_17_66_w6
private theorem endpoint_17_66_w8 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 8 2 193098676521747108 = some 193098676521747108 := by decide +kernel
private theorem endpoint_17_66_p10 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 10 179835709733269868 = some 193098676521747108 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 8 2 179835709733269868 193098676521747108 193098676521747108 endpoint_17_66_p8 endpoint_17_66_w8
private theorem endpoint_17_66_w10 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 10 2 193098676521747108 = some 193098676521747108 := by decide +kernel
private theorem endpoint_17_66_p12 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 12 179835709733269868 = some 193098676521747108 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 10 2 179835709733269868 193098676521747108 193098676521747108 endpoint_17_66_p10 endpoint_17_66_w10
private theorem endpoint_17_66_w12 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 12 2 193098676521747108 = some 193098676521747108 := by decide +kernel
private theorem endpoint_17_66_p14 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 14 179835709733269868 = some 193098676521747108 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 12 2 179835709733269868 193098676521747108 193098676521747108 endpoint_17_66_p12 endpoint_17_66_w12
private theorem endpoint_17_66_w14 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 14 2 193098676521747108 = some 193098676521747108 := by decide +kernel
private theorem endpoint_17_66_p16 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 16 179835709733269868 = some 193098676521747108 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 14 2 179835709733269868 193098676521747108 193098676521747108 endpoint_17_66_p14 endpoint_17_66_w14
def endpoint_17_66 : CertifiedEndpoint :=
  ⟨⟨17, 66, 1414⟩, 193098676521747108, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_66_flag endpoint_17_66_sources 16 179835709733269868 193098676521747108 rfl endpoint_17_66_base endpoint_17_66_p16) (by decide)⟩
private def endpoint_17_67_flag : Flag := ⟨17, 67, 1346⟩
private def endpoint_17_67_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_17_67_base : receiptBase endpoint_17_67_flag endpoint_17_67_sources = some 175196904498914148 := by decide +kernel
private theorem endpoint_17_67_w0 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 2 175196904498914148 = some 180415277005389197 := by decide +kernel
private theorem endpoint_17_67_w2 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 2 2 180415277005389197 = some 180415277005389197 := by decide +kernel
private theorem endpoint_17_67_p4 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 4 175196904498914148 = some 180415277005389197 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 2 2 175196904498914148 180415277005389197 180415277005389197 endpoint_17_67_w0 endpoint_17_67_w2
private theorem endpoint_17_67_w4 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 4 2 180415277005389197 = some 180415277005389197 := by decide +kernel
private theorem endpoint_17_67_p6 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 6 175196904498914148 = some 180415277005389197 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 4 2 175196904498914148 180415277005389197 180415277005389197 endpoint_17_67_p4 endpoint_17_67_w4
private theorem endpoint_17_67_w6 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 6 2 180415277005389197 = some 180415277005389197 := by decide +kernel
private theorem endpoint_17_67_p8 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 8 175196904498914148 = some 180415277005389197 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 6 2 175196904498914148 180415277005389197 180415277005389197 endpoint_17_67_p6 endpoint_17_67_w6
private theorem endpoint_17_67_w8 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 8 2 180415277005389197 = some 180415277005389197 := by decide +kernel
private theorem endpoint_17_67_p10 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 10 175196904498914148 = some 180415277005389197 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 8 2 175196904498914148 180415277005389197 180415277005389197 endpoint_17_67_p8 endpoint_17_67_w8
private theorem endpoint_17_67_w10 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 10 2 180415277005389197 = some 180415277005389197 := by decide +kernel
private theorem endpoint_17_67_p12 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 12 175196904498914148 = some 180415277005389197 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 10 2 175196904498914148 180415277005389197 180415277005389197 endpoint_17_67_p10 endpoint_17_67_w10
private theorem endpoint_17_67_w12 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 12 2 180415277005389197 = some 180415277005389197 := by decide +kernel
private theorem endpoint_17_67_p14 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 14 175196904498914148 = some 180415277005389197 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 12 2 175196904498914148 180415277005389197 180415277005389197 endpoint_17_67_p12 endpoint_17_67_w12
private theorem endpoint_17_67_w14 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 14 2 180415277005389197 = some 180415277005389197 := by decide +kernel
private theorem endpoint_17_67_p16 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 16 175196904498914148 = some 180415277005389197 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 14 2 175196904498914148 180415277005389197 180415277005389197 endpoint_17_67_p14 endpoint_17_67_w14
def endpoint_17_67 : CertifiedEndpoint :=
  ⟨⟨17, 67, 1346⟩, 180415277005389197, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_17_67_flag endpoint_17_67_sources 16 175196904498914148 180415277005389197 rfl endpoint_17_67_base endpoint_17_67_p16) (by decide)⟩
private def endpoint_17_68_flag : Flag := ⟨17, 68, 1276⟩
private def endpoint_17_68_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_17_68_base : receiptBase endpoint_17_68_flag endpoint_17_68_sources = some 168535383040789662 := by decide +kernel
private theorem endpoint_17_68_w0 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 2 168535383040789662 = some 178075240834475304 := by decide +kernel
private theorem endpoint_17_68_w2 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 2 2 178075240834475304 = some 178075240834475304 := by decide +kernel
private theorem endpoint_17_68_p4 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 4 168535383040789662 = some 178075240834475304 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 2 2 168535383040789662 178075240834475304 178075240834475304 endpoint_17_68_w0 endpoint_17_68_w2
private theorem endpoint_17_68_w4 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 4 2 178075240834475304 = some 178075240834475304 := by decide +kernel
private theorem endpoint_17_68_p6 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 6 168535383040789662 = some 178075240834475304 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 4 2 168535383040789662 178075240834475304 178075240834475304 endpoint_17_68_p4 endpoint_17_68_w4
private theorem endpoint_17_68_w6 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 6 2 178075240834475304 = some 178075240834475304 := by decide +kernel
private theorem endpoint_17_68_p8 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 8 168535383040789662 = some 178075240834475304 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 6 2 168535383040789662 178075240834475304 178075240834475304 endpoint_17_68_p6 endpoint_17_68_w6
private theorem endpoint_17_68_w8 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 8 2 178075240834475304 = some 178075240834475304 := by decide +kernel
private theorem endpoint_17_68_p10 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 10 168535383040789662 = some 178075240834475304 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 8 2 168535383040789662 178075240834475304 178075240834475304 endpoint_17_68_p8 endpoint_17_68_w8
private theorem endpoint_17_68_w10 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 10 2 178075240834475304 = some 178075240834475304 := by decide +kernel
private theorem endpoint_17_68_p12 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 12 168535383040789662 = some 178075240834475304 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 10 2 168535383040789662 178075240834475304 178075240834475304 endpoint_17_68_p10 endpoint_17_68_w10
private theorem endpoint_17_68_w12 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 12 2 178075240834475304 = some 178075240834475304 := by decide +kernel
private theorem endpoint_17_68_p14 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 14 168535383040789662 = some 178075240834475304 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 12 2 168535383040789662 178075240834475304 178075240834475304 endpoint_17_68_p12 endpoint_17_68_w12
private theorem endpoint_17_68_w14 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 14 2 178075240834475304 = some 178075240834475304 := by decide +kernel
private theorem endpoint_17_68_p16 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 16 168535383040789662 = some 178075240834475304 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 14 2 168535383040789662 178075240834475304 178075240834475304 endpoint_17_68_p14 endpoint_17_68_w14
def endpoint_17_68 : CertifiedEndpoint :=
  ⟨⟨17, 68, 1276⟩, 178075240834475304, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_17_68_flag endpoint_17_68_sources 16 168535383040789662 178075240834475304 rfl endpoint_17_68_base endpoint_17_68_p16) (by decide)⟩
private def endpoint_17_69_flag : Flag := ⟨17, 69, 1203⟩
private def endpoint_17_69_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_17_69_base : receiptBase endpoint_17_69_flag endpoint_17_69_sources = some 162578607771287892 := by decide +kernel
private theorem endpoint_17_69_w0 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 2 162578607771287892 = some 165836510188180165 := by decide +kernel
private theorem endpoint_17_69_w2 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 2 2 165836510188180165 = some 165836510188180165 := by decide +kernel
private theorem endpoint_17_69_p4 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 4 162578607771287892 = some 165836510188180165 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 2 2 162578607771287892 165836510188180165 165836510188180165 endpoint_17_69_w0 endpoint_17_69_w2
private theorem endpoint_17_69_w4 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 4 2 165836510188180165 = some 165836510188180165 := by decide +kernel
private theorem endpoint_17_69_p6 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 6 162578607771287892 = some 165836510188180165 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 4 2 162578607771287892 165836510188180165 165836510188180165 endpoint_17_69_p4 endpoint_17_69_w4
private theorem endpoint_17_69_w6 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 6 2 165836510188180165 = some 165836510188180165 := by decide +kernel
private theorem endpoint_17_69_p8 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 8 162578607771287892 = some 165836510188180165 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 6 2 162578607771287892 165836510188180165 165836510188180165 endpoint_17_69_p6 endpoint_17_69_w6
private theorem endpoint_17_69_w8 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 8 2 165836510188180165 = some 165836510188180165 := by decide +kernel
private theorem endpoint_17_69_p10 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 10 162578607771287892 = some 165836510188180165 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 8 2 162578607771287892 165836510188180165 165836510188180165 endpoint_17_69_p8 endpoint_17_69_w8
private theorem endpoint_17_69_w10 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 10 2 165836510188180165 = some 165836510188180165 := by decide +kernel
private theorem endpoint_17_69_p12 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 12 162578607771287892 = some 165836510188180165 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 10 2 162578607771287892 165836510188180165 165836510188180165 endpoint_17_69_p10 endpoint_17_69_w10
private theorem endpoint_17_69_w12 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 12 2 165836510188180165 = some 165836510188180165 := by decide +kernel
private theorem endpoint_17_69_p14 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 14 162578607771287892 = some 165836510188180165 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 12 2 162578607771287892 165836510188180165 165836510188180165 endpoint_17_69_p12 endpoint_17_69_w12
private theorem endpoint_17_69_w14 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 14 2 165836510188180165 = some 165836510188180165 := by decide +kernel
private theorem endpoint_17_69_p16 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 16 162578607771287892 = some 165836510188180165 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 14 2 162578607771287892 165836510188180165 165836510188180165 endpoint_17_69_p14 endpoint_17_69_w14
def endpoint_17_69 : CertifiedEndpoint :=
  ⟨⟨17, 69, 1203⟩, 165836510188180165, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_17_69_flag endpoint_17_69_sources 16 162578607771287892 165836510188180165 rfl endpoint_17_69_base endpoint_17_69_p16) (by decide)⟩
private def endpoint_17_70_flag : Flag := ⟨17, 70, 1129⟩
private def endpoint_17_70_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_17_70_base : receiptBase endpoint_17_70_flag endpoint_17_70_sources = some 154656671555545659 := by decide +kernel
private theorem endpoint_17_70_w0 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 2 154656671555545659 = some 162641049663834730 := by decide +kernel
private theorem endpoint_17_70_w2 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 2 2 162641049663834730 = some 162641049663834730 := by decide +kernel
private theorem endpoint_17_70_p4 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 4 154656671555545659 = some 162641049663834730 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 2 2 154656671555545659 162641049663834730 162641049663834730 endpoint_17_70_w0 endpoint_17_70_w2
private theorem endpoint_17_70_w4 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 4 2 162641049663834730 = some 162641049663834730 := by decide +kernel
private theorem endpoint_17_70_p6 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 6 154656671555545659 = some 162641049663834730 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 4 2 154656671555545659 162641049663834730 162641049663834730 endpoint_17_70_p4 endpoint_17_70_w4
private theorem endpoint_17_70_w6 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 6 2 162641049663834730 = some 162641049663834730 := by decide +kernel
private theorem endpoint_17_70_p8 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 8 154656671555545659 = some 162641049663834730 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 6 2 154656671555545659 162641049663834730 162641049663834730 endpoint_17_70_p6 endpoint_17_70_w6
private theorem endpoint_17_70_w8 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 8 2 162641049663834730 = some 162641049663834730 := by decide +kernel
private theorem endpoint_17_70_p10 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 10 154656671555545659 = some 162641049663834730 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 8 2 154656671555545659 162641049663834730 162641049663834730 endpoint_17_70_p8 endpoint_17_70_w8
private theorem endpoint_17_70_w10 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 10 2 162641049663834730 = some 162641049663834730 := by decide +kernel
private theorem endpoint_17_70_p12 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 12 154656671555545659 = some 162641049663834730 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 10 2 154656671555545659 162641049663834730 162641049663834730 endpoint_17_70_p10 endpoint_17_70_w10
private theorem endpoint_17_70_w12 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 12 2 162641049663834730 = some 162641049663834730 := by decide +kernel
private theorem endpoint_17_70_p14 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 14 154656671555545659 = some 162641049663834730 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 12 2 154656671555545659 162641049663834730 162641049663834730 endpoint_17_70_p12 endpoint_17_70_w12
private theorem endpoint_17_70_w14 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 14 2 162641049663834730 = some 162641049663834730 := by decide +kernel
private theorem endpoint_17_70_p16 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 16 154656671555545659 = some 162641049663834730 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 14 2 154656671555545659 162641049663834730 162641049663834730 endpoint_17_70_p14 endpoint_17_70_w14
def endpoint_17_70 : CertifiedEndpoint :=
  ⟨⟨17, 70, 1129⟩, 162641049663834730, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_17_70_flag endpoint_17_70_sources 16 154656671555545659 162641049663834730 rfl endpoint_17_70_base endpoint_17_70_p16) (by decide)⟩
private def endpoint_17_71_flag : Flag := ⟨17, 71, 1053⟩
private def endpoint_17_71_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_17_71_base : receiptBase endpoint_17_71_flag endpoint_17_71_sources = some 146209524817083656 := by decide +kernel
private theorem endpoint_17_71_w0 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 2 146209524817083656 = some 159086022596014131 := by decide +kernel
private theorem endpoint_17_71_w2 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 2 2 159086022596014131 = some 159086022596014131 := by decide +kernel
private theorem endpoint_17_71_p4 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 4 146209524817083656 = some 159086022596014131 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 2 2 146209524817083656 159086022596014131 159086022596014131 endpoint_17_71_w0 endpoint_17_71_w2
private theorem endpoint_17_71_w4 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 4 2 159086022596014131 = some 159086022596014131 := by decide +kernel
private theorem endpoint_17_71_p6 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 6 146209524817083656 = some 159086022596014131 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 4 2 146209524817083656 159086022596014131 159086022596014131 endpoint_17_71_p4 endpoint_17_71_w4
private theorem endpoint_17_71_w6 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 6 2 159086022596014131 = some 159086022596014131 := by decide +kernel
private theorem endpoint_17_71_p8 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 8 146209524817083656 = some 159086022596014131 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 6 2 146209524817083656 159086022596014131 159086022596014131 endpoint_17_71_p6 endpoint_17_71_w6
private theorem endpoint_17_71_w8 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 8 2 159086022596014131 = some 159086022596014131 := by decide +kernel
private theorem endpoint_17_71_p10 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 10 146209524817083656 = some 159086022596014131 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 8 2 146209524817083656 159086022596014131 159086022596014131 endpoint_17_71_p8 endpoint_17_71_w8
private theorem endpoint_17_71_w10 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 10 2 159086022596014131 = some 159086022596014131 := by decide +kernel
private theorem endpoint_17_71_p12 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 12 146209524817083656 = some 159086022596014131 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 10 2 146209524817083656 159086022596014131 159086022596014131 endpoint_17_71_p10 endpoint_17_71_w10
private theorem endpoint_17_71_w12 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 12 2 159086022596014131 = some 159086022596014131 := by decide +kernel
private theorem endpoint_17_71_p14 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 14 146209524817083656 = some 159086022596014131 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 12 2 146209524817083656 159086022596014131 159086022596014131 endpoint_17_71_p12 endpoint_17_71_w12
private theorem endpoint_17_71_w14 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 14 2 159086022596014131 = some 159086022596014131 := by decide +kernel
private theorem endpoint_17_71_p16 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 16 146209524817083656 = some 159086022596014131 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 14 2 146209524817083656 159086022596014131 159086022596014131 endpoint_17_71_p14 endpoint_17_71_w14
def endpoint_17_71 : CertifiedEndpoint :=
  ⟨⟨17, 71, 1053⟩, 159086022596014131, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_17_71_flag endpoint_17_71_sources 16 146209524817083656 159086022596014131 rfl endpoint_17_71_base endpoint_17_71_p16) (by decide)⟩
def endpoint_17_72 : CertifiedEndpoint :=
  ⟨⟨17, 72, 975⟩, 250899916000626295, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_73 : CertifiedEndpoint :=
  ⟨⟨17, 73, 894⟩, 232656972219916497, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_74 : CertifiedEndpoint :=
  ⟨⟨17, 74, 811⟩, 213165622157374603, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_75 : CertifiedEndpoint :=
  ⟨⟨17, 75, 726⟩, 192400301533000489, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_76 : CertifiedEndpoint :=
  ⟨⟨17, 76, 638⟩, 170049969635879626, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_77 : CertifiedEndpoint :=
  ⟨⟨17, 77, 548⟩, 146366017190259587, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_78 : CertifiedEndpoint :=
  ⟨⟨17, 78, 454⟩, 120734884200978022, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_79 : CertifiedEndpoint :=
  ⟨⟨17, 79, 359⟩, 94000217820778084, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_80 : CertifiedEndpoint :=
  ⟨⟨17, 80, 260⟩, 65241678056916248, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_81 : CertifiedEndpoint :=
  ⟨⟨17, 81, 159⟩, 35021696344554616, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_18 : CertifiedEndpoint :=
  ⟨⟨18, 18, 3216⟩, 142464528104038848, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_19 : CertifiedEndpoint :=
  ⟨⟨18, 19, 3187⟩, 145881078449679356, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_20 : CertifiedEndpoint :=
  ⟨⟨18, 20, 3158⟩, 149211435236394138, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_21 : CertifiedEndpoint :=
  ⟨⟨18, 21, 3129⟩, 161880827790806322, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_22 : CertifiedEndpoint :=
  ⟨⟨18, 22, 3099⟩, 174227144841944417, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_23 : CertifiedEndpoint :=
  ⟨⟨18, 23, 3069⟩, 186297838415663546, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_24 : CertifiedEndpoint :=
  ⟨⟨18, 24, 3038⟩, 198027382815458162, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_25 : CertifiedEndpoint :=
  ⟨⟨18, 25, 3007⟩, 209472266902508600, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_26 : CertifiedEndpoint :=
  ⟨⟨18, 26, 2975⟩, 220557928144984101, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_27 : CertifiedEndpoint :=
  ⟨⟨18, 27, 2942⟩, 231270811289896847, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_28 : CertifiedEndpoint :=
  ⟨⟨18, 28, 2909⟩, 241680960451414991, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_29 : CertifiedEndpoint :=
  ⟨⟨18, 29, 2876⟩, 251788375629538533, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_18_30_flag : Flag := ⟨18, 30, 2842⟩
private def endpoint_18_30_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_18_30_base : receiptBase endpoint_18_30_flag endpoint_18_30_sources = some 177036334138965135 := by decide +kernel
private theorem endpoint_18_30_w0 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 2 177036334138965135 = some 177036334138965135 := by decide +kernel
private theorem endpoint_18_30_w2 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 2 2 177036334138965135 = some 177036334138965135 := by decide +kernel
private theorem endpoint_18_30_p4 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 4 177036334138965135 = some 177036334138965135 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 2 2 177036334138965135 177036334138965135 177036334138965135 endpoint_18_30_w0 endpoint_18_30_w2
private theorem endpoint_18_30_w4 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 4 2 177036334138965135 = some 177036334138965135 := by decide +kernel
private theorem endpoint_18_30_p6 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 6 177036334138965135 = some 177036334138965135 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 4 2 177036334138965135 177036334138965135 177036334138965135 endpoint_18_30_p4 endpoint_18_30_w4
private theorem endpoint_18_30_w6 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 6 2 177036334138965135 = some 177036334138965135 := by decide +kernel
private theorem endpoint_18_30_p8 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 8 177036334138965135 = some 177036334138965135 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 6 2 177036334138965135 177036334138965135 177036334138965135 endpoint_18_30_p6 endpoint_18_30_w6
private theorem endpoint_18_30_w8 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 8 2 177036334138965135 = some 177036334138965135 := by decide +kernel
private theorem endpoint_18_30_p10 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 10 177036334138965135 = some 177036334138965135 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 8 2 177036334138965135 177036334138965135 177036334138965135 endpoint_18_30_p8 endpoint_18_30_w8
private theorem endpoint_18_30_w10 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 10 2 177036334138965135 = some 177036334138965135 := by decide +kernel
private theorem endpoint_18_30_p12 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 12 177036334138965135 = some 177036334138965135 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 10 2 177036334138965135 177036334138965135 177036334138965135 endpoint_18_30_p10 endpoint_18_30_w10
private theorem endpoint_18_30_w12 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 12 2 177036334138965135 = some 177036334138965135 := by decide +kernel
private theorem endpoint_18_30_p14 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 14 177036334138965135 = some 177036334138965135 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 12 2 177036334138965135 177036334138965135 177036334138965135 endpoint_18_30_p12 endpoint_18_30_w12
private theorem endpoint_18_30_w14 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 14 2 177036334138965135 = some 177036334138965135 := by decide +kernel
private theorem endpoint_18_30_p16 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 16 177036334138965135 = some 177036334138965135 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 14 2 177036334138965135 177036334138965135 177036334138965135 endpoint_18_30_p14 endpoint_18_30_w14
private theorem endpoint_18_30_w16 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 16 1 177036334138965135 = some 177036334138965135 := by decide +kernel
private theorem endpoint_18_30_p17 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 17 177036334138965135 = some 177036334138965135 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 16 1 177036334138965135 177036334138965135 177036334138965135 endpoint_18_30_p16 endpoint_18_30_w16
def endpoint_18_30 : CertifiedEndpoint :=
  ⟨⟨18, 30, 2842⟩, 177036334138965135, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_18_30_flag endpoint_18_30_sources 17 177036334138965135 177036334138965135 rfl endpoint_18_30_base endpoint_18_30_p17) (by decide)⟩
private def endpoint_18_31_flag : Flag := ⟨18, 31, 2808⟩
private def endpoint_18_31_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_18_31_base : receiptBase endpoint_18_31_flag endpoint_18_31_sources = some 179766029658849822 := by decide +kernel
private theorem endpoint_18_31_w0 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 2 179766029658849822 = some 179766029658849822 := by decide +kernel
private theorem endpoint_18_31_w2 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 2 2 179766029658849822 = some 179766029658849822 := by decide +kernel
private theorem endpoint_18_31_p4 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 4 179766029658849822 = some 179766029658849822 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 2 2 179766029658849822 179766029658849822 179766029658849822 endpoint_18_31_w0 endpoint_18_31_w2
private theorem endpoint_18_31_w4 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 4 2 179766029658849822 = some 179766029658849822 := by decide +kernel
private theorem endpoint_18_31_p6 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 6 179766029658849822 = some 179766029658849822 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 4 2 179766029658849822 179766029658849822 179766029658849822 endpoint_18_31_p4 endpoint_18_31_w4
private theorem endpoint_18_31_w6 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 6 2 179766029658849822 = some 179766029658849822 := by decide +kernel
private theorem endpoint_18_31_p8 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 8 179766029658849822 = some 179766029658849822 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 6 2 179766029658849822 179766029658849822 179766029658849822 endpoint_18_31_p6 endpoint_18_31_w6
private theorem endpoint_18_31_w8 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 8 2 179766029658849822 = some 179766029658849822 := by decide +kernel
private theorem endpoint_18_31_p10 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 10 179766029658849822 = some 179766029658849822 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 8 2 179766029658849822 179766029658849822 179766029658849822 endpoint_18_31_p8 endpoint_18_31_w8
private theorem endpoint_18_31_w10 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 10 2 179766029658849822 = some 179766029658849822 := by decide +kernel
private theorem endpoint_18_31_p12 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 12 179766029658849822 = some 179766029658849822 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 10 2 179766029658849822 179766029658849822 179766029658849822 endpoint_18_31_p10 endpoint_18_31_w10
private theorem endpoint_18_31_w12 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 12 2 179766029658849822 = some 179766029658849822 := by decide +kernel
private theorem endpoint_18_31_p14 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 14 179766029658849822 = some 179766029658849822 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 12 2 179766029658849822 179766029658849822 179766029658849822 endpoint_18_31_p12 endpoint_18_31_w12
private theorem endpoint_18_31_w14 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 14 2 179766029658849822 = some 179766029658849822 := by decide +kernel
private theorem endpoint_18_31_p16 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 16 179766029658849822 = some 179766029658849822 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 14 2 179766029658849822 179766029658849822 179766029658849822 endpoint_18_31_p14 endpoint_18_31_w14
private theorem endpoint_18_31_w16 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 16 1 179766029658849822 = some 179766029658849822 := by decide +kernel
private theorem endpoint_18_31_p17 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 17 179766029658849822 = some 179766029658849822 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 16 1 179766029658849822 179766029658849822 179766029658849822 endpoint_18_31_p16 endpoint_18_31_w16
def endpoint_18_31 : CertifiedEndpoint :=
  ⟨⟨18, 31, 2808⟩, 179766029658849822, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_18_31_flag endpoint_18_31_sources 17 179766029658849822 179766029658849822 rfl endpoint_18_31_base endpoint_18_31_p17) (by decide)⟩
private def endpoint_18_32_flag : Flag := ⟨18, 32, 2772⟩
private def endpoint_18_32_sources : Sources := ⟨contact32, contact08, contact04⟩
private theorem endpoint_18_32_base : receiptBase endpoint_18_32_flag endpoint_18_32_sources = some 182491600773882626 := by decide +kernel
private theorem endpoint_18_32_w0 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 2 182491600773882626 = some 182491600773882626 := by decide +kernel
private theorem endpoint_18_32_w2 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 2 2 182491600773882626 = some 182491600773882626 := by decide +kernel
private theorem endpoint_18_32_p4 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 4 182491600773882626 = some 182491600773882626 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 2 2 182491600773882626 182491600773882626 182491600773882626 endpoint_18_32_w0 endpoint_18_32_w2
private theorem endpoint_18_32_w4 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 4 2 182491600773882626 = some 182491600773882626 := by decide +kernel
private theorem endpoint_18_32_p6 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 6 182491600773882626 = some 182491600773882626 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 4 2 182491600773882626 182491600773882626 182491600773882626 endpoint_18_32_p4 endpoint_18_32_w4
private theorem endpoint_18_32_w6 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 6 2 182491600773882626 = some 182491600773882626 := by decide +kernel
private theorem endpoint_18_32_p8 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 8 182491600773882626 = some 182491600773882626 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 6 2 182491600773882626 182491600773882626 182491600773882626 endpoint_18_32_p6 endpoint_18_32_w6
private theorem endpoint_18_32_w8 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 8 2 182491600773882626 = some 182491600773882626 := by decide +kernel
private theorem endpoint_18_32_p10 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 10 182491600773882626 = some 182491600773882626 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 8 2 182491600773882626 182491600773882626 182491600773882626 endpoint_18_32_p8 endpoint_18_32_w8
private theorem endpoint_18_32_w10 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 10 2 182491600773882626 = some 182491600773882626 := by decide +kernel
private theorem endpoint_18_32_p12 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 12 182491600773882626 = some 182491600773882626 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 10 2 182491600773882626 182491600773882626 182491600773882626 endpoint_18_32_p10 endpoint_18_32_w10
private theorem endpoint_18_32_w12 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 12 2 182491600773882626 = some 182491600773882626 := by decide +kernel
private theorem endpoint_18_32_p14 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 14 182491600773882626 = some 182491600773882626 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 12 2 182491600773882626 182491600773882626 182491600773882626 endpoint_18_32_p12 endpoint_18_32_w12
private theorem endpoint_18_32_w14 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 14 2 182491600773882626 = some 182491600773882626 := by decide +kernel
private theorem endpoint_18_32_p16 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 16 182491600773882626 = some 182491600773882626 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 14 2 182491600773882626 182491600773882626 182491600773882626 endpoint_18_32_p14 endpoint_18_32_w14
private theorem endpoint_18_32_w16 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 16 1 182491600773882626 = some 182491600773882626 := by decide +kernel
private theorem endpoint_18_32_p17 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 17 182491600773882626 = some 182491600773882626 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 16 1 182491600773882626 182491600773882626 182491600773882626 endpoint_18_32_p16 endpoint_18_32_w16
def endpoint_18_32 : CertifiedEndpoint :=
  ⟨⟨18, 32, 2772⟩, 182491600773882626, .terminal ⟨contact32, contact08, contact04⟩ (finish_receipt_window endpoint_18_32_flag endpoint_18_32_sources 17 182491600773882626 182491600773882626 rfl endpoint_18_32_base endpoint_18_32_p17) (by decide)⟩
private def endpoint_18_33_flag : Flag := ⟨18, 33, 2737⟩
private def endpoint_18_33_sources : Sources := ⟨contact32, contact08, contact04⟩
private theorem endpoint_18_33_base : receiptBase endpoint_18_33_flag endpoint_18_33_sources = some 184933202036531869 := by decide +kernel
private theorem endpoint_18_33_w0 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 2 184933202036531869 = some 184933202036531869 := by decide +kernel
private theorem endpoint_18_33_w2 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 2 2 184933202036531869 = some 184933202036531869 := by decide +kernel
private theorem endpoint_18_33_p4 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 4 184933202036531869 = some 184933202036531869 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 2 2 184933202036531869 184933202036531869 184933202036531869 endpoint_18_33_w0 endpoint_18_33_w2
private theorem endpoint_18_33_w4 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 4 2 184933202036531869 = some 184933202036531869 := by decide +kernel
private theorem endpoint_18_33_p6 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 6 184933202036531869 = some 184933202036531869 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 4 2 184933202036531869 184933202036531869 184933202036531869 endpoint_18_33_p4 endpoint_18_33_w4
private theorem endpoint_18_33_w6 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 6 2 184933202036531869 = some 184933202036531869 := by decide +kernel
private theorem endpoint_18_33_p8 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 8 184933202036531869 = some 184933202036531869 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 6 2 184933202036531869 184933202036531869 184933202036531869 endpoint_18_33_p6 endpoint_18_33_w6
private theorem endpoint_18_33_w8 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 8 2 184933202036531869 = some 184933202036531869 := by decide +kernel
private theorem endpoint_18_33_p10 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 10 184933202036531869 = some 184933202036531869 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 8 2 184933202036531869 184933202036531869 184933202036531869 endpoint_18_33_p8 endpoint_18_33_w8
private theorem endpoint_18_33_w10 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 10 2 184933202036531869 = some 184933202036531869 := by decide +kernel
private theorem endpoint_18_33_p12 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 12 184933202036531869 = some 184933202036531869 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 10 2 184933202036531869 184933202036531869 184933202036531869 endpoint_18_33_p10 endpoint_18_33_w10
private theorem endpoint_18_33_w12 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 12 2 184933202036531869 = some 184933202036531869 := by decide +kernel
private theorem endpoint_18_33_p14 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 14 184933202036531869 = some 184933202036531869 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 12 2 184933202036531869 184933202036531869 184933202036531869 endpoint_18_33_p12 endpoint_18_33_w12
private theorem endpoint_18_33_w14 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 14 2 184933202036531869 = some 184933202036531869 := by decide +kernel
private theorem endpoint_18_33_p16 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 16 184933202036531869 = some 184933202036531869 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 14 2 184933202036531869 184933202036531869 184933202036531869 endpoint_18_33_p14 endpoint_18_33_w14
private theorem endpoint_18_33_w16 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 16 1 184933202036531869 = some 184933202036531869 := by decide +kernel
private theorem endpoint_18_33_p17 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 17 184933202036531869 = some 184933202036531869 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 16 1 184933202036531869 184933202036531869 184933202036531869 endpoint_18_33_p16 endpoint_18_33_w16
def endpoint_18_33 : CertifiedEndpoint :=
  ⟨⟨18, 33, 2737⟩, 184933202036531869, .terminal ⟨contact32, contact08, contact04⟩ (finish_receipt_window endpoint_18_33_flag endpoint_18_33_sources 17 184933202036531869 184933202036531869 rfl endpoint_18_33_base endpoint_18_33_p17) (by decide)⟩
private def endpoint_18_34_flag : Flag := ⟨18, 34, 2700⟩
private def endpoint_18_34_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_34_base : receiptBase endpoint_18_34_flag endpoint_18_34_sources = some 187528185904884688 := by decide +kernel
private theorem endpoint_18_34_w0 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 2 187528185904884688 = some 187528185904884688 := by decide +kernel
private theorem endpoint_18_34_w2 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 2 2 187528185904884688 = some 187528185904884688 := by decide +kernel
private theorem endpoint_18_34_p4 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 4 187528185904884688 = some 187528185904884688 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 2 2 187528185904884688 187528185904884688 187528185904884688 endpoint_18_34_w0 endpoint_18_34_w2
private theorem endpoint_18_34_w4 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 4 2 187528185904884688 = some 187528185904884688 := by decide +kernel
private theorem endpoint_18_34_p6 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 6 187528185904884688 = some 187528185904884688 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 4 2 187528185904884688 187528185904884688 187528185904884688 endpoint_18_34_p4 endpoint_18_34_w4
private theorem endpoint_18_34_w6 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 6 2 187528185904884688 = some 187528185904884688 := by decide +kernel
private theorem endpoint_18_34_p8 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 8 187528185904884688 = some 187528185904884688 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 6 2 187528185904884688 187528185904884688 187528185904884688 endpoint_18_34_p6 endpoint_18_34_w6
private theorem endpoint_18_34_w8 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 8 2 187528185904884688 = some 187528185904884688 := by decide +kernel
private theorem endpoint_18_34_p10 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 10 187528185904884688 = some 187528185904884688 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 8 2 187528185904884688 187528185904884688 187528185904884688 endpoint_18_34_p8 endpoint_18_34_w8
private theorem endpoint_18_34_w10 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 10 2 187528185904884688 = some 187528185904884688 := by decide +kernel
private theorem endpoint_18_34_p12 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 12 187528185904884688 = some 187528185904884688 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 10 2 187528185904884688 187528185904884688 187528185904884688 endpoint_18_34_p10 endpoint_18_34_w10
private theorem endpoint_18_34_w12 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 12 2 187528185904884688 = some 187528185904884688 := by decide +kernel
private theorem endpoint_18_34_p14 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 14 187528185904884688 = some 187528185904884688 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 12 2 187528185904884688 187528185904884688 187528185904884688 endpoint_18_34_p12 endpoint_18_34_w12
private theorem endpoint_18_34_w14 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 14 2 187528185904884688 = some 187528185904884688 := by decide +kernel
private theorem endpoint_18_34_p16 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 16 187528185904884688 = some 187528185904884688 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 14 2 187528185904884688 187528185904884688 187528185904884688 endpoint_18_34_p14 endpoint_18_34_w14
private theorem endpoint_18_34_w16 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 16 1 187528185904884688 = some 187528185904884688 := by decide +kernel
private theorem endpoint_18_34_p17 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 17 187528185904884688 = some 187528185904884688 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 16 1 187528185904884688 187528185904884688 187528185904884688 endpoint_18_34_p16 endpoint_18_34_w16
def endpoint_18_34 : CertifiedEndpoint :=
  ⟨⟨18, 34, 2700⟩, 187528185904884688, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_34_flag endpoint_18_34_sources 17 187528185904884688 187528185904884688 rfl endpoint_18_34_base endpoint_18_34_p17) (by decide)⟩
private def endpoint_18_35_flag : Flag := ⟨18, 35, 2663⟩
private def endpoint_18_35_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_35_base : receiptBase endpoint_18_35_flag endpoint_18_35_sources = some 189562491001134879 := by decide +kernel
private theorem endpoint_18_35_w0 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 2 189562491001134879 = some 189562491001134879 := by decide +kernel
private theorem endpoint_18_35_w2 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 2 2 189562491001134879 = some 189562491001134879 := by decide +kernel
private theorem endpoint_18_35_p4 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 4 189562491001134879 = some 189562491001134879 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 2 2 189562491001134879 189562491001134879 189562491001134879 endpoint_18_35_w0 endpoint_18_35_w2
private theorem endpoint_18_35_w4 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 4 2 189562491001134879 = some 189562491001134879 := by decide +kernel
private theorem endpoint_18_35_p6 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 6 189562491001134879 = some 189562491001134879 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 4 2 189562491001134879 189562491001134879 189562491001134879 endpoint_18_35_p4 endpoint_18_35_w4
private theorem endpoint_18_35_w6 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 6 2 189562491001134879 = some 189562491001134879 := by decide +kernel
private theorem endpoint_18_35_p8 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 8 189562491001134879 = some 189562491001134879 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 6 2 189562491001134879 189562491001134879 189562491001134879 endpoint_18_35_p6 endpoint_18_35_w6
private theorem endpoint_18_35_w8 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 8 2 189562491001134879 = some 189562491001134879 := by decide +kernel
private theorem endpoint_18_35_p10 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 10 189562491001134879 = some 189562491001134879 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 8 2 189562491001134879 189562491001134879 189562491001134879 endpoint_18_35_p8 endpoint_18_35_w8
private theorem endpoint_18_35_w10 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 10 2 189562491001134879 = some 189562491001134879 := by decide +kernel
private theorem endpoint_18_35_p12 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 12 189562491001134879 = some 189562491001134879 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 10 2 189562491001134879 189562491001134879 189562491001134879 endpoint_18_35_p10 endpoint_18_35_w10
private theorem endpoint_18_35_w12 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 12 2 189562491001134879 = some 189562491001134879 := by decide +kernel
private theorem endpoint_18_35_p14 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 14 189562491001134879 = some 189562491001134879 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 12 2 189562491001134879 189562491001134879 189562491001134879 endpoint_18_35_p12 endpoint_18_35_w12
private theorem endpoint_18_35_w14 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 14 2 189562491001134879 = some 189562491001134879 := by decide +kernel
private theorem endpoint_18_35_p16 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 16 189562491001134879 = some 189562491001134879 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 14 2 189562491001134879 189562491001134879 189562491001134879 endpoint_18_35_p14 endpoint_18_35_w14
private theorem endpoint_18_35_w16 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 16 1 189562491001134879 = some 189562491001134879 := by decide +kernel
private theorem endpoint_18_35_p17 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 17 189562491001134879 = some 189562491001134879 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 16 1 189562491001134879 189562491001134879 189562491001134879 endpoint_18_35_p16 endpoint_18_35_w16
def endpoint_18_35 : CertifiedEndpoint :=
  ⟨⟨18, 35, 2663⟩, 189562491001134879, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_35_flag endpoint_18_35_sources 17 189562491001134879 189562491001134879 rfl endpoint_18_35_base endpoint_18_35_p17) (by decide)⟩
private def endpoint_18_36_flag : Flag := ⟨18, 36, 2626⟩
private def endpoint_18_36_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_36_base : receiptBase endpoint_18_36_flag endpoint_18_36_sources = some 191470572275929244 := by decide +kernel
private theorem endpoint_18_36_w0 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 2 191470572275929244 = some 191470572275929244 := by decide +kernel
private theorem endpoint_18_36_w2 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 2 2 191470572275929244 = some 191470572275929244 := by decide +kernel
private theorem endpoint_18_36_p4 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 4 191470572275929244 = some 191470572275929244 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 2 2 191470572275929244 191470572275929244 191470572275929244 endpoint_18_36_w0 endpoint_18_36_w2
private theorem endpoint_18_36_w4 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 4 2 191470572275929244 = some 191470572275929244 := by decide +kernel
private theorem endpoint_18_36_p6 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 6 191470572275929244 = some 191470572275929244 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 4 2 191470572275929244 191470572275929244 191470572275929244 endpoint_18_36_p4 endpoint_18_36_w4
private theorem endpoint_18_36_w6 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 6 2 191470572275929244 = some 191470572275929244 := by decide +kernel
private theorem endpoint_18_36_p8 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 8 191470572275929244 = some 191470572275929244 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 6 2 191470572275929244 191470572275929244 191470572275929244 endpoint_18_36_p6 endpoint_18_36_w6
private theorem endpoint_18_36_w8 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 8 2 191470572275929244 = some 191470572275929244 := by decide +kernel
private theorem endpoint_18_36_p10 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 10 191470572275929244 = some 191470572275929244 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 8 2 191470572275929244 191470572275929244 191470572275929244 endpoint_18_36_p8 endpoint_18_36_w8
private theorem endpoint_18_36_w10 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 10 2 191470572275929244 = some 191470572275929244 := by decide +kernel
private theorem endpoint_18_36_p12 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 12 191470572275929244 = some 191470572275929244 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 10 2 191470572275929244 191470572275929244 191470572275929244 endpoint_18_36_p10 endpoint_18_36_w10
private theorem endpoint_18_36_w12 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 12 2 191470572275929244 = some 191470572275929244 := by decide +kernel
private theorem endpoint_18_36_p14 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 14 191470572275929244 = some 191470572275929244 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 12 2 191470572275929244 191470572275929244 191470572275929244 endpoint_18_36_p12 endpoint_18_36_w12
private theorem endpoint_18_36_w14 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 14 2 191470572275929244 = some 191470572275929244 := by decide +kernel
private theorem endpoint_18_36_p16 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 16 191470572275929244 = some 191470572275929244 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 14 2 191470572275929244 191470572275929244 191470572275929244 endpoint_18_36_p14 endpoint_18_36_w14
private theorem endpoint_18_36_w16 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 16 1 191470572275929244 = some 191470572275929244 := by decide +kernel
private theorem endpoint_18_36_p17 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 17 191470572275929244 = some 191470572275929244 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 16 1 191470572275929244 191470572275929244 191470572275929244 endpoint_18_36_p16 endpoint_18_36_w16
def endpoint_18_36 : CertifiedEndpoint :=
  ⟨⟨18, 36, 2626⟩, 191470572275929244, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_36_flag endpoint_18_36_sources 17 191470572275929244 191470572275929244 rfl endpoint_18_36_base endpoint_18_36_p17) (by decide)⟩
private def endpoint_18_37_flag : Flag := ⟨18, 37, 2588⟩
private def endpoint_18_37_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_37_base : receiptBase endpoint_18_37_flag endpoint_18_37_sources = some 193178837564423901 := by decide +kernel
private theorem endpoint_18_37_w0 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 2 193178837564423901 = some 193178837564423901 := by decide +kernel
private theorem endpoint_18_37_w2 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 2 2 193178837564423901 = some 193178837564423901 := by decide +kernel
private theorem endpoint_18_37_p4 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 4 193178837564423901 = some 193178837564423901 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 2 2 193178837564423901 193178837564423901 193178837564423901 endpoint_18_37_w0 endpoint_18_37_w2
private theorem endpoint_18_37_w4 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 4 2 193178837564423901 = some 193178837564423901 := by decide +kernel
private theorem endpoint_18_37_p6 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 6 193178837564423901 = some 193178837564423901 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 4 2 193178837564423901 193178837564423901 193178837564423901 endpoint_18_37_p4 endpoint_18_37_w4
private theorem endpoint_18_37_w6 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 6 2 193178837564423901 = some 193178837564423901 := by decide +kernel
private theorem endpoint_18_37_p8 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 8 193178837564423901 = some 193178837564423901 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 6 2 193178837564423901 193178837564423901 193178837564423901 endpoint_18_37_p6 endpoint_18_37_w6
private theorem endpoint_18_37_w8 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 8 2 193178837564423901 = some 193178837564423901 := by decide +kernel
private theorem endpoint_18_37_p10 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 10 193178837564423901 = some 193178837564423901 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 8 2 193178837564423901 193178837564423901 193178837564423901 endpoint_18_37_p8 endpoint_18_37_w8
private theorem endpoint_18_37_w10 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 10 2 193178837564423901 = some 193178837564423901 := by decide +kernel
private theorem endpoint_18_37_p12 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 12 193178837564423901 = some 193178837564423901 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 10 2 193178837564423901 193178837564423901 193178837564423901 endpoint_18_37_p10 endpoint_18_37_w10
private theorem endpoint_18_37_w12 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 12 2 193178837564423901 = some 193178837564423901 := by decide +kernel
private theorem endpoint_18_37_p14 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 14 193178837564423901 = some 193178837564423901 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 12 2 193178837564423901 193178837564423901 193178837564423901 endpoint_18_37_p12 endpoint_18_37_w12
private theorem endpoint_18_37_w14 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 14 2 193178837564423901 = some 193178837564423901 := by decide +kernel
private theorem endpoint_18_37_p16 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 16 193178837564423901 = some 193178837564423901 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 14 2 193178837564423901 193178837564423901 193178837564423901 endpoint_18_37_p14 endpoint_18_37_w14
private theorem endpoint_18_37_w16 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 16 1 193178837564423901 = some 193178837564423901 := by decide +kernel
private theorem endpoint_18_37_p17 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 17 193178837564423901 = some 193178837564423901 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 16 1 193178837564423901 193178837564423901 193178837564423901 endpoint_18_37_p16 endpoint_18_37_w16
def endpoint_18_37 : CertifiedEndpoint :=
  ⟨⟨18, 37, 2588⟩, 193178837564423901, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_37_flag endpoint_18_37_sources 17 193178837564423901 193178837564423901 rfl endpoint_18_37_base endpoint_18_37_p17) (by decide)⟩
private def endpoint_18_38_flag : Flag := ⟨18, 38, 2549⟩
private def endpoint_18_38_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_38_base : receiptBase endpoint_18_38_flag endpoint_18_38_sources = some 194682237913760617 := by decide +kernel
private theorem endpoint_18_38_w0 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 2 194682237913760617 = some 194682237913760617 := by decide +kernel
private theorem endpoint_18_38_w2 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 2 2 194682237913760617 = some 194682237913760617 := by decide +kernel
private theorem endpoint_18_38_p4 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 4 194682237913760617 = some 194682237913760617 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 2 2 194682237913760617 194682237913760617 194682237913760617 endpoint_18_38_w0 endpoint_18_38_w2
private theorem endpoint_18_38_w4 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 4 2 194682237913760617 = some 194682237913760617 := by decide +kernel
private theorem endpoint_18_38_p6 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 6 194682237913760617 = some 194682237913760617 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 4 2 194682237913760617 194682237913760617 194682237913760617 endpoint_18_38_p4 endpoint_18_38_w4
private theorem endpoint_18_38_w6 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 6 2 194682237913760617 = some 194682237913760617 := by decide +kernel
private theorem endpoint_18_38_p8 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 8 194682237913760617 = some 194682237913760617 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 6 2 194682237913760617 194682237913760617 194682237913760617 endpoint_18_38_p6 endpoint_18_38_w6
private theorem endpoint_18_38_w8 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 8 2 194682237913760617 = some 194682237913760617 := by decide +kernel
private theorem endpoint_18_38_p10 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 10 194682237913760617 = some 194682237913760617 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 8 2 194682237913760617 194682237913760617 194682237913760617 endpoint_18_38_p8 endpoint_18_38_w8
private theorem endpoint_18_38_w10 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 10 2 194682237913760617 = some 194682237913760617 := by decide +kernel
private theorem endpoint_18_38_p12 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 12 194682237913760617 = some 194682237913760617 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 10 2 194682237913760617 194682237913760617 194682237913760617 endpoint_18_38_p10 endpoint_18_38_w10
private theorem endpoint_18_38_w12 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 12 2 194682237913760617 = some 194682237913760617 := by decide +kernel
private theorem endpoint_18_38_p14 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 14 194682237913760617 = some 194682237913760617 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 12 2 194682237913760617 194682237913760617 194682237913760617 endpoint_18_38_p12 endpoint_18_38_w12
private theorem endpoint_18_38_w14 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 14 2 194682237913760617 = some 194682237913760617 := by decide +kernel
private theorem endpoint_18_38_p16 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 16 194682237913760617 = some 194682237913760617 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 14 2 194682237913760617 194682237913760617 194682237913760617 endpoint_18_38_p14 endpoint_18_38_w14
private theorem endpoint_18_38_w16 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 16 1 194682237913760617 = some 194682237913760617 := by decide +kernel
private theorem endpoint_18_38_p17 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 17 194682237913760617 = some 194682237913760617 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 16 1 194682237913760617 194682237913760617 194682237913760617 endpoint_18_38_p16 endpoint_18_38_w16
def endpoint_18_38 : CertifiedEndpoint :=
  ⟨⟨18, 38, 2549⟩, 194682237913760617, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_38_flag endpoint_18_38_sources 17 194682237913760617 194682237913760617 rfl endpoint_18_38_base endpoint_18_38_p17) (by decide)⟩
private def endpoint_18_39_flag : Flag := ⟨18, 39, 2509⟩
private def endpoint_18_39_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_39_base : receiptBase endpoint_18_39_flag endpoint_18_39_sources = some 195975724371081159 := by decide +kernel
private theorem endpoint_18_39_w0 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 2 195975724371081159 = some 195975724371081159 := by decide +kernel
private theorem endpoint_18_39_w2 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 2 2 195975724371081159 = some 195975724371081159 := by decide +kernel
private theorem endpoint_18_39_p4 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 4 195975724371081159 = some 195975724371081159 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 2 2 195975724371081159 195975724371081159 195975724371081159 endpoint_18_39_w0 endpoint_18_39_w2
private theorem endpoint_18_39_w4 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 4 2 195975724371081159 = some 195975724371081159 := by decide +kernel
private theorem endpoint_18_39_p6 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 6 195975724371081159 = some 195975724371081159 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 4 2 195975724371081159 195975724371081159 195975724371081159 endpoint_18_39_p4 endpoint_18_39_w4
private theorem endpoint_18_39_w6 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 6 2 195975724371081159 = some 195975724371081159 := by decide +kernel
private theorem endpoint_18_39_p8 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 8 195975724371081159 = some 195975724371081159 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 6 2 195975724371081159 195975724371081159 195975724371081159 endpoint_18_39_p6 endpoint_18_39_w6
private theorem endpoint_18_39_w8 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 8 2 195975724371081159 = some 195975724371081159 := by decide +kernel
private theorem endpoint_18_39_p10 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 10 195975724371081159 = some 195975724371081159 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 8 2 195975724371081159 195975724371081159 195975724371081159 endpoint_18_39_p8 endpoint_18_39_w8
private theorem endpoint_18_39_w10 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 10 2 195975724371081159 = some 195975724371081159 := by decide +kernel
private theorem endpoint_18_39_p12 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 12 195975724371081159 = some 195975724371081159 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 10 2 195975724371081159 195975724371081159 195975724371081159 endpoint_18_39_p10 endpoint_18_39_w10
private theorem endpoint_18_39_w12 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 12 2 195975724371081159 = some 195975724371081159 := by decide +kernel
private theorem endpoint_18_39_p14 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 14 195975724371081159 = some 195975724371081159 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 12 2 195975724371081159 195975724371081159 195975724371081159 endpoint_18_39_p12 endpoint_18_39_w12
private theorem endpoint_18_39_w14 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 14 2 195975724371081159 = some 195975724371081159 := by decide +kernel
private theorem endpoint_18_39_p16 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 16 195975724371081159 = some 195975724371081159 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 14 2 195975724371081159 195975724371081159 195975724371081159 endpoint_18_39_p14 endpoint_18_39_w14
private theorem endpoint_18_39_w16 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 16 1 195975724371081159 = some 195975724371081159 := by decide +kernel
private theorem endpoint_18_39_p17 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 17 195975724371081159 = some 195975724371081159 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 16 1 195975724371081159 195975724371081159 195975724371081159 endpoint_18_39_p16 endpoint_18_39_w16
def endpoint_18_39 : CertifiedEndpoint :=
  ⟨⟨18, 39, 2509⟩, 195975724371081159, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_39_flag endpoint_18_39_sources 17 195975724371081159 195975724371081159 rfl endpoint_18_39_base endpoint_18_39_p17) (by decide)⟩
private def endpoint_18_40_flag : Flag := ⟨18, 40, 2469⟩
private def endpoint_18_40_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_40_base : receiptBase endpoint_18_40_flag endpoint_18_40_sources = some 197132889101229410 := by decide +kernel
private theorem endpoint_18_40_w0 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 2 197132889101229410 = some 197140830135674536 := by decide +kernel
private theorem endpoint_18_40_w2 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 2 2 197140830135674536 = some 197140830135674536 := by decide +kernel
private theorem endpoint_18_40_p4 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 4 197132889101229410 = some 197140830135674536 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 2 2 197132889101229410 197140830135674536 197140830135674536 endpoint_18_40_w0 endpoint_18_40_w2
private theorem endpoint_18_40_w4 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 4 2 197140830135674536 = some 197140830135674536 := by decide +kernel
private theorem endpoint_18_40_p6 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 6 197132889101229410 = some 197140830135674536 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 4 2 197132889101229410 197140830135674536 197140830135674536 endpoint_18_40_p4 endpoint_18_40_w4
private theorem endpoint_18_40_w6 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 6 2 197140830135674536 = some 197140830135674536 := by decide +kernel
private theorem endpoint_18_40_p8 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 8 197132889101229410 = some 197140830135674536 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 6 2 197132889101229410 197140830135674536 197140830135674536 endpoint_18_40_p6 endpoint_18_40_w6
private theorem endpoint_18_40_w8 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 8 2 197140830135674536 = some 197140830135674536 := by decide +kernel
private theorem endpoint_18_40_p10 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 10 197132889101229410 = some 197140830135674536 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 8 2 197132889101229410 197140830135674536 197140830135674536 endpoint_18_40_p8 endpoint_18_40_w8
private theorem endpoint_18_40_w10 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 10 2 197140830135674536 = some 197140830135674536 := by decide +kernel
private theorem endpoint_18_40_p12 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 12 197132889101229410 = some 197140830135674536 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 10 2 197132889101229410 197140830135674536 197140830135674536 endpoint_18_40_p10 endpoint_18_40_w10
private theorem endpoint_18_40_w12 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 12 2 197140830135674536 = some 197140830135674536 := by decide +kernel
private theorem endpoint_18_40_p14 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 14 197132889101229410 = some 197140830135674536 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 12 2 197132889101229410 197140830135674536 197140830135674536 endpoint_18_40_p12 endpoint_18_40_w12
private theorem endpoint_18_40_w14 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 14 2 197140830135674536 = some 197140830135674536 := by decide +kernel
private theorem endpoint_18_40_p16 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 16 197132889101229410 = some 197140830135674536 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 14 2 197132889101229410 197140830135674536 197140830135674536 endpoint_18_40_p14 endpoint_18_40_w14
private theorem endpoint_18_40_w16 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 16 1 197140830135674536 = some 197140830135674536 := by decide +kernel
private theorem endpoint_18_40_p17 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 17 197132889101229410 = some 197140830135674536 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 16 1 197132889101229410 197140830135674536 197140830135674536 endpoint_18_40_p16 endpoint_18_40_w16
def endpoint_18_40 : CertifiedEndpoint :=
  ⟨⟨18, 40, 2469⟩, 197140830135674536, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_40_flag endpoint_18_40_sources 17 197132889101229410 197140830135674536 rfl endpoint_18_40_base endpoint_18_40_p17) (by decide)⟩
private def endpoint_18_41_flag : Flag := ⟨18, 41, 2427⟩
private def endpoint_18_41_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_41_base : receiptBase endpoint_18_41_flag endpoint_18_41_sources = some 197993083900228983 := by decide +kernel
private theorem endpoint_18_41_w0 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 2 197993083900228983 = some 201836951331973722 := by decide +kernel
private theorem endpoint_18_41_w2 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 2 2 201836951331973722 = some 201836951331973722 := by decide +kernel
private theorem endpoint_18_41_p4 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 4 197993083900228983 = some 201836951331973722 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 2 2 197993083900228983 201836951331973722 201836951331973722 endpoint_18_41_w0 endpoint_18_41_w2
private theorem endpoint_18_41_w4 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 4 2 201836951331973722 = some 201836951331973722 := by decide +kernel
private theorem endpoint_18_41_p6 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 6 197993083900228983 = some 201836951331973722 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 4 2 197993083900228983 201836951331973722 201836951331973722 endpoint_18_41_p4 endpoint_18_41_w4
private theorem endpoint_18_41_w6 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 6 2 201836951331973722 = some 201836951331973722 := by decide +kernel
private theorem endpoint_18_41_p8 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 8 197993083900228983 = some 201836951331973722 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 6 2 197993083900228983 201836951331973722 201836951331973722 endpoint_18_41_p6 endpoint_18_41_w6
private theorem endpoint_18_41_w8 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 8 2 201836951331973722 = some 201836951331973722 := by decide +kernel
private theorem endpoint_18_41_p10 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 10 197993083900228983 = some 201836951331973722 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 8 2 197993083900228983 201836951331973722 201836951331973722 endpoint_18_41_p8 endpoint_18_41_w8
private theorem endpoint_18_41_w10 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 10 2 201836951331973722 = some 201836951331973722 := by decide +kernel
private theorem endpoint_18_41_p12 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 12 197993083900228983 = some 201836951331973722 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 10 2 197993083900228983 201836951331973722 201836951331973722 endpoint_18_41_p10 endpoint_18_41_w10
private theorem endpoint_18_41_w12 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 12 2 201836951331973722 = some 201836951331973722 := by decide +kernel
private theorem endpoint_18_41_p14 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 14 197993083900228983 = some 201836951331973722 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 12 2 197993083900228983 201836951331973722 201836951331973722 endpoint_18_41_p12 endpoint_18_41_w12
private theorem endpoint_18_41_w14 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 14 2 201836951331973722 = some 201836951331973722 := by decide +kernel
private theorem endpoint_18_41_p16 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 16 197993083900228983 = some 201836951331973722 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 14 2 197993083900228983 201836951331973722 201836951331973722 endpoint_18_41_p14 endpoint_18_41_w14
private theorem endpoint_18_41_w16 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 16 1 201836951331973722 = some 201836951331973722 := by decide +kernel
private theorem endpoint_18_41_p17 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 17 197993083900228983 = some 201836951331973722 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 16 1 197993083900228983 201836951331973722 201836951331973722 endpoint_18_41_p16 endpoint_18_41_w16
def endpoint_18_41 : CertifiedEndpoint :=
  ⟨⟨18, 41, 2427⟩, 201836951331973722, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_41_flag endpoint_18_41_sources 17 197993083900228983 201836951331973722 rfl endpoint_18_41_base endpoint_18_41_p17) (by decide)⟩
private def endpoint_18_42_flag : Flag := ⟨18, 42, 2386⟩
private def endpoint_18_42_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_18_42_base : receiptBase endpoint_18_42_flag endpoint_18_42_sources = some 203743611195783765 := by decide +kernel
private theorem endpoint_18_42_w0 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 2 203743611195783765 = some 203743611195783765 := by decide +kernel
private theorem endpoint_18_42_w2 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 2 2 203743611195783765 = some 203743611195783765 := by decide +kernel
private theorem endpoint_18_42_p4 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 4 203743611195783765 = some 203743611195783765 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 2 2 203743611195783765 203743611195783765 203743611195783765 endpoint_18_42_w0 endpoint_18_42_w2
private theorem endpoint_18_42_w4 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 4 2 203743611195783765 = some 203743611195783765 := by decide +kernel
private theorem endpoint_18_42_p6 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 6 203743611195783765 = some 203743611195783765 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 4 2 203743611195783765 203743611195783765 203743611195783765 endpoint_18_42_p4 endpoint_18_42_w4
private theorem endpoint_18_42_w6 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 6 2 203743611195783765 = some 203743611195783765 := by decide +kernel
private theorem endpoint_18_42_p8 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 8 203743611195783765 = some 203743611195783765 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 6 2 203743611195783765 203743611195783765 203743611195783765 endpoint_18_42_p6 endpoint_18_42_w6
private theorem endpoint_18_42_w8 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 8 2 203743611195783765 = some 203743611195783765 := by decide +kernel
private theorem endpoint_18_42_p10 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 10 203743611195783765 = some 203743611195783765 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 8 2 203743611195783765 203743611195783765 203743611195783765 endpoint_18_42_p8 endpoint_18_42_w8
private theorem endpoint_18_42_w10 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 10 2 203743611195783765 = some 203743611195783765 := by decide +kernel
private theorem endpoint_18_42_p12 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 12 203743611195783765 = some 203743611195783765 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 10 2 203743611195783765 203743611195783765 203743611195783765 endpoint_18_42_p10 endpoint_18_42_w10
private theorem endpoint_18_42_w12 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 12 2 203743611195783765 = some 203743611195783765 := by decide +kernel
private theorem endpoint_18_42_p14 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 14 203743611195783765 = some 203743611195783765 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 12 2 203743611195783765 203743611195783765 203743611195783765 endpoint_18_42_p12 endpoint_18_42_w12
private theorem endpoint_18_42_w14 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 14 2 203743611195783765 = some 203743611195783765 := by decide +kernel
private theorem endpoint_18_42_p16 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 16 203743611195783765 = some 203743611195783765 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 14 2 203743611195783765 203743611195783765 203743611195783765 endpoint_18_42_p14 endpoint_18_42_w14
private theorem endpoint_18_42_w16 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 16 1 203743611195783765 = some 203743611195783765 := by decide +kernel
private theorem endpoint_18_42_p17 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 17 203743611195783765 = some 203743611195783765 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 16 1 203743611195783765 203743611195783765 203743611195783765 endpoint_18_42_p16 endpoint_18_42_w16
def endpoint_18_42 : CertifiedEndpoint :=
  ⟨⟨18, 42, 2386⟩, 203743611195783765, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_18_42_flag endpoint_18_42_sources 17 203743611195783765 203743611195783765 rfl endpoint_18_42_base endpoint_18_42_p17) (by decide)⟩
private def endpoint_18_43_flag : Flag := ⟨18, 43, 2343⟩
private def endpoint_18_43_sources : Sources := ⟨contact33, contact11, contact29⟩
private theorem endpoint_18_43_base : receiptBase endpoint_18_43_flag endpoint_18_43_sources = some 204745020199431389 := by decide +kernel
private theorem endpoint_18_43_w0 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 2 204745020199431389 = some 204745020199431389 := by decide +kernel
private theorem endpoint_18_43_w2 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 2 2 204745020199431389 = some 204745020199431389 := by decide +kernel
private theorem endpoint_18_43_p4 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 4 204745020199431389 = some 204745020199431389 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 2 2 204745020199431389 204745020199431389 204745020199431389 endpoint_18_43_w0 endpoint_18_43_w2
private theorem endpoint_18_43_w4 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 4 2 204745020199431389 = some 204745020199431389 := by decide +kernel
private theorem endpoint_18_43_p6 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 6 204745020199431389 = some 204745020199431389 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 4 2 204745020199431389 204745020199431389 204745020199431389 endpoint_18_43_p4 endpoint_18_43_w4
private theorem endpoint_18_43_w6 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 6 2 204745020199431389 = some 204745020199431389 := by decide +kernel
private theorem endpoint_18_43_p8 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 8 204745020199431389 = some 204745020199431389 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 6 2 204745020199431389 204745020199431389 204745020199431389 endpoint_18_43_p6 endpoint_18_43_w6
private theorem endpoint_18_43_w8 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 8 2 204745020199431389 = some 204745020199431389 := by decide +kernel
private theorem endpoint_18_43_p10 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 10 204745020199431389 = some 204745020199431389 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 8 2 204745020199431389 204745020199431389 204745020199431389 endpoint_18_43_p8 endpoint_18_43_w8
private theorem endpoint_18_43_w10 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 10 2 204745020199431389 = some 204745020199431389 := by decide +kernel
private theorem endpoint_18_43_p12 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 12 204745020199431389 = some 204745020199431389 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 10 2 204745020199431389 204745020199431389 204745020199431389 endpoint_18_43_p10 endpoint_18_43_w10
private theorem endpoint_18_43_w12 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 12 2 204745020199431389 = some 204745020199431389 := by decide +kernel
private theorem endpoint_18_43_p14 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 14 204745020199431389 = some 204745020199431389 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 12 2 204745020199431389 204745020199431389 204745020199431389 endpoint_18_43_p12 endpoint_18_43_w12
private theorem endpoint_18_43_w14 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 14 2 204745020199431389 = some 204745020199431389 := by decide +kernel
private theorem endpoint_18_43_p16 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 16 204745020199431389 = some 204745020199431389 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 14 2 204745020199431389 204745020199431389 204745020199431389 endpoint_18_43_p14 endpoint_18_43_w14
private theorem endpoint_18_43_w16 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 16 1 204745020199431389 = some 204745020199431389 := by decide +kernel
private theorem endpoint_18_43_p17 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 17 204745020199431389 = some 204745020199431389 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 16 1 204745020199431389 204745020199431389 204745020199431389 endpoint_18_43_p16 endpoint_18_43_w16
def endpoint_18_43 : CertifiedEndpoint :=
  ⟨⟨18, 43, 2343⟩, 204745020199431389, .terminal ⟨contact33, contact11, contact29⟩ (finish_receipt_window endpoint_18_43_flag endpoint_18_43_sources 17 204745020199431389 204745020199431389 rfl endpoint_18_43_base endpoint_18_43_p17) (by decide)⟩
private def endpoint_18_44_flag : Flag := ⟨18, 44, 2300⟩
private def endpoint_18_44_sources : Sources := ⟨contact33, contact11, contact29⟩
private theorem endpoint_18_44_base : receiptBase endpoint_18_44_flag endpoint_18_44_sources = some 205155423562139144 := by decide +kernel
private theorem endpoint_18_44_w0 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 2 205155423562139144 = some 205941568541634320 := by decide +kernel
private theorem endpoint_18_44_w2 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 2 2 205941568541634320 = some 205941568541634320 := by decide +kernel
private theorem endpoint_18_44_p4 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 4 205155423562139144 = some 205941568541634320 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 2 2 205155423562139144 205941568541634320 205941568541634320 endpoint_18_44_w0 endpoint_18_44_w2
private theorem endpoint_18_44_w4 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 4 2 205941568541634320 = some 205941568541634320 := by decide +kernel
private theorem endpoint_18_44_p6 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 6 205155423562139144 = some 205941568541634320 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 4 2 205155423562139144 205941568541634320 205941568541634320 endpoint_18_44_p4 endpoint_18_44_w4
private theorem endpoint_18_44_w6 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 6 2 205941568541634320 = some 205941568541634320 := by decide +kernel
private theorem endpoint_18_44_p8 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 8 205155423562139144 = some 205941568541634320 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 6 2 205155423562139144 205941568541634320 205941568541634320 endpoint_18_44_p6 endpoint_18_44_w6
private theorem endpoint_18_44_w8 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 8 2 205941568541634320 = some 205941568541634320 := by decide +kernel
private theorem endpoint_18_44_p10 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 10 205155423562139144 = some 205941568541634320 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 8 2 205155423562139144 205941568541634320 205941568541634320 endpoint_18_44_p8 endpoint_18_44_w8
private theorem endpoint_18_44_w10 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 10 2 205941568541634320 = some 205941568541634320 := by decide +kernel
private theorem endpoint_18_44_p12 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 12 205155423562139144 = some 205941568541634320 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 10 2 205155423562139144 205941568541634320 205941568541634320 endpoint_18_44_p10 endpoint_18_44_w10
private theorem endpoint_18_44_w12 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 12 2 205941568541634320 = some 205941568541634320 := by decide +kernel
private theorem endpoint_18_44_p14 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 14 205155423562139144 = some 205941568541634320 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 12 2 205155423562139144 205941568541634320 205941568541634320 endpoint_18_44_p12 endpoint_18_44_w12
private theorem endpoint_18_44_w14 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 14 2 205941568541634320 = some 205941568541634320 := by decide +kernel
private theorem endpoint_18_44_p16 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 16 205155423562139144 = some 205941568541634320 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 14 2 205155423562139144 205941568541634320 205941568541634320 endpoint_18_44_p14 endpoint_18_44_w14
private theorem endpoint_18_44_w16 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 16 1 205941568541634320 = some 205941568541634320 := by decide +kernel
private theorem endpoint_18_44_p17 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 17 205155423562139144 = some 205941568541634320 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 16 1 205155423562139144 205941568541634320 205941568541634320 endpoint_18_44_p16 endpoint_18_44_w16
def endpoint_18_44 : CertifiedEndpoint :=
  ⟨⟨18, 44, 2300⟩, 205941568541634320, .terminal ⟨contact33, contact11, contact29⟩ (finish_receipt_window endpoint_18_44_flag endpoint_18_44_sources 17 205155423562139144 205941568541634320 rfl endpoint_18_44_base endpoint_18_44_p17) (by decide)⟩
private def endpoint_18_45_flag : Flag := ⟨18, 45, 2255⟩
private def endpoint_18_45_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_18_45_base : receiptBase endpoint_18_45_flag endpoint_18_45_sources = some 205793870925014553 := by decide +kernel
private theorem endpoint_18_45_w0 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 2 205793870925014553 = some 205793870925014553 := by decide +kernel
private theorem endpoint_18_45_w2 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 2 2 205793870925014553 = some 205793870925014553 := by decide +kernel
private theorem endpoint_18_45_p4 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 4 205793870925014553 = some 205793870925014553 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 2 2 205793870925014553 205793870925014553 205793870925014553 endpoint_18_45_w0 endpoint_18_45_w2
private theorem endpoint_18_45_w4 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 4 2 205793870925014553 = some 205793870925014553 := by decide +kernel
private theorem endpoint_18_45_p6 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 6 205793870925014553 = some 205793870925014553 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 4 2 205793870925014553 205793870925014553 205793870925014553 endpoint_18_45_p4 endpoint_18_45_w4
private theorem endpoint_18_45_w6 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 6 2 205793870925014553 = some 205793870925014553 := by decide +kernel
private theorem endpoint_18_45_p8 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 8 205793870925014553 = some 205793870925014553 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 6 2 205793870925014553 205793870925014553 205793870925014553 endpoint_18_45_p6 endpoint_18_45_w6
private theorem endpoint_18_45_w8 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 8 2 205793870925014553 = some 205793870925014553 := by decide +kernel
private theorem endpoint_18_45_p10 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 10 205793870925014553 = some 205793870925014553 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 8 2 205793870925014553 205793870925014553 205793870925014553 endpoint_18_45_p8 endpoint_18_45_w8
private theorem endpoint_18_45_w10 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 10 2 205793870925014553 = some 205793870925014553 := by decide +kernel
private theorem endpoint_18_45_p12 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 12 205793870925014553 = some 205793870925014553 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 10 2 205793870925014553 205793870925014553 205793870925014553 endpoint_18_45_p10 endpoint_18_45_w10
private theorem endpoint_18_45_w12 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 12 2 205793870925014553 = some 205793870925014553 := by decide +kernel
private theorem endpoint_18_45_p14 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 14 205793870925014553 = some 205793870925014553 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 12 2 205793870925014553 205793870925014553 205793870925014553 endpoint_18_45_p12 endpoint_18_45_w12
private theorem endpoint_18_45_w14 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 14 2 205793870925014553 = some 205793870925014553 := by decide +kernel
private theorem endpoint_18_45_p16 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 16 205793870925014553 = some 205793870925014553 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 14 2 205793870925014553 205793870925014553 205793870925014553 endpoint_18_45_p14 endpoint_18_45_w14
private theorem endpoint_18_45_w16 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 16 1 205793870925014553 = some 205793870925014553 := by decide +kernel
private theorem endpoint_18_45_p17 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 17 205793870925014553 = some 205793870925014553 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 16 1 205793870925014553 205793870925014553 205793870925014553 endpoint_18_45_p16 endpoint_18_45_w16
def endpoint_18_45 : CertifiedEndpoint :=
  ⟨⟨18, 45, 2255⟩, 205793870925014553, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_18_45_flag endpoint_18_45_sources 17 205793870925014553 205793870925014553 rfl endpoint_18_45_base endpoint_18_45_p17) (by decide)⟩
private def endpoint_18_46_flag : Flag := ⟨18, 46, 2210⟩
private def endpoint_18_46_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_18_46_base : receiptBase endpoint_18_46_flag endpoint_18_46_sources = some 205691386128536523 := by decide +kernel
private theorem endpoint_18_46_w0 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 2 205691386128536523 = some 205691386128536523 := by decide +kernel
private theorem endpoint_18_46_w2 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 2 2 205691386128536523 = some 205691386128536523 := by decide +kernel
private theorem endpoint_18_46_p4 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 4 205691386128536523 = some 205691386128536523 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 2 2 205691386128536523 205691386128536523 205691386128536523 endpoint_18_46_w0 endpoint_18_46_w2
private theorem endpoint_18_46_w4 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 4 2 205691386128536523 = some 205691386128536523 := by decide +kernel
private theorem endpoint_18_46_p6 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 6 205691386128536523 = some 205691386128536523 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 4 2 205691386128536523 205691386128536523 205691386128536523 endpoint_18_46_p4 endpoint_18_46_w4
private theorem endpoint_18_46_w6 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 6 2 205691386128536523 = some 205691386128536523 := by decide +kernel
private theorem endpoint_18_46_p8 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 8 205691386128536523 = some 205691386128536523 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 6 2 205691386128536523 205691386128536523 205691386128536523 endpoint_18_46_p6 endpoint_18_46_w6
private theorem endpoint_18_46_w8 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 8 2 205691386128536523 = some 205691386128536523 := by decide +kernel
private theorem endpoint_18_46_p10 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 10 205691386128536523 = some 205691386128536523 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 8 2 205691386128536523 205691386128536523 205691386128536523 endpoint_18_46_p8 endpoint_18_46_w8
private theorem endpoint_18_46_w10 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 10 2 205691386128536523 = some 205691386128536523 := by decide +kernel
private theorem endpoint_18_46_p12 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 12 205691386128536523 = some 205691386128536523 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 10 2 205691386128536523 205691386128536523 205691386128536523 endpoint_18_46_p10 endpoint_18_46_w10
private theorem endpoint_18_46_w12 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 12 2 205691386128536523 = some 205691386128536523 := by decide +kernel
private theorem endpoint_18_46_p14 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 14 205691386128536523 = some 205691386128536523 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 12 2 205691386128536523 205691386128536523 205691386128536523 endpoint_18_46_p12 endpoint_18_46_w12
private theorem endpoint_18_46_w14 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 14 2 205691386128536523 = some 205691386128536523 := by decide +kernel
private theorem endpoint_18_46_p16 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 16 205691386128536523 = some 205691386128536523 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 14 2 205691386128536523 205691386128536523 205691386128536523 endpoint_18_46_p14 endpoint_18_46_w14
private theorem endpoint_18_46_w16 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 16 1 205691386128536523 = some 205691386128536523 := by decide +kernel
private theorem endpoint_18_46_p17 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 17 205691386128536523 = some 205691386128536523 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 16 1 205691386128536523 205691386128536523 205691386128536523 endpoint_18_46_p16 endpoint_18_46_w16
def endpoint_18_46 : CertifiedEndpoint :=
  ⟨⟨18, 46, 2210⟩, 205691386128536523, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_18_46_flag endpoint_18_46_sources 17 205691386128536523 205691386128536523 rfl endpoint_18_46_base endpoint_18_46_p17) (by decide)⟩
private def endpoint_18_47_flag : Flag := ⟨18, 47, 2164⟩
private def endpoint_18_47_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_18_47_base : receiptBase endpoint_18_47_flag endpoint_18_47_sources = some 205341915291191107 := by decide +kernel
private theorem endpoint_18_47_w0 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 2 205341915291191107 = some 205341915291191107 := by decide +kernel
private theorem endpoint_18_47_w2 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 2 2 205341915291191107 = some 205341915291191107 := by decide +kernel
private theorem endpoint_18_47_p4 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 4 205341915291191107 = some 205341915291191107 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 2 2 205341915291191107 205341915291191107 205341915291191107 endpoint_18_47_w0 endpoint_18_47_w2
private theorem endpoint_18_47_w4 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 4 2 205341915291191107 = some 205341915291191107 := by decide +kernel
private theorem endpoint_18_47_p6 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 6 205341915291191107 = some 205341915291191107 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 4 2 205341915291191107 205341915291191107 205341915291191107 endpoint_18_47_p4 endpoint_18_47_w4
private theorem endpoint_18_47_w6 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 6 2 205341915291191107 = some 205341915291191107 := by decide +kernel
private theorem endpoint_18_47_p8 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 8 205341915291191107 = some 205341915291191107 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 6 2 205341915291191107 205341915291191107 205341915291191107 endpoint_18_47_p6 endpoint_18_47_w6
private theorem endpoint_18_47_w8 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 8 2 205341915291191107 = some 205341915291191107 := by decide +kernel
private theorem endpoint_18_47_p10 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 10 205341915291191107 = some 205341915291191107 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 8 2 205341915291191107 205341915291191107 205341915291191107 endpoint_18_47_p8 endpoint_18_47_w8
private theorem endpoint_18_47_w10 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 10 2 205341915291191107 = some 205341915291191107 := by decide +kernel
private theorem endpoint_18_47_p12 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 12 205341915291191107 = some 205341915291191107 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 10 2 205341915291191107 205341915291191107 205341915291191107 endpoint_18_47_p10 endpoint_18_47_w10
private theorem endpoint_18_47_w12 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 12 2 205341915291191107 = some 205341915291191107 := by decide +kernel
private theorem endpoint_18_47_p14 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 14 205341915291191107 = some 205341915291191107 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 12 2 205341915291191107 205341915291191107 205341915291191107 endpoint_18_47_p12 endpoint_18_47_w12
private theorem endpoint_18_47_w14 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 14 2 205341915291191107 = some 205341915291191107 := by decide +kernel
private theorem endpoint_18_47_p16 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 16 205341915291191107 = some 205341915291191107 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 14 2 205341915291191107 205341915291191107 205341915291191107 endpoint_18_47_p14 endpoint_18_47_w14
private theorem endpoint_18_47_w16 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 16 1 205341915291191107 = some 205341915291191107 := by decide +kernel
private theorem endpoint_18_47_p17 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 17 205341915291191107 = some 205341915291191107 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 16 1 205341915291191107 205341915291191107 205341915291191107 endpoint_18_47_p16 endpoint_18_47_w16
def endpoint_18_47 : CertifiedEndpoint :=
  ⟨⟨18, 47, 2164⟩, 205341915291191107, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_18_47_flag endpoint_18_47_sources 17 205341915291191107 205341915291191107 rfl endpoint_18_47_base endpoint_18_47_p17) (by decide)⟩
private def endpoint_18_48_flag : Flag := ⟨18, 48, 2118⟩
private def endpoint_18_48_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_18_48_base : receiptBase endpoint_18_48_flag endpoint_18_48_sources = some 205611035384639050 := by decide +kernel
private theorem endpoint_18_48_w0 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 2 205611035384639050 = some 205611035384639050 := by decide +kernel
private theorem endpoint_18_48_w2 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 2 2 205611035384639050 = some 205611035384639050 := by decide +kernel
private theorem endpoint_18_48_p4 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 4 205611035384639050 = some 205611035384639050 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 2 2 205611035384639050 205611035384639050 205611035384639050 endpoint_18_48_w0 endpoint_18_48_w2
private theorem endpoint_18_48_w4 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 4 2 205611035384639050 = some 205611035384639050 := by decide +kernel
private theorem endpoint_18_48_p6 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 6 205611035384639050 = some 205611035384639050 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 4 2 205611035384639050 205611035384639050 205611035384639050 endpoint_18_48_p4 endpoint_18_48_w4
private theorem endpoint_18_48_w6 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 6 2 205611035384639050 = some 205611035384639050 := by decide +kernel
private theorem endpoint_18_48_p8 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 8 205611035384639050 = some 205611035384639050 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 6 2 205611035384639050 205611035384639050 205611035384639050 endpoint_18_48_p6 endpoint_18_48_w6
private theorem endpoint_18_48_w8 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 8 2 205611035384639050 = some 205611035384639050 := by decide +kernel
private theorem endpoint_18_48_p10 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 10 205611035384639050 = some 205611035384639050 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 8 2 205611035384639050 205611035384639050 205611035384639050 endpoint_18_48_p8 endpoint_18_48_w8
private theorem endpoint_18_48_w10 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 10 2 205611035384639050 = some 205611035384639050 := by decide +kernel
private theorem endpoint_18_48_p12 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 12 205611035384639050 = some 205611035384639050 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 10 2 205611035384639050 205611035384639050 205611035384639050 endpoint_18_48_p10 endpoint_18_48_w10
private theorem endpoint_18_48_w12 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 12 2 205611035384639050 = some 205611035384639050 := by decide +kernel
private theorem endpoint_18_48_p14 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 14 205611035384639050 = some 205611035384639050 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 12 2 205611035384639050 205611035384639050 205611035384639050 endpoint_18_48_p12 endpoint_18_48_w12
private theorem endpoint_18_48_w14 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 14 2 205611035384639050 = some 205611035384639050 := by decide +kernel
private theorem endpoint_18_48_p16 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 16 205611035384639050 = some 205611035384639050 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 14 2 205611035384639050 205611035384639050 205611035384639050 endpoint_18_48_p14 endpoint_18_48_w14
private theorem endpoint_18_48_w16 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 16 1 205611035384639050 = some 205611035384639050 := by decide +kernel
private theorem endpoint_18_48_p17 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 17 205611035384639050 = some 205611035384639050 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 16 1 205611035384639050 205611035384639050 205611035384639050 endpoint_18_48_p16 endpoint_18_48_w16
def endpoint_18_48 : CertifiedEndpoint :=
  ⟨⟨18, 48, 2118⟩, 205611035384639050, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_18_48_flag endpoint_18_48_sources 17 205611035384639050 205611035384639050 rfl endpoint_18_48_base endpoint_18_48_p17) (by decide)⟩
private def endpoint_18_49_flag : Flag := ⟨18, 49, 2070⟩
private def endpoint_18_49_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_18_49_base : receiptBase endpoint_18_49_flag endpoint_18_49_sources = some 204745263305370358 := by decide +kernel
private theorem endpoint_18_49_w0 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 2 204745263305370358 = some 204745263305370358 := by decide +kernel
private theorem endpoint_18_49_w2 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 2 2 204745263305370358 = some 204745263305370358 := by decide +kernel
private theorem endpoint_18_49_p4 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 4 204745263305370358 = some 204745263305370358 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 2 2 204745263305370358 204745263305370358 204745263305370358 endpoint_18_49_w0 endpoint_18_49_w2
private theorem endpoint_18_49_w4 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 4 2 204745263305370358 = some 204745263305370358 := by decide +kernel
private theorem endpoint_18_49_p6 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 6 204745263305370358 = some 204745263305370358 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 4 2 204745263305370358 204745263305370358 204745263305370358 endpoint_18_49_p4 endpoint_18_49_w4
private theorem endpoint_18_49_w6 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 6 2 204745263305370358 = some 204745263305370358 := by decide +kernel
private theorem endpoint_18_49_p8 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 8 204745263305370358 = some 204745263305370358 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 6 2 204745263305370358 204745263305370358 204745263305370358 endpoint_18_49_p6 endpoint_18_49_w6
private theorem endpoint_18_49_w8 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 8 2 204745263305370358 = some 204745263305370358 := by decide +kernel
private theorem endpoint_18_49_p10 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 10 204745263305370358 = some 204745263305370358 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 8 2 204745263305370358 204745263305370358 204745263305370358 endpoint_18_49_p8 endpoint_18_49_w8
private theorem endpoint_18_49_w10 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 10 2 204745263305370358 = some 204745263305370358 := by decide +kernel
private theorem endpoint_18_49_p12 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 12 204745263305370358 = some 204745263305370358 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 10 2 204745263305370358 204745263305370358 204745263305370358 endpoint_18_49_p10 endpoint_18_49_w10
private theorem endpoint_18_49_w12 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 12 2 204745263305370358 = some 204745263305370358 := by decide +kernel
private theorem endpoint_18_49_p14 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 14 204745263305370358 = some 204745263305370358 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 12 2 204745263305370358 204745263305370358 204745263305370358 endpoint_18_49_p12 endpoint_18_49_w12
private theorem endpoint_18_49_w14 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 14 2 204745263305370358 = some 204745263305370358 := by decide +kernel
private theorem endpoint_18_49_p16 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 16 204745263305370358 = some 204745263305370358 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 14 2 204745263305370358 204745263305370358 204745263305370358 endpoint_18_49_p14 endpoint_18_49_w14
private theorem endpoint_18_49_w16 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 16 1 204745263305370358 = some 204745263305370358 := by decide +kernel
private theorem endpoint_18_49_p17 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 17 204745263305370358 = some 204745263305370358 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 16 1 204745263305370358 204745263305370358 204745263305370358 endpoint_18_49_p16 endpoint_18_49_w16
def endpoint_18_49 : CertifiedEndpoint :=
  ⟨⟨18, 49, 2070⟩, 204745263305370358, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_18_49_flag endpoint_18_49_sources 17 204745263305370358 204745263305370358 rfl endpoint_18_49_base endpoint_18_49_p17) (by decide)⟩
private def endpoint_18_50_flag : Flag := ⟨18, 50, 2021⟩
private def endpoint_18_50_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_18_50_base : receiptBase endpoint_18_50_flag endpoint_18_50_sources = some 203614168517138664 := by decide +kernel
private theorem endpoint_18_50_w0 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 2 203614168517138664 = some 206674521594234246 := by decide +kernel
private theorem endpoint_18_50_w2 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 2 2 206674521594234246 = some 206674521594234246 := by decide +kernel
private theorem endpoint_18_50_p4 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 4 203614168517138664 = some 206674521594234246 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 2 2 203614168517138664 206674521594234246 206674521594234246 endpoint_18_50_w0 endpoint_18_50_w2
private theorem endpoint_18_50_w4 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 4 2 206674521594234246 = some 206674521594234246 := by decide +kernel
private theorem endpoint_18_50_p6 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 6 203614168517138664 = some 206674521594234246 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 4 2 203614168517138664 206674521594234246 206674521594234246 endpoint_18_50_p4 endpoint_18_50_w4
private theorem endpoint_18_50_w6 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 6 2 206674521594234246 = some 206674521594234246 := by decide +kernel
private theorem endpoint_18_50_p8 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 8 203614168517138664 = some 206674521594234246 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 6 2 203614168517138664 206674521594234246 206674521594234246 endpoint_18_50_p6 endpoint_18_50_w6
private theorem endpoint_18_50_w8 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 8 2 206674521594234246 = some 206674521594234246 := by decide +kernel
private theorem endpoint_18_50_p10 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 10 203614168517138664 = some 206674521594234246 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 8 2 203614168517138664 206674521594234246 206674521594234246 endpoint_18_50_p8 endpoint_18_50_w8
private theorem endpoint_18_50_w10 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 10 2 206674521594234246 = some 206674521594234246 := by decide +kernel
private theorem endpoint_18_50_p12 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 12 203614168517138664 = some 206674521594234246 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 10 2 203614168517138664 206674521594234246 206674521594234246 endpoint_18_50_p10 endpoint_18_50_w10
private theorem endpoint_18_50_w12 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 12 2 206674521594234246 = some 206674521594234246 := by decide +kernel
private theorem endpoint_18_50_p14 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 14 203614168517138664 = some 206674521594234246 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 12 2 203614168517138664 206674521594234246 206674521594234246 endpoint_18_50_p12 endpoint_18_50_w12
private theorem endpoint_18_50_w14 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 14 2 206674521594234246 = some 206674521594234246 := by decide +kernel
private theorem endpoint_18_50_p16 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 16 203614168517138664 = some 206674521594234246 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 14 2 203614168517138664 206674521594234246 206674521594234246 endpoint_18_50_p14 endpoint_18_50_w14
private theorem endpoint_18_50_w16 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 16 1 206674521594234246 = some 206674521594234246 := by decide +kernel
private theorem endpoint_18_50_p17 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 17 203614168517138664 = some 206674521594234246 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 16 1 203614168517138664 206674521594234246 206674521594234246 endpoint_18_50_p16 endpoint_18_50_w16
def endpoint_18_50 : CertifiedEndpoint :=
  ⟨⟨18, 50, 2021⟩, 206674521594234246, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_18_50_flag endpoint_18_50_sources 17 203614168517138664 206674521594234246 rfl endpoint_18_50_base endpoint_18_50_p17) (by decide)⟩
private def endpoint_18_51_flag : Flag := ⟨18, 51, 1971⟩
private def endpoint_18_51_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_18_51_base : receiptBase endpoint_18_51_flag endpoint_18_51_sources = some 202233043070833186 := by decide +kernel
private theorem endpoint_18_51_w0 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 2 202233043070833186 = some 208900837375491384 := by decide +kernel
private theorem endpoint_18_51_w2 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 2 2 208900837375491384 = some 208900837375491384 := by decide +kernel
private theorem endpoint_18_51_p4 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 4 202233043070833186 = some 208900837375491384 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 2 2 202233043070833186 208900837375491384 208900837375491384 endpoint_18_51_w0 endpoint_18_51_w2
private theorem endpoint_18_51_w4 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 4 2 208900837375491384 = some 208900837375491384 := by decide +kernel
private theorem endpoint_18_51_p6 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 6 202233043070833186 = some 208900837375491384 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 4 2 202233043070833186 208900837375491384 208900837375491384 endpoint_18_51_p4 endpoint_18_51_w4
private theorem endpoint_18_51_w6 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 6 2 208900837375491384 = some 208900837375491384 := by decide +kernel
private theorem endpoint_18_51_p8 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 8 202233043070833186 = some 208900837375491384 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 6 2 202233043070833186 208900837375491384 208900837375491384 endpoint_18_51_p6 endpoint_18_51_w6
private theorem endpoint_18_51_w8 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 8 2 208900837375491384 = some 208900837375491384 := by decide +kernel
private theorem endpoint_18_51_p10 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 10 202233043070833186 = some 208900837375491384 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 8 2 202233043070833186 208900837375491384 208900837375491384 endpoint_18_51_p8 endpoint_18_51_w8
private theorem endpoint_18_51_w10 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 10 2 208900837375491384 = some 208900837375491384 := by decide +kernel
private theorem endpoint_18_51_p12 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 12 202233043070833186 = some 208900837375491384 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 10 2 202233043070833186 208900837375491384 208900837375491384 endpoint_18_51_p10 endpoint_18_51_w10
private theorem endpoint_18_51_w12 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 12 2 208900837375491384 = some 208900837375491384 := by decide +kernel
private theorem endpoint_18_51_p14 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 14 202233043070833186 = some 208900837375491384 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 12 2 202233043070833186 208900837375491384 208900837375491384 endpoint_18_51_p12 endpoint_18_51_w12
private theorem endpoint_18_51_w14 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 14 2 208900837375491384 = some 208900837375491384 := by decide +kernel
private theorem endpoint_18_51_p16 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 16 202233043070833186 = some 208900837375491384 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 14 2 202233043070833186 208900837375491384 208900837375491384 endpoint_18_51_p14 endpoint_18_51_w14
private theorem endpoint_18_51_w16 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 16 1 208900837375491384 = some 208900837375491384 := by decide +kernel
private theorem endpoint_18_51_p17 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 17 202233043070833186 = some 208900837375491384 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 16 1 202233043070833186 208900837375491384 208900837375491384 endpoint_18_51_p16 endpoint_18_51_w16
def endpoint_18_51 : CertifiedEndpoint :=
  ⟨⟨18, 51, 1971⟩, 208900837375491384, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_18_51_flag endpoint_18_51_sources 17 202233043070833186 208900837375491384 rfl endpoint_18_51_base endpoint_18_51_p17) (by decide)⟩
private def endpoint_18_52_flag : Flag := ⟨18, 52, 1921⟩
private def endpoint_18_52_sources : Sources := ⟨contact29, contact16, contact12⟩
private theorem endpoint_18_52_base : receiptBase endpoint_18_52_flag endpoint_18_52_sources = some 201121930137019060 := by decide +kernel
private theorem endpoint_18_52_w0 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 2 201121930137019060 = some 209774754476585588 := by decide +kernel
private theorem endpoint_18_52_w2 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 2 2 209774754476585588 = some 209774754476585588 := by decide +kernel
private theorem endpoint_18_52_p4 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 4 201121930137019060 = some 209774754476585588 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 2 2 201121930137019060 209774754476585588 209774754476585588 endpoint_18_52_w0 endpoint_18_52_w2
private theorem endpoint_18_52_w4 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 4 2 209774754476585588 = some 209774754476585588 := by decide +kernel
private theorem endpoint_18_52_p6 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 6 201121930137019060 = some 209774754476585588 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 4 2 201121930137019060 209774754476585588 209774754476585588 endpoint_18_52_p4 endpoint_18_52_w4
private theorem endpoint_18_52_w6 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 6 2 209774754476585588 = some 209774754476585588 := by decide +kernel
private theorem endpoint_18_52_p8 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 8 201121930137019060 = some 209774754476585588 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 6 2 201121930137019060 209774754476585588 209774754476585588 endpoint_18_52_p6 endpoint_18_52_w6
private theorem endpoint_18_52_w8 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 8 2 209774754476585588 = some 209774754476585588 := by decide +kernel
private theorem endpoint_18_52_p10 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 10 201121930137019060 = some 209774754476585588 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 8 2 201121930137019060 209774754476585588 209774754476585588 endpoint_18_52_p8 endpoint_18_52_w8
private theorem endpoint_18_52_w10 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 10 2 209774754476585588 = some 209774754476585588 := by decide +kernel
private theorem endpoint_18_52_p12 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 12 201121930137019060 = some 209774754476585588 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 10 2 201121930137019060 209774754476585588 209774754476585588 endpoint_18_52_p10 endpoint_18_52_w10
private theorem endpoint_18_52_w12 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 12 2 209774754476585588 = some 209774754476585588 := by decide +kernel
private theorem endpoint_18_52_p14 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 14 201121930137019060 = some 209774754476585588 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 12 2 201121930137019060 209774754476585588 209774754476585588 endpoint_18_52_p12 endpoint_18_52_w12
private theorem endpoint_18_52_w14 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 14 2 209774754476585588 = some 209774754476585588 := by decide +kernel
private theorem endpoint_18_52_p16 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 16 201121930137019060 = some 209774754476585588 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 14 2 201121930137019060 209774754476585588 209774754476585588 endpoint_18_52_p14 endpoint_18_52_w14
private theorem endpoint_18_52_w16 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 16 1 209774754476585588 = some 209774754476585588 := by decide +kernel
private theorem endpoint_18_52_p17 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 17 201121930137019060 = some 209774754476585588 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 16 1 201121930137019060 209774754476585588 209774754476585588 endpoint_18_52_p16 endpoint_18_52_w16
def endpoint_18_52 : CertifiedEndpoint :=
  ⟨⟨18, 52, 1921⟩, 209774754476585588, .terminal ⟨contact29, contact16, contact12⟩ (finish_receipt_window endpoint_18_52_flag endpoint_18_52_sources 17 201121930137019060 209774754476585588 rfl endpoint_18_52_base endpoint_18_52_p17) (by decide)⟩
private def endpoint_18_53_flag : Flag := ⟨18, 53, 1869⟩
private def endpoint_18_53_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_18_53_base : receiptBase endpoint_18_53_flag endpoint_18_53_sources = some 200759798682834844 := by decide +kernel
private theorem endpoint_18_53_w0 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 2 200759798682834844 = some 200759798682834844 := by decide +kernel
private theorem endpoint_18_53_w2 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 2 2 200759798682834844 = some 200759798682834844 := by decide +kernel
private theorem endpoint_18_53_p4 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 4 200759798682834844 = some 200759798682834844 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 2 2 200759798682834844 200759798682834844 200759798682834844 endpoint_18_53_w0 endpoint_18_53_w2
private theorem endpoint_18_53_w4 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 4 2 200759798682834844 = some 200759798682834844 := by decide +kernel
private theorem endpoint_18_53_p6 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 6 200759798682834844 = some 200759798682834844 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 4 2 200759798682834844 200759798682834844 200759798682834844 endpoint_18_53_p4 endpoint_18_53_w4
private theorem endpoint_18_53_w6 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 6 2 200759798682834844 = some 200759798682834844 := by decide +kernel
private theorem endpoint_18_53_p8 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 8 200759798682834844 = some 200759798682834844 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 6 2 200759798682834844 200759798682834844 200759798682834844 endpoint_18_53_p6 endpoint_18_53_w6
private theorem endpoint_18_53_w8 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 8 2 200759798682834844 = some 200759798682834844 := by decide +kernel
private theorem endpoint_18_53_p10 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 10 200759798682834844 = some 200759798682834844 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 8 2 200759798682834844 200759798682834844 200759798682834844 endpoint_18_53_p8 endpoint_18_53_w8
private theorem endpoint_18_53_w10 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 10 2 200759798682834844 = some 200759798682834844 := by decide +kernel
private theorem endpoint_18_53_p12 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 12 200759798682834844 = some 200759798682834844 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 10 2 200759798682834844 200759798682834844 200759798682834844 endpoint_18_53_p10 endpoint_18_53_w10
private theorem endpoint_18_53_w12 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 12 2 200759798682834844 = some 200759798682834844 := by decide +kernel
private theorem endpoint_18_53_p14 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 14 200759798682834844 = some 200759798682834844 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 12 2 200759798682834844 200759798682834844 200759798682834844 endpoint_18_53_p12 endpoint_18_53_w12
private theorem endpoint_18_53_w14 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 14 2 200759798682834844 = some 200759798682834844 := by decide +kernel
private theorem endpoint_18_53_p16 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 16 200759798682834844 = some 200759798682834844 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 14 2 200759798682834844 200759798682834844 200759798682834844 endpoint_18_53_p14 endpoint_18_53_w14
private theorem endpoint_18_53_w16 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 16 1 200759798682834844 = some 200759798682834844 := by decide +kernel
private theorem endpoint_18_53_p17 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 17 200759798682834844 = some 200759798682834844 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 16 1 200759798682834844 200759798682834844 200759798682834844 endpoint_18_53_p16 endpoint_18_53_w16
def endpoint_18_53 : CertifiedEndpoint :=
  ⟨⟨18, 53, 1869⟩, 200759798682834844, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_18_53_flag endpoint_18_53_sources 17 200759798682834844 200759798682834844 rfl endpoint_18_53_base endpoint_18_53_p17) (by decide)⟩
private def endpoint_18_54_flag : Flag := ⟨18, 54, 1816⟩
private def endpoint_18_54_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_54_base : receiptBase endpoint_18_54_flag endpoint_18_54_sources = some 200440126950314369 := by decide +kernel
private theorem endpoint_18_54_w0 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 2 200440126950314369 = some 200440126950314369 := by decide +kernel
private theorem endpoint_18_54_w2 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 2 2 200440126950314369 = some 200440126950314369 := by decide +kernel
private theorem endpoint_18_54_p4 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 4 200440126950314369 = some 200440126950314369 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 2 2 200440126950314369 200440126950314369 200440126950314369 endpoint_18_54_w0 endpoint_18_54_w2
private theorem endpoint_18_54_w4 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 4 2 200440126950314369 = some 200440126950314369 := by decide +kernel
private theorem endpoint_18_54_p6 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 6 200440126950314369 = some 200440126950314369 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 4 2 200440126950314369 200440126950314369 200440126950314369 endpoint_18_54_p4 endpoint_18_54_w4
private theorem endpoint_18_54_w6 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 6 2 200440126950314369 = some 200440126950314369 := by decide +kernel
private theorem endpoint_18_54_p8 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 8 200440126950314369 = some 200440126950314369 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 6 2 200440126950314369 200440126950314369 200440126950314369 endpoint_18_54_p6 endpoint_18_54_w6
private theorem endpoint_18_54_w8 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 8 2 200440126950314369 = some 200440126950314369 := by decide +kernel
private theorem endpoint_18_54_p10 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 10 200440126950314369 = some 200440126950314369 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 8 2 200440126950314369 200440126950314369 200440126950314369 endpoint_18_54_p8 endpoint_18_54_w8
private theorem endpoint_18_54_w10 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 10 2 200440126950314369 = some 200440126950314369 := by decide +kernel
private theorem endpoint_18_54_p12 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 12 200440126950314369 = some 200440126950314369 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 10 2 200440126950314369 200440126950314369 200440126950314369 endpoint_18_54_p10 endpoint_18_54_w10
private theorem endpoint_18_54_w12 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 12 2 200440126950314369 = some 200440126950314369 := by decide +kernel
private theorem endpoint_18_54_p14 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 14 200440126950314369 = some 200440126950314369 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 12 2 200440126950314369 200440126950314369 200440126950314369 endpoint_18_54_p12 endpoint_18_54_w12
private theorem endpoint_18_54_w14 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 14 2 200440126950314369 = some 200440126950314369 := by decide +kernel
private theorem endpoint_18_54_p16 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 16 200440126950314369 = some 200440126950314369 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 14 2 200440126950314369 200440126950314369 200440126950314369 endpoint_18_54_p14 endpoint_18_54_w14
private theorem endpoint_18_54_w16 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 16 1 200440126950314369 = some 200440126950314369 := by decide +kernel
private theorem endpoint_18_54_p17 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 17 200440126950314369 = some 200440126950314369 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 16 1 200440126950314369 200440126950314369 200440126950314369 endpoint_18_54_p16 endpoint_18_54_w16
def endpoint_18_54 : CertifiedEndpoint :=
  ⟨⟨18, 54, 1816⟩, 200440126950314369, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_54_flag endpoint_18_54_sources 17 200440126950314369 200440126950314369 rfl endpoint_18_54_base endpoint_18_54_p17) (by decide)⟩
private def endpoint_18_55_flag : Flag := ⟨18, 55, 1762⟩
private def endpoint_18_55_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_55_base : receiptBase endpoint_18_55_flag endpoint_18_55_sources = some 197685996778341354 := by decide +kernel
private theorem endpoint_18_55_w0 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 2 197685996778341354 = some 197685996778341354 := by decide +kernel
private theorem endpoint_18_55_w2 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 2 2 197685996778341354 = some 197685996778341354 := by decide +kernel
private theorem endpoint_18_55_p4 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 4 197685996778341354 = some 197685996778341354 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 2 2 197685996778341354 197685996778341354 197685996778341354 endpoint_18_55_w0 endpoint_18_55_w2
private theorem endpoint_18_55_w4 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 4 2 197685996778341354 = some 197685996778341354 := by decide +kernel
private theorem endpoint_18_55_p6 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 6 197685996778341354 = some 197685996778341354 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 4 2 197685996778341354 197685996778341354 197685996778341354 endpoint_18_55_p4 endpoint_18_55_w4
private theorem endpoint_18_55_w6 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 6 2 197685996778341354 = some 197685996778341354 := by decide +kernel
private theorem endpoint_18_55_p8 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 8 197685996778341354 = some 197685996778341354 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 6 2 197685996778341354 197685996778341354 197685996778341354 endpoint_18_55_p6 endpoint_18_55_w6
private theorem endpoint_18_55_w8 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 8 2 197685996778341354 = some 197685996778341354 := by decide +kernel
private theorem endpoint_18_55_p10 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 10 197685996778341354 = some 197685996778341354 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 8 2 197685996778341354 197685996778341354 197685996778341354 endpoint_18_55_p8 endpoint_18_55_w8
private theorem endpoint_18_55_w10 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 10 2 197685996778341354 = some 197685996778341354 := by decide +kernel
private theorem endpoint_18_55_p12 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 12 197685996778341354 = some 197685996778341354 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 10 2 197685996778341354 197685996778341354 197685996778341354 endpoint_18_55_p10 endpoint_18_55_w10
private theorem endpoint_18_55_w12 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 12 2 197685996778341354 = some 197685996778341354 := by decide +kernel
private theorem endpoint_18_55_p14 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 14 197685996778341354 = some 197685996778341354 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 12 2 197685996778341354 197685996778341354 197685996778341354 endpoint_18_55_p12 endpoint_18_55_w12
private theorem endpoint_18_55_w14 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 14 2 197685996778341354 = some 197685996778341354 := by decide +kernel
private theorem endpoint_18_55_p16 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 16 197685996778341354 = some 197685996778341354 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 14 2 197685996778341354 197685996778341354 197685996778341354 endpoint_18_55_p14 endpoint_18_55_w14
private theorem endpoint_18_55_w16 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 16 1 197685996778341354 = some 197685996778341354 := by decide +kernel
private theorem endpoint_18_55_p17 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 17 197685996778341354 = some 197685996778341354 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 16 1 197685996778341354 197685996778341354 197685996778341354 endpoint_18_55_p16 endpoint_18_55_w16
def endpoint_18_55 : CertifiedEndpoint :=
  ⟨⟨18, 55, 1762⟩, 197685996778341354, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_55_flag endpoint_18_55_sources 17 197685996778341354 197685996778341354 rfl endpoint_18_55_base endpoint_18_55_p17) (by decide)⟩
private def endpoint_18_56_flag : Flag := ⟨18, 56, 1708⟩
private def endpoint_18_56_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_18_56_base : receiptBase endpoint_18_56_flag endpoint_18_56_sources = some 193074448150834329 := by decide +kernel
private theorem endpoint_18_56_w0 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 2 193074448150834329 = some 201164669552152104 := by decide +kernel
private theorem endpoint_18_56_w2 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 2 2 201164669552152104 = some 201164669552152104 := by decide +kernel
private theorem endpoint_18_56_p4 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 4 193074448150834329 = some 201164669552152104 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 2 2 193074448150834329 201164669552152104 201164669552152104 endpoint_18_56_w0 endpoint_18_56_w2
private theorem endpoint_18_56_w4 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 4 2 201164669552152104 = some 201164669552152104 := by decide +kernel
private theorem endpoint_18_56_p6 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 6 193074448150834329 = some 201164669552152104 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 4 2 193074448150834329 201164669552152104 201164669552152104 endpoint_18_56_p4 endpoint_18_56_w4
private theorem endpoint_18_56_w6 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 6 2 201164669552152104 = some 201164669552152104 := by decide +kernel
private theorem endpoint_18_56_p8 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 8 193074448150834329 = some 201164669552152104 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 6 2 193074448150834329 201164669552152104 201164669552152104 endpoint_18_56_p6 endpoint_18_56_w6
private theorem endpoint_18_56_w8 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 8 2 201164669552152104 = some 201164669552152104 := by decide +kernel
private theorem endpoint_18_56_p10 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 10 193074448150834329 = some 201164669552152104 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 8 2 193074448150834329 201164669552152104 201164669552152104 endpoint_18_56_p8 endpoint_18_56_w8
private theorem endpoint_18_56_w10 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 10 2 201164669552152104 = some 201164669552152104 := by decide +kernel
private theorem endpoint_18_56_p12 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 12 193074448150834329 = some 201164669552152104 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 10 2 193074448150834329 201164669552152104 201164669552152104 endpoint_18_56_p10 endpoint_18_56_w10
private theorem endpoint_18_56_w12 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 12 2 201164669552152104 = some 201164669552152104 := by decide +kernel
private theorem endpoint_18_56_p14 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 14 193074448150834329 = some 201164669552152104 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 12 2 193074448150834329 201164669552152104 201164669552152104 endpoint_18_56_p12 endpoint_18_56_w12
private theorem endpoint_18_56_w14 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 14 2 201164669552152104 = some 201164669552152104 := by decide +kernel
private theorem endpoint_18_56_p16 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 16 193074448150834329 = some 201164669552152104 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 14 2 193074448150834329 201164669552152104 201164669552152104 endpoint_18_56_p14 endpoint_18_56_w14
private theorem endpoint_18_56_w16 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 16 1 201164669552152104 = some 201164669552152104 := by decide +kernel
private theorem endpoint_18_56_p17 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 17 193074448150834329 = some 201164669552152104 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 16 1 193074448150834329 201164669552152104 201164669552152104 endpoint_18_56_p16 endpoint_18_56_w16
def endpoint_18_56 : CertifiedEndpoint :=
  ⟨⟨18, 56, 1708⟩, 201164669552152104, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_18_56_flag endpoint_18_56_sources 17 193074448150834329 201164669552152104 rfl endpoint_18_56_base endpoint_18_56_p17) (by decide)⟩
private def endpoint_18_57_flag : Flag := ⟨18, 57, 1651⟩
private def endpoint_18_57_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_18_57_base : receiptBase endpoint_18_57_flag endpoint_18_57_sources = some 189638781769505043 := by decide +kernel
private theorem endpoint_18_57_w0 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 2 189638781769505043 = some 201705460473313458 := by decide +kernel
private theorem endpoint_18_57_w2 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 2 2 201705460473313458 = some 201705460473313458 := by decide +kernel
private theorem endpoint_18_57_p4 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 4 189638781769505043 = some 201705460473313458 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 2 2 189638781769505043 201705460473313458 201705460473313458 endpoint_18_57_w0 endpoint_18_57_w2
private theorem endpoint_18_57_w4 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 4 2 201705460473313458 = some 201705460473313458 := by decide +kernel
private theorem endpoint_18_57_p6 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 6 189638781769505043 = some 201705460473313458 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 4 2 189638781769505043 201705460473313458 201705460473313458 endpoint_18_57_p4 endpoint_18_57_w4
private theorem endpoint_18_57_w6 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 6 2 201705460473313458 = some 201705460473313458 := by decide +kernel
private theorem endpoint_18_57_p8 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 8 189638781769505043 = some 201705460473313458 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 6 2 189638781769505043 201705460473313458 201705460473313458 endpoint_18_57_p6 endpoint_18_57_w6
private theorem endpoint_18_57_w8 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 8 2 201705460473313458 = some 201705460473313458 := by decide +kernel
private theorem endpoint_18_57_p10 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 10 189638781769505043 = some 201705460473313458 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 8 2 189638781769505043 201705460473313458 201705460473313458 endpoint_18_57_p8 endpoint_18_57_w8
private theorem endpoint_18_57_w10 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 10 2 201705460473313458 = some 201705460473313458 := by decide +kernel
private theorem endpoint_18_57_p12 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 12 189638781769505043 = some 201705460473313458 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 10 2 189638781769505043 201705460473313458 201705460473313458 endpoint_18_57_p10 endpoint_18_57_w10
private theorem endpoint_18_57_w12 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 12 2 201705460473313458 = some 201705460473313458 := by decide +kernel
private theorem endpoint_18_57_p14 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 14 189638781769505043 = some 201705460473313458 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 12 2 189638781769505043 201705460473313458 201705460473313458 endpoint_18_57_p12 endpoint_18_57_w12
private theorem endpoint_18_57_w14 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 14 2 201705460473313458 = some 201705460473313458 := by decide +kernel
private theorem endpoint_18_57_p16 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 16 189638781769505043 = some 201705460473313458 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 14 2 189638781769505043 201705460473313458 201705460473313458 endpoint_18_57_p14 endpoint_18_57_w14
private theorem endpoint_18_57_w16 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 16 1 201705460473313458 = some 201705460473313458 := by decide +kernel
private theorem endpoint_18_57_p17 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 17 189638781769505043 = some 201705460473313458 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 16 1 189638781769505043 201705460473313458 201705460473313458 endpoint_18_57_p16 endpoint_18_57_w16
def endpoint_18_57 : CertifiedEndpoint :=
  ⟨⟨18, 57, 1651⟩, 201705460473313458, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_18_57_flag endpoint_18_57_sources 17 189638781769505043 201705460473313458 rfl endpoint_18_57_base endpoint_18_57_p17) (by decide)⟩

def endpointBlock11 : List CertifiedEndpoint := [
  endpoint_16_63, endpoint_16_64, endpoint_16_65, endpoint_16_66, endpoint_16_67, endpoint_16_68, endpoint_16_69,
  endpoint_16_70, endpoint_16_71, endpoint_16_72, endpoint_16_73, endpoint_16_74, endpoint_16_75, endpoint_16_76,
  endpoint_16_77, endpoint_16_78, endpoint_16_79, endpoint_16_80, endpoint_16_81, endpoint_16_82, endpoint_16_83,
  endpoint_16_84, endpoint_17_17, endpoint_17_18, endpoint_17_19, endpoint_17_20, endpoint_17_21, endpoint_17_22,
  endpoint_17_23, endpoint_17_24, endpoint_17_25, endpoint_17_26, endpoint_17_27, endpoint_17_28, endpoint_17_29,
  endpoint_17_30, endpoint_17_31, endpoint_17_32, endpoint_17_33, endpoint_17_34, endpoint_17_35, endpoint_17_36,
  endpoint_17_37, endpoint_17_38, endpoint_17_39, endpoint_17_40, endpoint_17_41, endpoint_17_42, endpoint_17_43,
  endpoint_17_44, endpoint_17_45, endpoint_17_46, endpoint_17_47, endpoint_17_48, endpoint_17_49, endpoint_17_50,
  endpoint_17_51, endpoint_17_52, endpoint_17_53, endpoint_17_54, endpoint_17_55, endpoint_17_56, endpoint_17_57,
  endpoint_17_58, endpoint_17_59, endpoint_17_60, endpoint_17_61, endpoint_17_62, endpoint_17_63, endpoint_17_64,
  endpoint_17_65, endpoint_17_66, endpoint_17_67, endpoint_17_68, endpoint_17_69, endpoint_17_70, endpoint_17_71,
  endpoint_17_72, endpoint_17_73, endpoint_17_74, endpoint_17_75, endpoint_17_76, endpoint_17_77, endpoint_17_78,
  endpoint_17_79, endpoint_17_80, endpoint_17_81, endpoint_18_18, endpoint_18_19, endpoint_18_20, endpoint_18_21,
  endpoint_18_22, endpoint_18_23, endpoint_18_24, endpoint_18_25, endpoint_18_26, endpoint_18_27, endpoint_18_28,
  endpoint_18_29, endpoint_18_30, endpoint_18_31, endpoint_18_32, endpoint_18_33, endpoint_18_34, endpoint_18_35,
  endpoint_18_36, endpoint_18_37, endpoint_18_38, endpoint_18_39, endpoint_18_40, endpoint_18_41, endpoint_18_42,
  endpoint_18_43, endpoint_18_44, endpoint_18_45, endpoint_18_46, endpoint_18_47, endpoint_18_48, endpoint_18_49,
  endpoint_18_50, endpoint_18_51, endpoint_18_52, endpoint_18_53, endpoint_18_54, endpoint_18_55, endpoint_18_56,
  endpoint_18_57
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
