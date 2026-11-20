import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_18_58_flag : Flag := ⟨18, 58, 1594⟩
private def endpoint_18_58_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_58_base : receiptBase endpoint_18_58_flag endpoint_18_58_sources = some 187573586116755377 := by decide +kernel
private theorem endpoint_18_58_w0 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 2 187573586116755377 = some 187573586116755377 := by decide +kernel
private theorem endpoint_18_58_w2 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 2 2 187573586116755377 = some 187573586116755377 := by decide +kernel
private theorem endpoint_18_58_p4 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 4 187573586116755377 = some 187573586116755377 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 2 2 187573586116755377 187573586116755377 187573586116755377 endpoint_18_58_w0 endpoint_18_58_w2
private theorem endpoint_18_58_w4 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 4 2 187573586116755377 = some 187573586116755377 := by decide +kernel
private theorem endpoint_18_58_p6 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 6 187573586116755377 = some 187573586116755377 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 4 2 187573586116755377 187573586116755377 187573586116755377 endpoint_18_58_p4 endpoint_18_58_w4
private theorem endpoint_18_58_w6 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 6 2 187573586116755377 = some 187573586116755377 := by decide +kernel
private theorem endpoint_18_58_p8 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 8 187573586116755377 = some 187573586116755377 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 6 2 187573586116755377 187573586116755377 187573586116755377 endpoint_18_58_p6 endpoint_18_58_w6
private theorem endpoint_18_58_w8 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 8 2 187573586116755377 = some 187573586116755377 := by decide +kernel
private theorem endpoint_18_58_p10 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 10 187573586116755377 = some 187573586116755377 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 8 2 187573586116755377 187573586116755377 187573586116755377 endpoint_18_58_p8 endpoint_18_58_w8
private theorem endpoint_18_58_w10 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 10 2 187573586116755377 = some 187573586116755377 := by decide +kernel
private theorem endpoint_18_58_p12 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 12 187573586116755377 = some 187573586116755377 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 10 2 187573586116755377 187573586116755377 187573586116755377 endpoint_18_58_p10 endpoint_18_58_w10
private theorem endpoint_18_58_w12 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 12 2 187573586116755377 = some 187573586116755377 := by decide +kernel
private theorem endpoint_18_58_p14 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 14 187573586116755377 = some 187573586116755377 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 12 2 187573586116755377 187573586116755377 187573586116755377 endpoint_18_58_p12 endpoint_18_58_w12
private theorem endpoint_18_58_w14 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 14 2 187573586116755377 = some 187573586116755377 := by decide +kernel
private theorem endpoint_18_58_p16 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 16 187573586116755377 = some 187573586116755377 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 14 2 187573586116755377 187573586116755377 187573586116755377 endpoint_18_58_p14 endpoint_18_58_w14
private theorem endpoint_18_58_w16 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 16 1 187573586116755377 = some 187573586116755377 := by decide +kernel
private theorem endpoint_18_58_p17 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 17 187573586116755377 = some 187573586116755377 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 16 1 187573586116755377 187573586116755377 187573586116755377 endpoint_18_58_p16 endpoint_18_58_w16
def endpoint_18_58 : CertifiedEndpoint :=
  ⟨⟨18, 58, 1594⟩, 187573586116755377, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_58_flag endpoint_18_58_sources 17 187573586116755377 187573586116755377 rfl endpoint_18_58_base endpoint_18_58_p17) (by decide)⟩
private def endpoint_18_59_flag : Flag := ⟨18, 59, 1535⟩
private def endpoint_18_59_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_59_base : receiptBase endpoint_18_59_flag endpoint_18_59_sources = some 183450638085246034 := by decide +kernel
private theorem endpoint_18_59_w0 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 2 183450638085246034 = some 187230266012206610 := by decide +kernel
private theorem endpoint_18_59_w2 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 2 2 187230266012206610 = some 187230266012206610 := by decide +kernel
private theorem endpoint_18_59_p4 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 4 183450638085246034 = some 187230266012206610 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 2 2 183450638085246034 187230266012206610 187230266012206610 endpoint_18_59_w0 endpoint_18_59_w2
private theorem endpoint_18_59_w4 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 4 2 187230266012206610 = some 187230266012206610 := by decide +kernel
private theorem endpoint_18_59_p6 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 6 183450638085246034 = some 187230266012206610 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 4 2 183450638085246034 187230266012206610 187230266012206610 endpoint_18_59_p4 endpoint_18_59_w4
private theorem endpoint_18_59_w6 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 6 2 187230266012206610 = some 187230266012206610 := by decide +kernel
private theorem endpoint_18_59_p8 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 8 183450638085246034 = some 187230266012206610 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 6 2 183450638085246034 187230266012206610 187230266012206610 endpoint_18_59_p6 endpoint_18_59_w6
private theorem endpoint_18_59_w8 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 8 2 187230266012206610 = some 187230266012206610 := by decide +kernel
private theorem endpoint_18_59_p10 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 10 183450638085246034 = some 187230266012206610 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 8 2 183450638085246034 187230266012206610 187230266012206610 endpoint_18_59_p8 endpoint_18_59_w8
private theorem endpoint_18_59_w10 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 10 2 187230266012206610 = some 187230266012206610 := by decide +kernel
private theorem endpoint_18_59_p12 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 12 183450638085246034 = some 187230266012206610 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 10 2 183450638085246034 187230266012206610 187230266012206610 endpoint_18_59_p10 endpoint_18_59_w10
private theorem endpoint_18_59_w12 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 12 2 187230266012206610 = some 187230266012206610 := by decide +kernel
private theorem endpoint_18_59_p14 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 14 183450638085246034 = some 187230266012206610 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 12 2 183450638085246034 187230266012206610 187230266012206610 endpoint_18_59_p12 endpoint_18_59_w12
private theorem endpoint_18_59_w14 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 14 2 187230266012206610 = some 187230266012206610 := by decide +kernel
private theorem endpoint_18_59_p16 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 16 183450638085246034 = some 187230266012206610 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 14 2 183450638085246034 187230266012206610 187230266012206610 endpoint_18_59_p14 endpoint_18_59_w14
private theorem endpoint_18_59_w16 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 16 1 187230266012206610 = some 187230266012206610 := by decide +kernel
private theorem endpoint_18_59_p17 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 17 183450638085246034 = some 187230266012206610 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 16 1 183450638085246034 187230266012206610 187230266012206610 endpoint_18_59_p16 endpoint_18_59_w16
def endpoint_18_59 : CertifiedEndpoint :=
  ⟨⟨18, 59, 1535⟩, 187230266012206610, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_59_flag endpoint_18_59_sources 17 183450638085246034 187230266012206610 rfl endpoint_18_59_base endpoint_18_59_p17) (by decide)⟩
private def endpoint_18_60_flag : Flag := ⟨18, 60, 1476⟩
private def endpoint_18_60_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_60_base : receiptBase endpoint_18_60_flag endpoint_18_60_sources = some 179117781831010694 := by decide +kernel
private theorem endpoint_18_60_w0 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 2 179117781831010694 = some 186834026277558000 := by decide +kernel
private theorem endpoint_18_60_w2 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 2 2 186834026277558000 = some 186834026277558000 := by decide +kernel
private theorem endpoint_18_60_p4 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 4 179117781831010694 = some 186834026277558000 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 2 2 179117781831010694 186834026277558000 186834026277558000 endpoint_18_60_w0 endpoint_18_60_w2
private theorem endpoint_18_60_w4 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 4 2 186834026277558000 = some 186834026277558000 := by decide +kernel
private theorem endpoint_18_60_p6 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 6 179117781831010694 = some 186834026277558000 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 4 2 179117781831010694 186834026277558000 186834026277558000 endpoint_18_60_p4 endpoint_18_60_w4
private theorem endpoint_18_60_w6 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 6 2 186834026277558000 = some 186834026277558000 := by decide +kernel
private theorem endpoint_18_60_p8 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 8 179117781831010694 = some 186834026277558000 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 6 2 179117781831010694 186834026277558000 186834026277558000 endpoint_18_60_p6 endpoint_18_60_w6
private theorem endpoint_18_60_w8 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 8 2 186834026277558000 = some 186834026277558000 := by decide +kernel
private theorem endpoint_18_60_p10 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 10 179117781831010694 = some 186834026277558000 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 8 2 179117781831010694 186834026277558000 186834026277558000 endpoint_18_60_p8 endpoint_18_60_w8
private theorem endpoint_18_60_w10 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 10 2 186834026277558000 = some 186834026277558000 := by decide +kernel
private theorem endpoint_18_60_p12 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 12 179117781831010694 = some 186834026277558000 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 10 2 179117781831010694 186834026277558000 186834026277558000 endpoint_18_60_p10 endpoint_18_60_w10
private theorem endpoint_18_60_w12 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 12 2 186834026277558000 = some 186834026277558000 := by decide +kernel
private theorem endpoint_18_60_p14 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 14 179117781831010694 = some 186834026277558000 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 12 2 179117781831010694 186834026277558000 186834026277558000 endpoint_18_60_p12 endpoint_18_60_w12
private theorem endpoint_18_60_w14 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 14 2 186834026277558000 = some 186834026277558000 := by decide +kernel
private theorem endpoint_18_60_p16 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 16 179117781831010694 = some 186834026277558000 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 14 2 179117781831010694 186834026277558000 186834026277558000 endpoint_18_60_p14 endpoint_18_60_w14
private theorem endpoint_18_60_w16 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 16 1 186834026277558000 = some 186834026277558000 := by decide +kernel
private theorem endpoint_18_60_p17 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 17 179117781831010694 = some 186834026277558000 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 16 1 179117781831010694 186834026277558000 186834026277558000 endpoint_18_60_p16 endpoint_18_60_w16
def endpoint_18_60 : CertifiedEndpoint :=
  ⟨⟨18, 60, 1476⟩, 186834026277558000, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_60_flag endpoint_18_60_sources 17 179117781831010694 186834026277558000 rfl endpoint_18_60_base endpoint_18_60_p17) (by decide)⟩
private def endpoint_18_61_flag : Flag := ⟨18, 61, 1414⟩
private def endpoint_18_61_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_18_61_base : receiptBase endpoint_18_61_flag endpoint_18_61_sources = some 174483716755472512 := by decide +kernel
private theorem endpoint_18_61_w0 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 2 174483716755472512 = some 183123921892886797 := by decide +kernel
private theorem endpoint_18_61_w2 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 2 2 183123921892886797 = some 183123921892886797 := by decide +kernel
private theorem endpoint_18_61_p4 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 4 174483716755472512 = some 183123921892886797 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 2 2 174483716755472512 183123921892886797 183123921892886797 endpoint_18_61_w0 endpoint_18_61_w2
private theorem endpoint_18_61_w4 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 4 2 183123921892886797 = some 183123921892886797 := by decide +kernel
private theorem endpoint_18_61_p6 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 6 174483716755472512 = some 183123921892886797 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 4 2 174483716755472512 183123921892886797 183123921892886797 endpoint_18_61_p4 endpoint_18_61_w4
private theorem endpoint_18_61_w6 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 6 2 183123921892886797 = some 183123921892886797 := by decide +kernel
private theorem endpoint_18_61_p8 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 8 174483716755472512 = some 183123921892886797 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 6 2 174483716755472512 183123921892886797 183123921892886797 endpoint_18_61_p6 endpoint_18_61_w6
private theorem endpoint_18_61_w8 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 8 2 183123921892886797 = some 183123921892886797 := by decide +kernel
private theorem endpoint_18_61_p10 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 10 174483716755472512 = some 183123921892886797 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 8 2 174483716755472512 183123921892886797 183123921892886797 endpoint_18_61_p8 endpoint_18_61_w8
private theorem endpoint_18_61_w10 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 10 2 183123921892886797 = some 183123921892886797 := by decide +kernel
private theorem endpoint_18_61_p12 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 12 174483716755472512 = some 183123921892886797 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 10 2 174483716755472512 183123921892886797 183123921892886797 endpoint_18_61_p10 endpoint_18_61_w10
private theorem endpoint_18_61_w12 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 12 2 183123921892886797 = some 183123921892886797 := by decide +kernel
private theorem endpoint_18_61_p14 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 14 174483716755472512 = some 183123921892886797 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 12 2 174483716755472512 183123921892886797 183123921892886797 endpoint_18_61_p12 endpoint_18_61_w12
private theorem endpoint_18_61_w14 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 14 2 183123921892886797 = some 183123921892886797 := by decide +kernel
private theorem endpoint_18_61_p16 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 16 174483716755472512 = some 183123921892886797 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 14 2 174483716755472512 183123921892886797 183123921892886797 endpoint_18_61_p14 endpoint_18_61_w14
private theorem endpoint_18_61_w16 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 16 1 183123921892886797 = some 183123921892886797 := by decide +kernel
private theorem endpoint_18_61_p17 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 17 174483716755472512 = some 183123921892886797 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 16 1 174483716755472512 183123921892886797 183123921892886797 endpoint_18_61_p16 endpoint_18_61_w16
def endpoint_18_61 : CertifiedEndpoint :=
  ⟨⟨18, 61, 1414⟩, 183123921892886797, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_18_61_flag endpoint_18_61_sources 17 174483716755472512 183123921892886797 rfl endpoint_18_61_base endpoint_18_61_p17) (by decide)⟩
private def endpoint_18_62_flag : Flag := ⟨18, 62, 1352⟩
private def endpoint_18_62_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_18_62_base : receiptBase endpoint_18_62_flag endpoint_18_62_sources = some 170720577523343006 := by decide +kernel
private theorem endpoint_18_62_w0 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 2 170720577523343006 = some 174639000671692048 := by decide +kernel
private theorem endpoint_18_62_w2 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 2 2 174639000671692048 = some 174639000671692048 := by decide +kernel
private theorem endpoint_18_62_p4 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 4 170720577523343006 = some 174639000671692048 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 2 2 170720577523343006 174639000671692048 174639000671692048 endpoint_18_62_w0 endpoint_18_62_w2
private theorem endpoint_18_62_w4 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 4 2 174639000671692048 = some 174639000671692048 := by decide +kernel
private theorem endpoint_18_62_p6 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 6 170720577523343006 = some 174639000671692048 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 4 2 170720577523343006 174639000671692048 174639000671692048 endpoint_18_62_p4 endpoint_18_62_w4
private theorem endpoint_18_62_w6 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 6 2 174639000671692048 = some 174639000671692048 := by decide +kernel
private theorem endpoint_18_62_p8 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 8 170720577523343006 = some 174639000671692048 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 6 2 170720577523343006 174639000671692048 174639000671692048 endpoint_18_62_p6 endpoint_18_62_w6
private theorem endpoint_18_62_w8 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 8 2 174639000671692048 = some 174639000671692048 := by decide +kernel
private theorem endpoint_18_62_p10 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 10 170720577523343006 = some 174639000671692048 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 8 2 170720577523343006 174639000671692048 174639000671692048 endpoint_18_62_p8 endpoint_18_62_w8
private theorem endpoint_18_62_w10 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 10 2 174639000671692048 = some 174639000671692048 := by decide +kernel
private theorem endpoint_18_62_p12 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 12 170720577523343006 = some 174639000671692048 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 10 2 170720577523343006 174639000671692048 174639000671692048 endpoint_18_62_p10 endpoint_18_62_w10
private theorem endpoint_18_62_w12 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 12 2 174639000671692048 = some 174639000671692048 := by decide +kernel
private theorem endpoint_18_62_p14 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 14 170720577523343006 = some 174639000671692048 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 12 2 170720577523343006 174639000671692048 174639000671692048 endpoint_18_62_p12 endpoint_18_62_w12
private theorem endpoint_18_62_w14 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 14 2 174639000671692048 = some 174639000671692048 := by decide +kernel
private theorem endpoint_18_62_p16 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 16 170720577523343006 = some 174639000671692048 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 14 2 170720577523343006 174639000671692048 174639000671692048 endpoint_18_62_p14 endpoint_18_62_w14
private theorem endpoint_18_62_w16 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 16 1 174639000671692048 = some 174639000671692048 := by decide +kernel
private theorem endpoint_18_62_p17 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 17 170720577523343006 = some 174639000671692048 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 16 1 170720577523343006 174639000671692048 174639000671692048 endpoint_18_62_p16 endpoint_18_62_w16
def endpoint_18_62 : CertifiedEndpoint :=
  ⟨⟨18, 62, 1352⟩, 174639000671692048, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_18_62_flag endpoint_18_62_sources 17 170720577523343006 174639000671692048 rfl endpoint_18_62_base endpoint_18_62_p17) (by decide)⟩
private def endpoint_18_63_flag : Flag := ⟨18, 63, 1288⟩
private def endpoint_18_63_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_18_63_base : receiptBase endpoint_18_63_flag endpoint_18_63_sources = some 165147269338817819 := by decide +kernel
private theorem endpoint_18_63_w0 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 2 165147269338817819 = some 173156252983656921 := by decide +kernel
private theorem endpoint_18_63_w2 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 2 2 173156252983656921 = some 173156252983656921 := by decide +kernel
private theorem endpoint_18_63_p4 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 4 165147269338817819 = some 173156252983656921 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 2 2 165147269338817819 173156252983656921 173156252983656921 endpoint_18_63_w0 endpoint_18_63_w2
private theorem endpoint_18_63_w4 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 4 2 173156252983656921 = some 173156252983656921 := by decide +kernel
private theorem endpoint_18_63_p6 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 6 165147269338817819 = some 173156252983656921 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 4 2 165147269338817819 173156252983656921 173156252983656921 endpoint_18_63_p4 endpoint_18_63_w4
private theorem endpoint_18_63_w6 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 6 2 173156252983656921 = some 173156252983656921 := by decide +kernel
private theorem endpoint_18_63_p8 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 8 165147269338817819 = some 173156252983656921 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 6 2 165147269338817819 173156252983656921 173156252983656921 endpoint_18_63_p6 endpoint_18_63_w6
private theorem endpoint_18_63_w8 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 8 2 173156252983656921 = some 173156252983656921 := by decide +kernel
private theorem endpoint_18_63_p10 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 10 165147269338817819 = some 173156252983656921 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 8 2 165147269338817819 173156252983656921 173156252983656921 endpoint_18_63_p8 endpoint_18_63_w8
private theorem endpoint_18_63_w10 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 10 2 173156252983656921 = some 173156252983656921 := by decide +kernel
private theorem endpoint_18_63_p12 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 12 165147269338817819 = some 173156252983656921 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 10 2 165147269338817819 173156252983656921 173156252983656921 endpoint_18_63_p10 endpoint_18_63_w10
private theorem endpoint_18_63_w12 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 12 2 173156252983656921 = some 173156252983656921 := by decide +kernel
private theorem endpoint_18_63_p14 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 14 165147269338817819 = some 173156252983656921 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 12 2 165147269338817819 173156252983656921 173156252983656921 endpoint_18_63_p12 endpoint_18_63_w12
private theorem endpoint_18_63_w14 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 14 2 173156252983656921 = some 173156252983656921 := by decide +kernel
private theorem endpoint_18_63_p16 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 16 165147269338817819 = some 173156252983656921 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 14 2 165147269338817819 173156252983656921 173156252983656921 endpoint_18_63_p14 endpoint_18_63_w14
private theorem endpoint_18_63_w16 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 16 1 173156252983656921 = some 173156252983656921 := by decide +kernel
private theorem endpoint_18_63_p17 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 17 165147269338817819 = some 173156252983656921 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 16 1 165147269338817819 173156252983656921 173156252983656921 endpoint_18_63_p16 endpoint_18_63_w16
def endpoint_18_63 : CertifiedEndpoint :=
  ⟨⟨18, 63, 1288⟩, 173156252983656921, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_18_63_flag endpoint_18_63_sources 17 165147269338817819 173156252983656921 rfl endpoint_18_63_base endpoint_18_63_p17) (by decide)⟩
private def endpoint_18_64_flag : Flag := ⟨18, 64, 1223⟩
private def endpoint_18_64_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_18_64_base : receiptBase endpoint_18_64_flag endpoint_18_64_sources = some 160826674977501790 := by decide +kernel
private theorem endpoint_18_64_w0 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 2 160826674977501790 = some 162261588891337052 := by decide +kernel
private theorem endpoint_18_64_w2 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 2 2 162261588891337052 = some 162261588891337052 := by decide +kernel
private theorem endpoint_18_64_p4 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 4 160826674977501790 = some 162261588891337052 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 2 2 160826674977501790 162261588891337052 162261588891337052 endpoint_18_64_w0 endpoint_18_64_w2
private theorem endpoint_18_64_w4 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 4 2 162261588891337052 = some 162261588891337052 := by decide +kernel
private theorem endpoint_18_64_p6 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 6 160826674977501790 = some 162261588891337052 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 4 2 160826674977501790 162261588891337052 162261588891337052 endpoint_18_64_p4 endpoint_18_64_w4
private theorem endpoint_18_64_w6 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 6 2 162261588891337052 = some 162261588891337052 := by decide +kernel
private theorem endpoint_18_64_p8 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 8 160826674977501790 = some 162261588891337052 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 6 2 160826674977501790 162261588891337052 162261588891337052 endpoint_18_64_p6 endpoint_18_64_w6
private theorem endpoint_18_64_w8 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 8 2 162261588891337052 = some 162261588891337052 := by decide +kernel
private theorem endpoint_18_64_p10 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 10 160826674977501790 = some 162261588891337052 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 8 2 160826674977501790 162261588891337052 162261588891337052 endpoint_18_64_p8 endpoint_18_64_w8
private theorem endpoint_18_64_w10 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 10 2 162261588891337052 = some 162261588891337052 := by decide +kernel
private theorem endpoint_18_64_p12 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 12 160826674977501790 = some 162261588891337052 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 10 2 160826674977501790 162261588891337052 162261588891337052 endpoint_18_64_p10 endpoint_18_64_w10
private theorem endpoint_18_64_w12 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 12 2 162261588891337052 = some 162261588891337052 := by decide +kernel
private theorem endpoint_18_64_p14 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 14 160826674977501790 = some 162261588891337052 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 12 2 160826674977501790 162261588891337052 162261588891337052 endpoint_18_64_p12 endpoint_18_64_w12
private theorem endpoint_18_64_w14 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 14 2 162261588891337052 = some 162261588891337052 := by decide +kernel
private theorem endpoint_18_64_p16 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 16 160826674977501790 = some 162261588891337052 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 14 2 160826674977501790 162261588891337052 162261588891337052 endpoint_18_64_p14 endpoint_18_64_w14
private theorem endpoint_18_64_w16 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 16 1 162261588891337052 = some 162261588891337052 := by decide +kernel
private theorem endpoint_18_64_p17 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 17 160826674977501790 = some 162261588891337052 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 16 1 160826674977501790 162261588891337052 162261588891337052 endpoint_18_64_p16 endpoint_18_64_w16
def endpoint_18_64 : CertifiedEndpoint :=
  ⟨⟨18, 64, 1223⟩, 162261588891337052, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_18_64_flag endpoint_18_64_sources 17 160826674977501790 162261588891337052 rfl endpoint_18_64_base endpoint_18_64_p17) (by decide)⟩
private def endpoint_18_65_flag : Flag := ⟨18, 65, 1156⟩
private def endpoint_18_65_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_18_65_base : receiptBase endpoint_18_65_flag endpoint_18_65_sources = some 154219494788359453 := by decide +kernel
private theorem endpoint_18_65_w0 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 2 154219494788359453 = some 160011646329922436 := by decide +kernel
private theorem endpoint_18_65_w2 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 2 2 160011646329922436 = some 160011646329922436 := by decide +kernel
private theorem endpoint_18_65_p4 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 4 154219494788359453 = some 160011646329922436 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 2 2 154219494788359453 160011646329922436 160011646329922436 endpoint_18_65_w0 endpoint_18_65_w2
private theorem endpoint_18_65_w4 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 4 2 160011646329922436 = some 160011646329922436 := by decide +kernel
private theorem endpoint_18_65_p6 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 6 154219494788359453 = some 160011646329922436 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 4 2 154219494788359453 160011646329922436 160011646329922436 endpoint_18_65_p4 endpoint_18_65_w4
private theorem endpoint_18_65_w6 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 6 2 160011646329922436 = some 160011646329922436 := by decide +kernel
private theorem endpoint_18_65_p8 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 8 154219494788359453 = some 160011646329922436 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 6 2 154219494788359453 160011646329922436 160011646329922436 endpoint_18_65_p6 endpoint_18_65_w6
private theorem endpoint_18_65_w8 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 8 2 160011646329922436 = some 160011646329922436 := by decide +kernel
private theorem endpoint_18_65_p10 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 10 154219494788359453 = some 160011646329922436 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 8 2 154219494788359453 160011646329922436 160011646329922436 endpoint_18_65_p8 endpoint_18_65_w8
private theorem endpoint_18_65_w10 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 10 2 160011646329922436 = some 160011646329922436 := by decide +kernel
private theorem endpoint_18_65_p12 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 12 154219494788359453 = some 160011646329922436 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 10 2 154219494788359453 160011646329922436 160011646329922436 endpoint_18_65_p10 endpoint_18_65_w10
private theorem endpoint_18_65_w12 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 12 2 160011646329922436 = some 160011646329922436 := by decide +kernel
private theorem endpoint_18_65_p14 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 14 154219494788359453 = some 160011646329922436 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 12 2 154219494788359453 160011646329922436 160011646329922436 endpoint_18_65_p12 endpoint_18_65_w12
private theorem endpoint_18_65_w14 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 14 2 160011646329922436 = some 160011646329922436 := by decide +kernel
private theorem endpoint_18_65_p16 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 16 154219494788359453 = some 160011646329922436 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 14 2 154219494788359453 160011646329922436 160011646329922436 endpoint_18_65_p14 endpoint_18_65_w14
private theorem endpoint_18_65_w16 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 16 1 160011646329922436 = some 160011646329922436 := by decide +kernel
private theorem endpoint_18_65_p17 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 17 154219494788359453 = some 160011646329922436 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 16 1 154219494788359453 160011646329922436 160011646329922436 endpoint_18_65_p16 endpoint_18_65_w16
def endpoint_18_65 : CertifiedEndpoint :=
  ⟨⟨18, 65, 1156⟩, 160011646329922436, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_18_65_flag endpoint_18_65_sources 17 154219494788359453 160011646329922436 rfl endpoint_18_65_base endpoint_18_65_p17) (by decide)⟩
private def endpoint_18_66_flag : Flag := ⟨18, 66, 1087⟩
private def endpoint_18_66_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_18_66_base : receiptBase endpoint_18_66_flag endpoint_18_66_sources = some 147108686363339774 := by decide +kernel
private theorem endpoint_18_66_w0 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 2 147108686363339774 = some 157413648037542684 := by decide +kernel
private theorem endpoint_18_66_w2 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 2 2 157413648037542684 = some 157413648037542684 := by decide +kernel
private theorem endpoint_18_66_p4 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 4 147108686363339774 = some 157413648037542684 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 2 2 147108686363339774 157413648037542684 157413648037542684 endpoint_18_66_w0 endpoint_18_66_w2
private theorem endpoint_18_66_w4 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 4 2 157413648037542684 = some 157413648037542684 := by decide +kernel
private theorem endpoint_18_66_p6 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 6 147108686363339774 = some 157413648037542684 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 4 2 147108686363339774 157413648037542684 157413648037542684 endpoint_18_66_p4 endpoint_18_66_w4
private theorem endpoint_18_66_w6 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 6 2 157413648037542684 = some 157413648037542684 := by decide +kernel
private theorem endpoint_18_66_p8 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 8 147108686363339774 = some 157413648037542684 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 6 2 147108686363339774 157413648037542684 157413648037542684 endpoint_18_66_p6 endpoint_18_66_w6
private theorem endpoint_18_66_w8 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 8 2 157413648037542684 = some 157413648037542684 := by decide +kernel
private theorem endpoint_18_66_p10 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 10 147108686363339774 = some 157413648037542684 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 8 2 147108686363339774 157413648037542684 157413648037542684 endpoint_18_66_p8 endpoint_18_66_w8
private theorem endpoint_18_66_w10 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 10 2 157413648037542684 = some 157413648037542684 := by decide +kernel
private theorem endpoint_18_66_p12 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 12 147108686363339774 = some 157413648037542684 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 10 2 147108686363339774 157413648037542684 157413648037542684 endpoint_18_66_p10 endpoint_18_66_w10
private theorem endpoint_18_66_w12 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 12 2 157413648037542684 = some 157413648037542684 := by decide +kernel
private theorem endpoint_18_66_p14 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 14 147108686363339774 = some 157413648037542684 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 12 2 147108686363339774 157413648037542684 157413648037542684 endpoint_18_66_p12 endpoint_18_66_w12
private theorem endpoint_18_66_w14 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 14 2 157413648037542684 = some 157413648037542684 := by decide +kernel
private theorem endpoint_18_66_p16 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 16 147108686363339774 = some 157413648037542684 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 14 2 147108686363339774 157413648037542684 157413648037542684 endpoint_18_66_p14 endpoint_18_66_w14
private theorem endpoint_18_66_w16 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 16 1 157413648037542684 = some 157413648037542684 := by decide +kernel
private theorem endpoint_18_66_p17 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 17 147108686363339774 = some 157413648037542684 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 16 1 147108686363339774 157413648037542684 157413648037542684 endpoint_18_66_p16 endpoint_18_66_w16
def endpoint_18_66 : CertifiedEndpoint :=
  ⟨⟨18, 66, 1087⟩, 157413648037542684, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_18_66_flag endpoint_18_66_sources 17 147108686363339774 157413648037542684 rfl endpoint_18_66_base endpoint_18_66_p17) (by decide)⟩
def endpoint_18_67 : CertifiedEndpoint :=
  ⟨⟨18, 67, 1017⟩, 254354588824282022, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_68 : CertifiedEndpoint :=
  ⟨⟨18, 68, 945⟩, 239612629091391227, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_69 : CertifiedEndpoint :=
  ⟨⟨18, 69, 872⟩, 223946644306099745, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_70 : CertifiedEndpoint :=
  ⟨⟨18, 70, 796⟩, 206796333397448912, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_71 : CertifiedEndpoint :=
  ⟨⟨18, 71, 719⟩, 188676813259771332, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_72 : CertifiedEndpoint :=
  ⟨⟨18, 72, 640⟩, 169292118895768552, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_73 : CertifiedEndpoint :=
  ⟨⟨18, 73, 559⟩, 148615139799464936, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_74 : CertifiedEndpoint :=
  ⟨⟨18, 74, 476⟩, 126618765464884848, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_75 : CertifiedEndpoint :=
  ⟨⟨18, 75, 391⟩, 103275885386052652, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_76 : CertifiedEndpoint :=
  ⟨⟨18, 76, 303⟩, 78258905642031653, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_77 : CertifiedEndpoint :=
  ⟨⟨18, 77, 213⟩, 51832162306482062, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_78 : CertifiedEndpoint :=
  ⟨⟨18, 78, 121⟩, 23968544873428243, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_19 : CertifiedEndpoint :=
  ⟨⟨19, 19, 2946⟩, 144858155970797671, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_20 : CertifiedEndpoint :=
  ⟨⟨19, 20, 2914⟩, 147825080423324866, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_21 : CertifiedEndpoint :=
  ⟨⟨19, 21, 2882⟩, 150691397049507677, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_22 : CertifiedEndpoint :=
  ⟨⟨19, 22, 2850⟩, 162519186579437358, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_23 : CertifiedEndpoint :=
  ⟨⟨19, 23, 2816⟩, 173912331721676295, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_24 : CertifiedEndpoint :=
  ⟨⟨19, 24, 2783⟩, 185042798797578875, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_25 : CertifiedEndpoint :=
  ⟨⟨19, 25, 2749⟩, 195781615226933266, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_26 : CertifiedEndpoint :=
  ⟨⟨19, 26, 2714⟩, 206114452643763894, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_27 : CertifiedEndpoint :=
  ⟨⟨19, 27, 2679⟩, 216108185399172604, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_28 : CertifiedEndpoint :=
  ⟨⟨19, 28, 2643⟩, 225676834654090119, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_29 : CertifiedEndpoint :=
  ⟨⟨19, 29, 2607⟩, 234896827003602000, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_30 : CertifiedEndpoint :=
  ⟨⟨19, 30, 2570⟩, 243672631364655254, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_31 : CertifiedEndpoint :=
  ⟨⟨19, 31, 2533⟩, 252090226576319158, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_19_32_flag : Flag := ⟨19, 32, 2495⟩
private def endpoint_19_32_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_32_base : receiptBase endpoint_19_32_flag endpoint_19_32_sources = some 170496406164625120 := by decide +kernel
private theorem endpoint_19_32_w0 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 2 170496406164625120 = some 170496406164625120 := by decide +kernel
private theorem endpoint_19_32_w2 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 2 2 170496406164625120 = some 170496406164625120 := by decide +kernel
private theorem endpoint_19_32_p4 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 4 170496406164625120 = some 170496406164625120 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 2 2 170496406164625120 170496406164625120 170496406164625120 endpoint_19_32_w0 endpoint_19_32_w2
private theorem endpoint_19_32_w4 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 4 2 170496406164625120 = some 170496406164625120 := by decide +kernel
private theorem endpoint_19_32_p6 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 6 170496406164625120 = some 170496406164625120 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 4 2 170496406164625120 170496406164625120 170496406164625120 endpoint_19_32_p4 endpoint_19_32_w4
private theorem endpoint_19_32_w6 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 6 2 170496406164625120 = some 170496406164625120 := by decide +kernel
private theorem endpoint_19_32_p8 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 8 170496406164625120 = some 170496406164625120 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 6 2 170496406164625120 170496406164625120 170496406164625120 endpoint_19_32_p6 endpoint_19_32_w6
private theorem endpoint_19_32_w8 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 8 2 170496406164625120 = some 170496406164625120 := by decide +kernel
private theorem endpoint_19_32_p10 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 10 170496406164625120 = some 170496406164625120 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 8 2 170496406164625120 170496406164625120 170496406164625120 endpoint_19_32_p8 endpoint_19_32_w8
private theorem endpoint_19_32_w10 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 10 2 170496406164625120 = some 170496406164625120 := by decide +kernel
private theorem endpoint_19_32_p12 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 12 170496406164625120 = some 170496406164625120 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 10 2 170496406164625120 170496406164625120 170496406164625120 endpoint_19_32_p10 endpoint_19_32_w10
private theorem endpoint_19_32_w12 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 12 2 170496406164625120 = some 170496406164625120 := by decide +kernel
private theorem endpoint_19_32_p14 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 14 170496406164625120 = some 170496406164625120 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 12 2 170496406164625120 170496406164625120 170496406164625120 endpoint_19_32_p12 endpoint_19_32_w12
private theorem endpoint_19_32_w14 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 14 2 170496406164625120 = some 170496406164625120 := by decide +kernel
private theorem endpoint_19_32_p16 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 16 170496406164625120 = some 170496406164625120 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 14 2 170496406164625120 170496406164625120 170496406164625120 endpoint_19_32_p14 endpoint_19_32_w14
private theorem endpoint_19_32_w16 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 16 2 170496406164625120 = some 170496406164625120 := by decide +kernel
private theorem endpoint_19_32_p18 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 18 170496406164625120 = some 170496406164625120 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 16 2 170496406164625120 170496406164625120 170496406164625120 endpoint_19_32_p16 endpoint_19_32_w16
def endpoint_19_32 : CertifiedEndpoint :=
  ⟨⟨19, 32, 2495⟩, 170496406164625120, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_32_flag endpoint_19_32_sources 18 170496406164625120 170496406164625120 rfl endpoint_19_32_base endpoint_19_32_p18) (by decide)⟩
private def endpoint_19_33_flag : Flag := ⟨19, 33, 2456⟩
private def endpoint_19_33_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_33_base : receiptBase endpoint_19_33_flag endpoint_19_33_sources = some 172268172719135061 := by decide +kernel
private theorem endpoint_19_33_w0 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 2 172268172719135061 = some 172268172719135061 := by decide +kernel
private theorem endpoint_19_33_w2 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 2 2 172268172719135061 = some 172268172719135061 := by decide +kernel
private theorem endpoint_19_33_p4 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 4 172268172719135061 = some 172268172719135061 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 2 2 172268172719135061 172268172719135061 172268172719135061 endpoint_19_33_w0 endpoint_19_33_w2
private theorem endpoint_19_33_w4 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 4 2 172268172719135061 = some 172268172719135061 := by decide +kernel
private theorem endpoint_19_33_p6 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 6 172268172719135061 = some 172268172719135061 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 4 2 172268172719135061 172268172719135061 172268172719135061 endpoint_19_33_p4 endpoint_19_33_w4
private theorem endpoint_19_33_w6 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 6 2 172268172719135061 = some 172268172719135061 := by decide +kernel
private theorem endpoint_19_33_p8 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 8 172268172719135061 = some 172268172719135061 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 6 2 172268172719135061 172268172719135061 172268172719135061 endpoint_19_33_p6 endpoint_19_33_w6
private theorem endpoint_19_33_w8 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 8 2 172268172719135061 = some 172268172719135061 := by decide +kernel
private theorem endpoint_19_33_p10 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 10 172268172719135061 = some 172268172719135061 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 8 2 172268172719135061 172268172719135061 172268172719135061 endpoint_19_33_p8 endpoint_19_33_w8
private theorem endpoint_19_33_w10 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 10 2 172268172719135061 = some 172268172719135061 := by decide +kernel
private theorem endpoint_19_33_p12 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 12 172268172719135061 = some 172268172719135061 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 10 2 172268172719135061 172268172719135061 172268172719135061 endpoint_19_33_p10 endpoint_19_33_w10
private theorem endpoint_19_33_w12 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 12 2 172268172719135061 = some 172268172719135061 := by decide +kernel
private theorem endpoint_19_33_p14 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 14 172268172719135061 = some 172268172719135061 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 12 2 172268172719135061 172268172719135061 172268172719135061 endpoint_19_33_p12 endpoint_19_33_w12
private theorem endpoint_19_33_w14 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 14 2 172268172719135061 = some 172268172719135061 := by decide +kernel
private theorem endpoint_19_33_p16 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 16 172268172719135061 = some 172268172719135061 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 14 2 172268172719135061 172268172719135061 172268172719135061 endpoint_19_33_p14 endpoint_19_33_w14
private theorem endpoint_19_33_w16 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 16 2 172268172719135061 = some 172268172719135061 := by decide +kernel
private theorem endpoint_19_33_p18 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 18 172268172719135061 = some 172268172719135061 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 16 2 172268172719135061 172268172719135061 172268172719135061 endpoint_19_33_p16 endpoint_19_33_w16
def endpoint_19_33 : CertifiedEndpoint :=
  ⟨⟨19, 33, 2456⟩, 172268172719135061, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_33_flag endpoint_19_33_sources 18 172268172719135061 172268172719135061 rfl endpoint_19_33_base endpoint_19_33_p18) (by decide)⟩
private def endpoint_19_34_flag : Flag := ⟨19, 34, 2417⟩
private def endpoint_19_34_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_34_base : receiptBase endpoint_19_34_flag endpoint_19_34_sources = some 173901554593545219 := by decide +kernel
private theorem endpoint_19_34_w0 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 2 173901554593545219 = some 173901554593545219 := by decide +kernel
private theorem endpoint_19_34_w2 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 2 2 173901554593545219 = some 173901554593545219 := by decide +kernel
private theorem endpoint_19_34_p4 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 4 173901554593545219 = some 173901554593545219 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 2 2 173901554593545219 173901554593545219 173901554593545219 endpoint_19_34_w0 endpoint_19_34_w2
private theorem endpoint_19_34_w4 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 4 2 173901554593545219 = some 173901554593545219 := by decide +kernel
private theorem endpoint_19_34_p6 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 6 173901554593545219 = some 173901554593545219 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 4 2 173901554593545219 173901554593545219 173901554593545219 endpoint_19_34_p4 endpoint_19_34_w4
private theorem endpoint_19_34_w6 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 6 2 173901554593545219 = some 173901554593545219 := by decide +kernel
private theorem endpoint_19_34_p8 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 8 173901554593545219 = some 173901554593545219 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 6 2 173901554593545219 173901554593545219 173901554593545219 endpoint_19_34_p6 endpoint_19_34_w6
private theorem endpoint_19_34_w8 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 8 2 173901554593545219 = some 173901554593545219 := by decide +kernel
private theorem endpoint_19_34_p10 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 10 173901554593545219 = some 173901554593545219 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 8 2 173901554593545219 173901554593545219 173901554593545219 endpoint_19_34_p8 endpoint_19_34_w8
private theorem endpoint_19_34_w10 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 10 2 173901554593545219 = some 173901554593545219 := by decide +kernel
private theorem endpoint_19_34_p12 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 12 173901554593545219 = some 173901554593545219 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 10 2 173901554593545219 173901554593545219 173901554593545219 endpoint_19_34_p10 endpoint_19_34_w10
private theorem endpoint_19_34_w12 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 12 2 173901554593545219 = some 173901554593545219 := by decide +kernel
private theorem endpoint_19_34_p14 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 14 173901554593545219 = some 173901554593545219 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 12 2 173901554593545219 173901554593545219 173901554593545219 endpoint_19_34_p12 endpoint_19_34_w12
private theorem endpoint_19_34_w14 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 14 2 173901554593545219 = some 173901554593545219 := by decide +kernel
private theorem endpoint_19_34_p16 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 16 173901554593545219 = some 173901554593545219 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 14 2 173901554593545219 173901554593545219 173901554593545219 endpoint_19_34_p14 endpoint_19_34_w14
private theorem endpoint_19_34_w16 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 16 2 173901554593545219 = some 173901554593545219 := by decide +kernel
private theorem endpoint_19_34_p18 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 18 173901554593545219 = some 173901554593545219 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 16 2 173901554593545219 173901554593545219 173901554593545219 endpoint_19_34_p16 endpoint_19_34_w16
def endpoint_19_34 : CertifiedEndpoint :=
  ⟨⟨19, 34, 2417⟩, 173901554593545219, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_34_flag endpoint_19_34_sources 18 173901554593545219 173901554593545219 rfl endpoint_19_34_base endpoint_19_34_p18) (by decide)⟩
private def endpoint_19_35_flag : Flag := ⟨19, 35, 2377⟩
private def endpoint_19_35_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_35_base : receiptBase endpoint_19_35_flag endpoint_19_35_sources = some 175323899587467635 := by decide +kernel
private theorem endpoint_19_35_w0 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 2 175323899587467635 = some 175323899587467635 := by decide +kernel
private theorem endpoint_19_35_w2 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 2 2 175323899587467635 = some 175323899587467635 := by decide +kernel
private theorem endpoint_19_35_p4 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 4 175323899587467635 = some 175323899587467635 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 2 2 175323899587467635 175323899587467635 175323899587467635 endpoint_19_35_w0 endpoint_19_35_w2
private theorem endpoint_19_35_w4 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 4 2 175323899587467635 = some 175323899587467635 := by decide +kernel
private theorem endpoint_19_35_p6 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 6 175323899587467635 = some 175323899587467635 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 4 2 175323899587467635 175323899587467635 175323899587467635 endpoint_19_35_p4 endpoint_19_35_w4
private theorem endpoint_19_35_w6 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 6 2 175323899587467635 = some 175323899587467635 := by decide +kernel
private theorem endpoint_19_35_p8 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 8 175323899587467635 = some 175323899587467635 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 6 2 175323899587467635 175323899587467635 175323899587467635 endpoint_19_35_p6 endpoint_19_35_w6
private theorem endpoint_19_35_w8 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 8 2 175323899587467635 = some 175323899587467635 := by decide +kernel
private theorem endpoint_19_35_p10 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 10 175323899587467635 = some 175323899587467635 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 8 2 175323899587467635 175323899587467635 175323899587467635 endpoint_19_35_p8 endpoint_19_35_w8
private theorem endpoint_19_35_w10 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 10 2 175323899587467635 = some 175323899587467635 := by decide +kernel
private theorem endpoint_19_35_p12 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 12 175323899587467635 = some 175323899587467635 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 10 2 175323899587467635 175323899587467635 175323899587467635 endpoint_19_35_p10 endpoint_19_35_w10
private theorem endpoint_19_35_w12 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 12 2 175323899587467635 = some 175323899587467635 := by decide +kernel
private theorem endpoint_19_35_p14 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 14 175323899587467635 = some 175323899587467635 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 12 2 175323899587467635 175323899587467635 175323899587467635 endpoint_19_35_p12 endpoint_19_35_w12
private theorem endpoint_19_35_w14 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 14 2 175323899587467635 = some 175323899587467635 := by decide +kernel
private theorem endpoint_19_35_p16 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 16 175323899587467635 = some 175323899587467635 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 14 2 175323899587467635 175323899587467635 175323899587467635 endpoint_19_35_p14 endpoint_19_35_w14
private theorem endpoint_19_35_w16 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 16 2 175323899587467635 = some 175323899587467635 := by decide +kernel
private theorem endpoint_19_35_p18 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 18 175323899587467635 = some 175323899587467635 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 16 2 175323899587467635 175323899587467635 175323899587467635 endpoint_19_35_p16 endpoint_19_35_w16
def endpoint_19_35 : CertifiedEndpoint :=
  ⟨⟨19, 35, 2377⟩, 175323899587467635, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_35_flag endpoint_19_35_sources 18 175323899587467635 175323899587467635 rfl endpoint_19_35_base endpoint_19_35_p18) (by decide)⟩
private def endpoint_19_36_flag : Flag := ⟨19, 36, 2337⟩
private def endpoint_19_36_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_19_36_base : receiptBase endpoint_19_36_flag endpoint_19_36_sources = some 182107741108560390 := by decide +kernel
private theorem endpoint_19_36_w0 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 2 182107741108560390 = some 182107741108560390 := by decide +kernel
private theorem endpoint_19_36_w2 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 2 2 182107741108560390 = some 182107741108560390 := by decide +kernel
private theorem endpoint_19_36_p4 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 4 182107741108560390 = some 182107741108560390 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 2 2 182107741108560390 182107741108560390 182107741108560390 endpoint_19_36_w0 endpoint_19_36_w2
private theorem endpoint_19_36_w4 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 4 2 182107741108560390 = some 182107741108560390 := by decide +kernel
private theorem endpoint_19_36_p6 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 6 182107741108560390 = some 182107741108560390 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 4 2 182107741108560390 182107741108560390 182107741108560390 endpoint_19_36_p4 endpoint_19_36_w4
private theorem endpoint_19_36_w6 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 6 2 182107741108560390 = some 182107741108560390 := by decide +kernel
private theorem endpoint_19_36_p8 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 8 182107741108560390 = some 182107741108560390 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 6 2 182107741108560390 182107741108560390 182107741108560390 endpoint_19_36_p6 endpoint_19_36_w6
private theorem endpoint_19_36_w8 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 8 2 182107741108560390 = some 182107741108560390 := by decide +kernel
private theorem endpoint_19_36_p10 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 10 182107741108560390 = some 182107741108560390 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 8 2 182107741108560390 182107741108560390 182107741108560390 endpoint_19_36_p8 endpoint_19_36_w8
private theorem endpoint_19_36_w10 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 10 2 182107741108560390 = some 182107741108560390 := by decide +kernel
private theorem endpoint_19_36_p12 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 12 182107741108560390 = some 182107741108560390 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 10 2 182107741108560390 182107741108560390 182107741108560390 endpoint_19_36_p10 endpoint_19_36_w10
private theorem endpoint_19_36_w12 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 12 2 182107741108560390 = some 182107741108560390 := by decide +kernel
private theorem endpoint_19_36_p14 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 14 182107741108560390 = some 182107741108560390 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 12 2 182107741108560390 182107741108560390 182107741108560390 endpoint_19_36_p12 endpoint_19_36_w12
private theorem endpoint_19_36_w14 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 14 2 182107741108560390 = some 182107741108560390 := by decide +kernel
private theorem endpoint_19_36_p16 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 16 182107741108560390 = some 182107741108560390 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 14 2 182107741108560390 182107741108560390 182107741108560390 endpoint_19_36_p14 endpoint_19_36_w14
private theorem endpoint_19_36_w16 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 16 2 182107741108560390 = some 182107741108560390 := by decide +kernel
private theorem endpoint_19_36_p18 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 18 182107741108560390 = some 182107741108560390 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 16 2 182107741108560390 182107741108560390 182107741108560390 endpoint_19_36_p16 endpoint_19_36_w16
def endpoint_19_36 : CertifiedEndpoint :=
  ⟨⟨19, 36, 2337⟩, 182107741108560390, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_19_36_flag endpoint_19_36_sources 18 182107741108560390 182107741108560390 rfl endpoint_19_36_base endpoint_19_36_p18) (by decide)⟩
private def endpoint_19_37_flag : Flag := ⟨19, 37, 2296⟩
private def endpoint_19_37_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_19_37_base : receiptBase endpoint_19_37_flag endpoint_19_37_sources = some 183212470803960771 := by decide +kernel
private theorem endpoint_19_37_w0 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 2 183212470803960771 = some 183212470803960771 := by decide +kernel
private theorem endpoint_19_37_w2 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 2 2 183212470803960771 = some 183212470803960771 := by decide +kernel
private theorem endpoint_19_37_p4 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 4 183212470803960771 = some 183212470803960771 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 2 2 183212470803960771 183212470803960771 183212470803960771 endpoint_19_37_w0 endpoint_19_37_w2
private theorem endpoint_19_37_w4 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 4 2 183212470803960771 = some 183212470803960771 := by decide +kernel
private theorem endpoint_19_37_p6 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 6 183212470803960771 = some 183212470803960771 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 4 2 183212470803960771 183212470803960771 183212470803960771 endpoint_19_37_p4 endpoint_19_37_w4
private theorem endpoint_19_37_w6 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 6 2 183212470803960771 = some 183212470803960771 := by decide +kernel
private theorem endpoint_19_37_p8 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 8 183212470803960771 = some 183212470803960771 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 6 2 183212470803960771 183212470803960771 183212470803960771 endpoint_19_37_p6 endpoint_19_37_w6
private theorem endpoint_19_37_w8 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 8 2 183212470803960771 = some 183212470803960771 := by decide +kernel
private theorem endpoint_19_37_p10 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 10 183212470803960771 = some 183212470803960771 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 8 2 183212470803960771 183212470803960771 183212470803960771 endpoint_19_37_p8 endpoint_19_37_w8
private theorem endpoint_19_37_w10 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 10 2 183212470803960771 = some 183212470803960771 := by decide +kernel
private theorem endpoint_19_37_p12 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 12 183212470803960771 = some 183212470803960771 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 10 2 183212470803960771 183212470803960771 183212470803960771 endpoint_19_37_p10 endpoint_19_37_w10
private theorem endpoint_19_37_w12 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 12 2 183212470803960771 = some 183212470803960771 := by decide +kernel
private theorem endpoint_19_37_p14 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 14 183212470803960771 = some 183212470803960771 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 12 2 183212470803960771 183212470803960771 183212470803960771 endpoint_19_37_p12 endpoint_19_37_w12
private theorem endpoint_19_37_w14 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 14 2 183212470803960771 = some 183212470803960771 := by decide +kernel
private theorem endpoint_19_37_p16 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 16 183212470803960771 = some 183212470803960771 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 14 2 183212470803960771 183212470803960771 183212470803960771 endpoint_19_37_p14 endpoint_19_37_w14
private theorem endpoint_19_37_w16 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 16 2 183212470803960771 = some 183212470803960771 := by decide +kernel
private theorem endpoint_19_37_p18 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 18 183212470803960771 = some 183212470803960771 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 16 2 183212470803960771 183212470803960771 183212470803960771 endpoint_19_37_p16 endpoint_19_37_w16
def endpoint_19_37 : CertifiedEndpoint :=
  ⟨⟨19, 37, 2296⟩, 183212470803960771, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_19_37_flag endpoint_19_37_sources 18 183212470803960771 183212470803960771 rfl endpoint_19_37_base endpoint_19_37_p18) (by decide)⟩
private def endpoint_19_38_flag : Flag := ⟨19, 38, 2254⟩
private def endpoint_19_38_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_38_base : receiptBase endpoint_19_38_flag endpoint_19_38_sources = some 184617205665404088 := by decide +kernel
private theorem endpoint_19_38_w0 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 2 184617205665404088 = some 184617205665404088 := by decide +kernel
private theorem endpoint_19_38_w2 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 2 2 184617205665404088 = some 184617205665404088 := by decide +kernel
private theorem endpoint_19_38_p4 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 4 184617205665404088 = some 184617205665404088 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 2 2 184617205665404088 184617205665404088 184617205665404088 endpoint_19_38_w0 endpoint_19_38_w2
private theorem endpoint_19_38_w4 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 4 2 184617205665404088 = some 184617205665404088 := by decide +kernel
private theorem endpoint_19_38_p6 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 6 184617205665404088 = some 184617205665404088 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 4 2 184617205665404088 184617205665404088 184617205665404088 endpoint_19_38_p4 endpoint_19_38_w4
private theorem endpoint_19_38_w6 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 6 2 184617205665404088 = some 184617205665404088 := by decide +kernel
private theorem endpoint_19_38_p8 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 8 184617205665404088 = some 184617205665404088 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 6 2 184617205665404088 184617205665404088 184617205665404088 endpoint_19_38_p6 endpoint_19_38_w6
private theorem endpoint_19_38_w8 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 8 2 184617205665404088 = some 184617205665404088 := by decide +kernel
private theorem endpoint_19_38_p10 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 10 184617205665404088 = some 184617205665404088 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 8 2 184617205665404088 184617205665404088 184617205665404088 endpoint_19_38_p8 endpoint_19_38_w8
private theorem endpoint_19_38_w10 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 10 2 184617205665404088 = some 184617205665404088 := by decide +kernel
private theorem endpoint_19_38_p12 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 12 184617205665404088 = some 184617205665404088 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 10 2 184617205665404088 184617205665404088 184617205665404088 endpoint_19_38_p10 endpoint_19_38_w10
private theorem endpoint_19_38_w12 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 12 2 184617205665404088 = some 184617205665404088 := by decide +kernel
private theorem endpoint_19_38_p14 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 14 184617205665404088 = some 184617205665404088 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 12 2 184617205665404088 184617205665404088 184617205665404088 endpoint_19_38_p12 endpoint_19_38_w12
private theorem endpoint_19_38_w14 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 14 2 184617205665404088 = some 184617205665404088 := by decide +kernel
private theorem endpoint_19_38_p16 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 16 184617205665404088 = some 184617205665404088 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 14 2 184617205665404088 184617205665404088 184617205665404088 endpoint_19_38_p14 endpoint_19_38_w14
private theorem endpoint_19_38_w16 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 16 2 184617205665404088 = some 184617205665404088 := by decide +kernel
private theorem endpoint_19_38_p18 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 18 184617205665404088 = some 184617205665404088 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 16 2 184617205665404088 184617205665404088 184617205665404088 endpoint_19_38_p16 endpoint_19_38_w16
def endpoint_19_38 : CertifiedEndpoint :=
  ⟨⟨19, 38, 2254⟩, 184617205665404088, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_38_flag endpoint_19_38_sources 18 184617205665404088 184617205665404088 rfl endpoint_19_38_base endpoint_19_38_p18) (by decide)⟩
private def endpoint_19_39_flag : Flag := ⟨19, 39, 2211⟩
private def endpoint_19_39_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_39_base : receiptBase endpoint_19_39_flag endpoint_19_39_sources = some 185271834846811839 := by decide +kernel
private theorem endpoint_19_39_w0 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 2 185271834846811839 = some 185271834846811839 := by decide +kernel
private theorem endpoint_19_39_w2 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 2 2 185271834846811839 = some 185271834846811839 := by decide +kernel
private theorem endpoint_19_39_p4 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 4 185271834846811839 = some 185271834846811839 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 2 2 185271834846811839 185271834846811839 185271834846811839 endpoint_19_39_w0 endpoint_19_39_w2
private theorem endpoint_19_39_w4 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 4 2 185271834846811839 = some 185271834846811839 := by decide +kernel
private theorem endpoint_19_39_p6 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 6 185271834846811839 = some 185271834846811839 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 4 2 185271834846811839 185271834846811839 185271834846811839 endpoint_19_39_p4 endpoint_19_39_w4
private theorem endpoint_19_39_w6 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 6 2 185271834846811839 = some 185271834846811839 := by decide +kernel
private theorem endpoint_19_39_p8 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 8 185271834846811839 = some 185271834846811839 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 6 2 185271834846811839 185271834846811839 185271834846811839 endpoint_19_39_p6 endpoint_19_39_w6
private theorem endpoint_19_39_w8 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 8 2 185271834846811839 = some 185271834846811839 := by decide +kernel
private theorem endpoint_19_39_p10 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 10 185271834846811839 = some 185271834846811839 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 8 2 185271834846811839 185271834846811839 185271834846811839 endpoint_19_39_p8 endpoint_19_39_w8
private theorem endpoint_19_39_w10 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 10 2 185271834846811839 = some 185271834846811839 := by decide +kernel
private theorem endpoint_19_39_p12 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 12 185271834846811839 = some 185271834846811839 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 10 2 185271834846811839 185271834846811839 185271834846811839 endpoint_19_39_p10 endpoint_19_39_w10
private theorem endpoint_19_39_w12 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 12 2 185271834846811839 = some 185271834846811839 := by decide +kernel
private theorem endpoint_19_39_p14 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 14 185271834846811839 = some 185271834846811839 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 12 2 185271834846811839 185271834846811839 185271834846811839 endpoint_19_39_p12 endpoint_19_39_w12
private theorem endpoint_19_39_w14 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 14 2 185271834846811839 = some 185271834846811839 := by decide +kernel
private theorem endpoint_19_39_p16 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 16 185271834846811839 = some 185271834846811839 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 14 2 185271834846811839 185271834846811839 185271834846811839 endpoint_19_39_p14 endpoint_19_39_w14
private theorem endpoint_19_39_w16 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 16 2 185271834846811839 = some 185271834846811839 := by decide +kernel
private theorem endpoint_19_39_p18 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 18 185271834846811839 = some 185271834846811839 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 16 2 185271834846811839 185271834846811839 185271834846811839 endpoint_19_39_p16 endpoint_19_39_w16
def endpoint_19_39 : CertifiedEndpoint :=
  ⟨⟨19, 39, 2211⟩, 185271834846811839, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_39_flag endpoint_19_39_sources 18 185271834846811839 185271834846811839 rfl endpoint_19_39_base endpoint_19_39_p18) (by decide)⟩
private def endpoint_19_40_flag : Flag := ⟨19, 40, 2168⟩
private def endpoint_19_40_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_40_base : receiptBase endpoint_19_40_flag endpoint_19_40_sources = some 185770457548569793 := by decide +kernel
private theorem endpoint_19_40_w0 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 2 185770457548569793 = some 185770457548569793 := by decide +kernel
private theorem endpoint_19_40_w2 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 2 2 185770457548569793 = some 185770457548569793 := by decide +kernel
private theorem endpoint_19_40_p4 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 4 185770457548569793 = some 185770457548569793 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 2 2 185770457548569793 185770457548569793 185770457548569793 endpoint_19_40_w0 endpoint_19_40_w2
private theorem endpoint_19_40_w4 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 4 2 185770457548569793 = some 185770457548569793 := by decide +kernel
private theorem endpoint_19_40_p6 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 6 185770457548569793 = some 185770457548569793 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 4 2 185770457548569793 185770457548569793 185770457548569793 endpoint_19_40_p4 endpoint_19_40_w4
private theorem endpoint_19_40_w6 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 6 2 185770457548569793 = some 185770457548569793 := by decide +kernel
private theorem endpoint_19_40_p8 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 8 185770457548569793 = some 185770457548569793 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 6 2 185770457548569793 185770457548569793 185770457548569793 endpoint_19_40_p6 endpoint_19_40_w6
private theorem endpoint_19_40_w8 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 8 2 185770457548569793 = some 185770457548569793 := by decide +kernel
private theorem endpoint_19_40_p10 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 10 185770457548569793 = some 185770457548569793 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 8 2 185770457548569793 185770457548569793 185770457548569793 endpoint_19_40_p8 endpoint_19_40_w8
private theorem endpoint_19_40_w10 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 10 2 185770457548569793 = some 185770457548569793 := by decide +kernel
private theorem endpoint_19_40_p12 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 12 185770457548569793 = some 185770457548569793 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 10 2 185770457548569793 185770457548569793 185770457548569793 endpoint_19_40_p10 endpoint_19_40_w10
private theorem endpoint_19_40_w12 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 12 2 185770457548569793 = some 185770457548569793 := by decide +kernel
private theorem endpoint_19_40_p14 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 14 185770457548569793 = some 185770457548569793 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 12 2 185770457548569793 185770457548569793 185770457548569793 endpoint_19_40_p12 endpoint_19_40_w12
private theorem endpoint_19_40_w14 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 14 2 185770457548569793 = some 185770457548569793 := by decide +kernel
private theorem endpoint_19_40_p16 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 16 185770457548569793 = some 185770457548569793 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 14 2 185770457548569793 185770457548569793 185770457548569793 endpoint_19_40_p14 endpoint_19_40_w14
private theorem endpoint_19_40_w16 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 16 2 185770457548569793 = some 185770457548569793 := by decide +kernel
private theorem endpoint_19_40_p18 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 18 185770457548569793 = some 185770457548569793 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 16 2 185770457548569793 185770457548569793 185770457548569793 endpoint_19_40_p16 endpoint_19_40_w16
def endpoint_19_40 : CertifiedEndpoint :=
  ⟨⟨19, 40, 2168⟩, 185770457548569793, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_40_flag endpoint_19_40_sources 18 185770457548569793 185770457548569793 rfl endpoint_19_40_base endpoint_19_40_p18) (by decide)⟩
private def endpoint_19_41_flag : Flag := ⟨19, 41, 2124⟩
private def endpoint_19_41_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_41_base : receiptBase endpoint_19_41_flag endpoint_19_41_sources = some 186027676695483369 := by decide +kernel
private theorem endpoint_19_41_w0 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 2 186027676695483369 = some 186027676695483369 := by decide +kernel
private theorem endpoint_19_41_w2 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 2 2 186027676695483369 = some 186027676695483369 := by decide +kernel
private theorem endpoint_19_41_p4 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 4 186027676695483369 = some 186027676695483369 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 2 2 186027676695483369 186027676695483369 186027676695483369 endpoint_19_41_w0 endpoint_19_41_w2
private theorem endpoint_19_41_w4 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 4 2 186027676695483369 = some 186027676695483369 := by decide +kernel
private theorem endpoint_19_41_p6 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 6 186027676695483369 = some 186027676695483369 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 4 2 186027676695483369 186027676695483369 186027676695483369 endpoint_19_41_p4 endpoint_19_41_w4
private theorem endpoint_19_41_w6 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 6 2 186027676695483369 = some 186027676695483369 := by decide +kernel
private theorem endpoint_19_41_p8 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 8 186027676695483369 = some 186027676695483369 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 6 2 186027676695483369 186027676695483369 186027676695483369 endpoint_19_41_p6 endpoint_19_41_w6
private theorem endpoint_19_41_w8 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 8 2 186027676695483369 = some 186027676695483369 := by decide +kernel
private theorem endpoint_19_41_p10 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 10 186027676695483369 = some 186027676695483369 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 8 2 186027676695483369 186027676695483369 186027676695483369 endpoint_19_41_p8 endpoint_19_41_w8
private theorem endpoint_19_41_w10 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 10 2 186027676695483369 = some 186027676695483369 := by decide +kernel
private theorem endpoint_19_41_p12 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 12 186027676695483369 = some 186027676695483369 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 10 2 186027676695483369 186027676695483369 186027676695483369 endpoint_19_41_p10 endpoint_19_41_w10
private theorem endpoint_19_41_w12 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 12 2 186027676695483369 = some 186027676695483369 := by decide +kernel
private theorem endpoint_19_41_p14 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 14 186027676695483369 = some 186027676695483369 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 12 2 186027676695483369 186027676695483369 186027676695483369 endpoint_19_41_p12 endpoint_19_41_w12
private theorem endpoint_19_41_w14 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 14 2 186027676695483369 = some 186027676695483369 := by decide +kernel
private theorem endpoint_19_41_p16 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 16 186027676695483369 = some 186027676695483369 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 14 2 186027676695483369 186027676695483369 186027676695483369 endpoint_19_41_p14 endpoint_19_41_w14
private theorem endpoint_19_41_w16 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 16 2 186027676695483369 = some 186027676695483369 := by decide +kernel
private theorem endpoint_19_41_p18 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 18 186027676695483369 = some 186027676695483369 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 16 2 186027676695483369 186027676695483369 186027676695483369 endpoint_19_41_p16 endpoint_19_41_w16
def endpoint_19_41 : CertifiedEndpoint :=
  ⟨⟨19, 41, 2124⟩, 186027676695483369, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_41_flag endpoint_19_41_sources 18 186027676695483369 186027676695483369 rfl endpoint_19_41_base endpoint_19_41_p18) (by decide)⟩
private def endpoint_19_42_flag : Flag := ⟨19, 42, 2079⟩
private def endpoint_19_42_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_42_base : receiptBase endpoint_19_42_flag endpoint_19_42_sources = some 186038112482243650 := by decide +kernel
private theorem endpoint_19_42_w0 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 2 186038112482243650 = some 186038112482243650 := by decide +kernel
private theorem endpoint_19_42_w2 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 2 2 186038112482243650 = some 186038112482243650 := by decide +kernel
private theorem endpoint_19_42_p4 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 4 186038112482243650 = some 186038112482243650 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 2 2 186038112482243650 186038112482243650 186038112482243650 endpoint_19_42_w0 endpoint_19_42_w2
private theorem endpoint_19_42_w4 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 4 2 186038112482243650 = some 186038112482243650 := by decide +kernel
private theorem endpoint_19_42_p6 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 6 186038112482243650 = some 186038112482243650 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 4 2 186038112482243650 186038112482243650 186038112482243650 endpoint_19_42_p4 endpoint_19_42_w4
private theorem endpoint_19_42_w6 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 6 2 186038112482243650 = some 186038112482243650 := by decide +kernel
private theorem endpoint_19_42_p8 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 8 186038112482243650 = some 186038112482243650 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 6 2 186038112482243650 186038112482243650 186038112482243650 endpoint_19_42_p6 endpoint_19_42_w6
private theorem endpoint_19_42_w8 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 8 2 186038112482243650 = some 186038112482243650 := by decide +kernel
private theorem endpoint_19_42_p10 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 10 186038112482243650 = some 186038112482243650 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 8 2 186038112482243650 186038112482243650 186038112482243650 endpoint_19_42_p8 endpoint_19_42_w8
private theorem endpoint_19_42_w10 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 10 2 186038112482243650 = some 186038112482243650 := by decide +kernel
private theorem endpoint_19_42_p12 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 12 186038112482243650 = some 186038112482243650 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 10 2 186038112482243650 186038112482243650 186038112482243650 endpoint_19_42_p10 endpoint_19_42_w10
private theorem endpoint_19_42_w12 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 12 2 186038112482243650 = some 186038112482243650 := by decide +kernel
private theorem endpoint_19_42_p14 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 14 186038112482243650 = some 186038112482243650 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 12 2 186038112482243650 186038112482243650 186038112482243650 endpoint_19_42_p12 endpoint_19_42_w12
private theorem endpoint_19_42_w14 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 14 2 186038112482243650 = some 186038112482243650 := by decide +kernel
private theorem endpoint_19_42_p16 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 16 186038112482243650 = some 186038112482243650 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 14 2 186038112482243650 186038112482243650 186038112482243650 endpoint_19_42_p14 endpoint_19_42_w14
private theorem endpoint_19_42_w16 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 16 2 186038112482243650 = some 186038112482243650 := by decide +kernel
private theorem endpoint_19_42_p18 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 18 186038112482243650 = some 186038112482243650 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 16 2 186038112482243650 186038112482243650 186038112482243650 endpoint_19_42_p16 endpoint_19_42_w16
def endpoint_19_42 : CertifiedEndpoint :=
  ⟨⟨19, 42, 2079⟩, 186038112482243650, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_42_flag endpoint_19_42_sources 18 186038112482243650 186038112482243650 rfl endpoint_19_42_base endpoint_19_42_p18) (by decide)⟩
private def endpoint_19_43_flag : Flag := ⟨19, 43, 2034⟩
private def endpoint_19_43_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_43_base : receiptBase endpoint_19_43_flag endpoint_19_43_sources = some 185885368715608913 := by decide +kernel
private theorem endpoint_19_43_w0 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 2 185885368715608913 = some 185885368715608913 := by decide +kernel
private theorem endpoint_19_43_w2 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 2 2 185885368715608913 = some 185885368715608913 := by decide +kernel
private theorem endpoint_19_43_p4 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 4 185885368715608913 = some 185885368715608913 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 2 2 185885368715608913 185885368715608913 185885368715608913 endpoint_19_43_w0 endpoint_19_43_w2
private theorem endpoint_19_43_w4 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 4 2 185885368715608913 = some 185885368715608913 := by decide +kernel
private theorem endpoint_19_43_p6 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 6 185885368715608913 = some 185885368715608913 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 4 2 185885368715608913 185885368715608913 185885368715608913 endpoint_19_43_p4 endpoint_19_43_w4
private theorem endpoint_19_43_w6 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 6 2 185885368715608913 = some 185885368715608913 := by decide +kernel
private theorem endpoint_19_43_p8 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 8 185885368715608913 = some 185885368715608913 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 6 2 185885368715608913 185885368715608913 185885368715608913 endpoint_19_43_p6 endpoint_19_43_w6
private theorem endpoint_19_43_w8 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 8 2 185885368715608913 = some 185885368715608913 := by decide +kernel
private theorem endpoint_19_43_p10 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 10 185885368715608913 = some 185885368715608913 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 8 2 185885368715608913 185885368715608913 185885368715608913 endpoint_19_43_p8 endpoint_19_43_w8
private theorem endpoint_19_43_w10 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 10 2 185885368715608913 = some 185885368715608913 := by decide +kernel
private theorem endpoint_19_43_p12 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 12 185885368715608913 = some 185885368715608913 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 10 2 185885368715608913 185885368715608913 185885368715608913 endpoint_19_43_p10 endpoint_19_43_w10
private theorem endpoint_19_43_w12 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 12 2 185885368715608913 = some 185885368715608913 := by decide +kernel
private theorem endpoint_19_43_p14 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 14 185885368715608913 = some 185885368715608913 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 12 2 185885368715608913 185885368715608913 185885368715608913 endpoint_19_43_p12 endpoint_19_43_w12
private theorem endpoint_19_43_w14 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 14 2 185885368715608913 = some 185885368715608913 := by decide +kernel
private theorem endpoint_19_43_p16 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 16 185885368715608913 = some 185885368715608913 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 14 2 185885368715608913 185885368715608913 185885368715608913 endpoint_19_43_p14 endpoint_19_43_w14
private theorem endpoint_19_43_w16 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 16 2 185885368715608913 = some 185885368715608913 := by decide +kernel
private theorem endpoint_19_43_p18 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 18 185885368715608913 = some 185885368715608913 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 16 2 185885368715608913 185885368715608913 185885368715608913 endpoint_19_43_p16 endpoint_19_43_w16
def endpoint_19_43 : CertifiedEndpoint :=
  ⟨⟨19, 43, 2034⟩, 185885368715608913, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_43_flag endpoint_19_43_sources 18 185885368715608913 185885368715608913 rfl endpoint_19_43_base endpoint_19_43_p18) (by decide)⟩
private def endpoint_19_44_flag : Flag := ⟨19, 44, 1988⟩
private def endpoint_19_44_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_44_base : receiptBase endpoint_19_44_flag endpoint_19_44_sources = some 185478668515075659 := by decide +kernel
private theorem endpoint_19_44_w0 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 2 185478668515075659 = some 185478668515075659 := by decide +kernel
private theorem endpoint_19_44_w2 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 2 2 185478668515075659 = some 185478668515075659 := by decide +kernel
private theorem endpoint_19_44_p4 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 4 185478668515075659 = some 185478668515075659 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 2 2 185478668515075659 185478668515075659 185478668515075659 endpoint_19_44_w0 endpoint_19_44_w2
private theorem endpoint_19_44_w4 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 4 2 185478668515075659 = some 185478668515075659 := by decide +kernel
private theorem endpoint_19_44_p6 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 6 185478668515075659 = some 185478668515075659 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 4 2 185478668515075659 185478668515075659 185478668515075659 endpoint_19_44_p4 endpoint_19_44_w4
private theorem endpoint_19_44_w6 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 6 2 185478668515075659 = some 185478668515075659 := by decide +kernel
private theorem endpoint_19_44_p8 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 8 185478668515075659 = some 185478668515075659 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 6 2 185478668515075659 185478668515075659 185478668515075659 endpoint_19_44_p6 endpoint_19_44_w6
private theorem endpoint_19_44_w8 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 8 2 185478668515075659 = some 185478668515075659 := by decide +kernel
private theorem endpoint_19_44_p10 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 10 185478668515075659 = some 185478668515075659 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 8 2 185478668515075659 185478668515075659 185478668515075659 endpoint_19_44_p8 endpoint_19_44_w8
private theorem endpoint_19_44_w10 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 10 2 185478668515075659 = some 185478668515075659 := by decide +kernel
private theorem endpoint_19_44_p12 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 12 185478668515075659 = some 185478668515075659 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 10 2 185478668515075659 185478668515075659 185478668515075659 endpoint_19_44_p10 endpoint_19_44_w10
private theorem endpoint_19_44_w12 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 12 2 185478668515075659 = some 185478668515075659 := by decide +kernel
private theorem endpoint_19_44_p14 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 14 185478668515075659 = some 185478668515075659 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 12 2 185478668515075659 185478668515075659 185478668515075659 endpoint_19_44_p12 endpoint_19_44_w12
private theorem endpoint_19_44_w14 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 14 2 185478668515075659 = some 185478668515075659 := by decide +kernel
private theorem endpoint_19_44_p16 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 16 185478668515075659 = some 185478668515075659 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 14 2 185478668515075659 185478668515075659 185478668515075659 endpoint_19_44_p14 endpoint_19_44_w14
private theorem endpoint_19_44_w16 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 16 2 185478668515075659 = some 185478668515075659 := by decide +kernel
private theorem endpoint_19_44_p18 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 18 185478668515075659 = some 185478668515075659 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 16 2 185478668515075659 185478668515075659 185478668515075659 endpoint_19_44_p16 endpoint_19_44_w16
def endpoint_19_44 : CertifiedEndpoint :=
  ⟨⟨19, 44, 1988⟩, 185478668515075659, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_44_flag endpoint_19_44_sources 18 185478668515075659 185478668515075659 rfl endpoint_19_44_base endpoint_19_44_p18) (by decide)⟩
private def endpoint_19_45_flag : Flag := ⟨19, 45, 1941⟩
private def endpoint_19_45_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_45_base : receiptBase endpoint_19_45_flag endpoint_19_45_sources = some 186812328971768099 := by decide +kernel
private theorem endpoint_19_45_w0 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 2 186812328971768099 = some 186812328971768099 := by decide +kernel
private theorem endpoint_19_45_w2 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 2 2 186812328971768099 = some 186812328971768099 := by decide +kernel
private theorem endpoint_19_45_p4 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 4 186812328971768099 = some 186812328971768099 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 2 2 186812328971768099 186812328971768099 186812328971768099 endpoint_19_45_w0 endpoint_19_45_w2
private theorem endpoint_19_45_w4 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 4 2 186812328971768099 = some 186812328971768099 := by decide +kernel
private theorem endpoint_19_45_p6 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 6 186812328971768099 = some 186812328971768099 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 4 2 186812328971768099 186812328971768099 186812328971768099 endpoint_19_45_p4 endpoint_19_45_w4
private theorem endpoint_19_45_w6 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 6 2 186812328971768099 = some 186812328971768099 := by decide +kernel
private theorem endpoint_19_45_p8 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 8 186812328971768099 = some 186812328971768099 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 6 2 186812328971768099 186812328971768099 186812328971768099 endpoint_19_45_p6 endpoint_19_45_w6
private theorem endpoint_19_45_w8 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 8 2 186812328971768099 = some 186812328971768099 := by decide +kernel
private theorem endpoint_19_45_p10 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 10 186812328971768099 = some 186812328971768099 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 8 2 186812328971768099 186812328971768099 186812328971768099 endpoint_19_45_p8 endpoint_19_45_w8
private theorem endpoint_19_45_w10 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 10 2 186812328971768099 = some 186812328971768099 := by decide +kernel
private theorem endpoint_19_45_p12 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 12 186812328971768099 = some 186812328971768099 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 10 2 186812328971768099 186812328971768099 186812328971768099 endpoint_19_45_p10 endpoint_19_45_w10
private theorem endpoint_19_45_w12 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 12 2 186812328971768099 = some 186812328971768099 := by decide +kernel
private theorem endpoint_19_45_p14 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 14 186812328971768099 = some 186812328971768099 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 12 2 186812328971768099 186812328971768099 186812328971768099 endpoint_19_45_p12 endpoint_19_45_w12
private theorem endpoint_19_45_w14 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 14 2 186812328971768099 = some 186812328971768099 := by decide +kernel
private theorem endpoint_19_45_p16 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 16 186812328971768099 = some 186812328971768099 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 14 2 186812328971768099 186812328971768099 186812328971768099 endpoint_19_45_p14 endpoint_19_45_w14
private theorem endpoint_19_45_w16 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 16 2 186812328971768099 = some 186812328971768099 := by decide +kernel
private theorem endpoint_19_45_p18 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 18 186812328971768099 = some 186812328971768099 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 16 2 186812328971768099 186812328971768099 186812328971768099 endpoint_19_45_p16 endpoint_19_45_w16
def endpoint_19_45 : CertifiedEndpoint :=
  ⟨⟨19, 45, 1941⟩, 186812328971768099, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_45_flag endpoint_19_45_sources 18 186812328971768099 186812328971768099 rfl endpoint_19_45_base endpoint_19_45_p18) (by decide)⟩
private def endpoint_19_46_flag : Flag := ⟨19, 46, 1893⟩
private def endpoint_19_46_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_46_base : receiptBase endpoint_19_46_flag endpoint_19_46_sources = some 185822278261335652 := by decide +kernel
private theorem endpoint_19_46_w0 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 2 185822278261335652 = some 185822278261335652 := by decide +kernel
private theorem endpoint_19_46_w2 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 2 2 185822278261335652 = some 185822278261335652 := by decide +kernel
private theorem endpoint_19_46_p4 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 4 185822278261335652 = some 185822278261335652 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 2 2 185822278261335652 185822278261335652 185822278261335652 endpoint_19_46_w0 endpoint_19_46_w2
private theorem endpoint_19_46_w4 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 4 2 185822278261335652 = some 185822278261335652 := by decide +kernel
private theorem endpoint_19_46_p6 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 6 185822278261335652 = some 185822278261335652 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 4 2 185822278261335652 185822278261335652 185822278261335652 endpoint_19_46_p4 endpoint_19_46_w4
private theorem endpoint_19_46_w6 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 6 2 185822278261335652 = some 185822278261335652 := by decide +kernel
private theorem endpoint_19_46_p8 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 8 185822278261335652 = some 185822278261335652 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 6 2 185822278261335652 185822278261335652 185822278261335652 endpoint_19_46_p6 endpoint_19_46_w6
private theorem endpoint_19_46_w8 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 8 2 185822278261335652 = some 185822278261335652 := by decide +kernel
private theorem endpoint_19_46_p10 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 10 185822278261335652 = some 185822278261335652 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 8 2 185822278261335652 185822278261335652 185822278261335652 endpoint_19_46_p8 endpoint_19_46_w8
private theorem endpoint_19_46_w10 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 10 2 185822278261335652 = some 185822278261335652 := by decide +kernel
private theorem endpoint_19_46_p12 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 12 185822278261335652 = some 185822278261335652 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 10 2 185822278261335652 185822278261335652 185822278261335652 endpoint_19_46_p10 endpoint_19_46_w10
private theorem endpoint_19_46_w12 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 12 2 185822278261335652 = some 185822278261335652 := by decide +kernel
private theorem endpoint_19_46_p14 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 14 185822278261335652 = some 185822278261335652 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 12 2 185822278261335652 185822278261335652 185822278261335652 endpoint_19_46_p12 endpoint_19_46_w12
private theorem endpoint_19_46_w14 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 14 2 185822278261335652 = some 185822278261335652 := by decide +kernel
private theorem endpoint_19_46_p16 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 16 185822278261335652 = some 185822278261335652 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 14 2 185822278261335652 185822278261335652 185822278261335652 endpoint_19_46_p14 endpoint_19_46_w14
private theorem endpoint_19_46_w16 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 16 2 185822278261335652 = some 185822278261335652 := by decide +kernel
private theorem endpoint_19_46_p18 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 18 185822278261335652 = some 185822278261335652 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 16 2 185822278261335652 185822278261335652 185822278261335652 endpoint_19_46_p16 endpoint_19_46_w16
def endpoint_19_46 : CertifiedEndpoint :=
  ⟨⟨19, 46, 1893⟩, 185822278261335652, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_46_flag endpoint_19_46_sources 18 185822278261335652 185822278261335652 rfl endpoint_19_46_base endpoint_19_46_p18) (by decide)⟩
private def endpoint_19_47_flag : Flag := ⟨19, 47, 1844⟩
private def endpoint_19_47_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_47_base : receiptBase endpoint_19_47_flag endpoint_19_47_sources = some 184557324879673783 := by decide +kernel
private theorem endpoint_19_47_w0 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 2 184557324879673783 = some 184557324879673783 := by decide +kernel
private theorem endpoint_19_47_w2 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 2 2 184557324879673783 = some 184557324879673783 := by decide +kernel
private theorem endpoint_19_47_p4 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 4 184557324879673783 = some 184557324879673783 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 2 2 184557324879673783 184557324879673783 184557324879673783 endpoint_19_47_w0 endpoint_19_47_w2
private theorem endpoint_19_47_w4 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 4 2 184557324879673783 = some 184557324879673783 := by decide +kernel
private theorem endpoint_19_47_p6 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 6 184557324879673783 = some 184557324879673783 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 4 2 184557324879673783 184557324879673783 184557324879673783 endpoint_19_47_p4 endpoint_19_47_w4
private theorem endpoint_19_47_w6 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 6 2 184557324879673783 = some 184557324879673783 := by decide +kernel
private theorem endpoint_19_47_p8 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 8 184557324879673783 = some 184557324879673783 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 6 2 184557324879673783 184557324879673783 184557324879673783 endpoint_19_47_p6 endpoint_19_47_w6
private theorem endpoint_19_47_w8 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 8 2 184557324879673783 = some 184557324879673783 := by decide +kernel
private theorem endpoint_19_47_p10 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 10 184557324879673783 = some 184557324879673783 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 8 2 184557324879673783 184557324879673783 184557324879673783 endpoint_19_47_p8 endpoint_19_47_w8
private theorem endpoint_19_47_w10 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 10 2 184557324879673783 = some 184557324879673783 := by decide +kernel
private theorem endpoint_19_47_p12 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 12 184557324879673783 = some 184557324879673783 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 10 2 184557324879673783 184557324879673783 184557324879673783 endpoint_19_47_p10 endpoint_19_47_w10
private theorem endpoint_19_47_w12 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 12 2 184557324879673783 = some 184557324879673783 := by decide +kernel
private theorem endpoint_19_47_p14 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 14 184557324879673783 = some 184557324879673783 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 12 2 184557324879673783 184557324879673783 184557324879673783 endpoint_19_47_p12 endpoint_19_47_w12
private theorem endpoint_19_47_w14 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 14 2 184557324879673783 = some 184557324879673783 := by decide +kernel
private theorem endpoint_19_47_p16 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 16 184557324879673783 = some 184557324879673783 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 14 2 184557324879673783 184557324879673783 184557324879673783 endpoint_19_47_p14 endpoint_19_47_w14
private theorem endpoint_19_47_w16 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 16 2 184557324879673783 = some 184557324879673783 := by decide +kernel
private theorem endpoint_19_47_p18 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 18 184557324879673783 = some 184557324879673783 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 16 2 184557324879673783 184557324879673783 184557324879673783 endpoint_19_47_p16 endpoint_19_47_w16
def endpoint_19_47 : CertifiedEndpoint :=
  ⟨⟨19, 47, 1844⟩, 184557324879673783, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_47_flag endpoint_19_47_sources 18 184557324879673783 184557324879673783 rfl endpoint_19_47_base endpoint_19_47_p18) (by decide)⟩
private def endpoint_19_48_flag : Flag := ⟨19, 48, 1794⟩
private def endpoint_19_48_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_48_base : receiptBase endpoint_19_48_flag endpoint_19_48_sources = some 183011994518375823 := by decide +kernel
private theorem endpoint_19_48_w0 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 2 183011994518375823 = some 183011994518375823 := by decide +kernel
private theorem endpoint_19_48_w2 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 2 2 183011994518375823 = some 183011994518375823 := by decide +kernel
private theorem endpoint_19_48_p4 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 4 183011994518375823 = some 183011994518375823 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 2 2 183011994518375823 183011994518375823 183011994518375823 endpoint_19_48_w0 endpoint_19_48_w2
private theorem endpoint_19_48_w4 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 4 2 183011994518375823 = some 183011994518375823 := by decide +kernel
private theorem endpoint_19_48_p6 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 6 183011994518375823 = some 183011994518375823 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 4 2 183011994518375823 183011994518375823 183011994518375823 endpoint_19_48_p4 endpoint_19_48_w4
private theorem endpoint_19_48_w6 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 6 2 183011994518375823 = some 183011994518375823 := by decide +kernel
private theorem endpoint_19_48_p8 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 8 183011994518375823 = some 183011994518375823 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 6 2 183011994518375823 183011994518375823 183011994518375823 endpoint_19_48_p6 endpoint_19_48_w6
private theorem endpoint_19_48_w8 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 8 2 183011994518375823 = some 183011994518375823 := by decide +kernel
private theorem endpoint_19_48_p10 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 10 183011994518375823 = some 183011994518375823 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 8 2 183011994518375823 183011994518375823 183011994518375823 endpoint_19_48_p8 endpoint_19_48_w8
private theorem endpoint_19_48_w10 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 10 2 183011994518375823 = some 183011994518375823 := by decide +kernel
private theorem endpoint_19_48_p12 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 12 183011994518375823 = some 183011994518375823 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 10 2 183011994518375823 183011994518375823 183011994518375823 endpoint_19_48_p10 endpoint_19_48_w10
private theorem endpoint_19_48_w12 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 12 2 183011994518375823 = some 183011994518375823 := by decide +kernel
private theorem endpoint_19_48_p14 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 14 183011994518375823 = some 183011994518375823 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 12 2 183011994518375823 183011994518375823 183011994518375823 endpoint_19_48_p12 endpoint_19_48_w12
private theorem endpoint_19_48_w14 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 14 2 183011994518375823 = some 183011994518375823 := by decide +kernel
private theorem endpoint_19_48_p16 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 16 183011994518375823 = some 183011994518375823 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 14 2 183011994518375823 183011994518375823 183011994518375823 endpoint_19_48_p14 endpoint_19_48_w14
private theorem endpoint_19_48_w16 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 16 2 183011994518375823 = some 183011994518375823 := by decide +kernel
private theorem endpoint_19_48_p18 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 18 183011994518375823 = some 183011994518375823 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 16 2 183011994518375823 183011994518375823 183011994518375823 endpoint_19_48_p16 endpoint_19_48_w16
def endpoint_19_48 : CertifiedEndpoint :=
  ⟨⟨19, 48, 1794⟩, 183011994518375823, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_48_flag endpoint_19_48_sources 18 183011994518375823 183011994518375823 rfl endpoint_19_48_base endpoint_19_48_p18) (by decide)⟩
private def endpoint_19_49_flag : Flag := ⟨19, 49, 1744⟩
private def endpoint_19_49_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_49_base : receiptBase endpoint_19_49_flag endpoint_19_49_sources = some 183309414547048914 := by decide +kernel
private theorem endpoint_19_49_w0 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 2 183309414547048914 = some 183309414547048914 := by decide +kernel
private theorem endpoint_19_49_w2 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 2 2 183309414547048914 = some 183309414547048914 := by decide +kernel
private theorem endpoint_19_49_p4 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 4 183309414547048914 = some 183309414547048914 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 2 2 183309414547048914 183309414547048914 183309414547048914 endpoint_19_49_w0 endpoint_19_49_w2
private theorem endpoint_19_49_w4 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 4 2 183309414547048914 = some 183309414547048914 := by decide +kernel
private theorem endpoint_19_49_p6 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 6 183309414547048914 = some 183309414547048914 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 4 2 183309414547048914 183309414547048914 183309414547048914 endpoint_19_49_p4 endpoint_19_49_w4
private theorem endpoint_19_49_w6 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 6 2 183309414547048914 = some 183309414547048914 := by decide +kernel
private theorem endpoint_19_49_p8 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 8 183309414547048914 = some 183309414547048914 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 6 2 183309414547048914 183309414547048914 183309414547048914 endpoint_19_49_p6 endpoint_19_49_w6
private theorem endpoint_19_49_w8 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 8 2 183309414547048914 = some 183309414547048914 := by decide +kernel
private theorem endpoint_19_49_p10 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 10 183309414547048914 = some 183309414547048914 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 8 2 183309414547048914 183309414547048914 183309414547048914 endpoint_19_49_p8 endpoint_19_49_w8
private theorem endpoint_19_49_w10 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 10 2 183309414547048914 = some 183309414547048914 := by decide +kernel
private theorem endpoint_19_49_p12 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 12 183309414547048914 = some 183309414547048914 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 10 2 183309414547048914 183309414547048914 183309414547048914 endpoint_19_49_p10 endpoint_19_49_w10
private theorem endpoint_19_49_w12 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 12 2 183309414547048914 = some 183309414547048914 := by decide +kernel
private theorem endpoint_19_49_p14 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 14 183309414547048914 = some 183309414547048914 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 12 2 183309414547048914 183309414547048914 183309414547048914 endpoint_19_49_p12 endpoint_19_49_w12
private theorem endpoint_19_49_w14 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 14 2 183309414547048914 = some 183309414547048914 := by decide +kernel
private theorem endpoint_19_49_p16 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 16 183309414547048914 = some 183309414547048914 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 14 2 183309414547048914 183309414547048914 183309414547048914 endpoint_19_49_p14 endpoint_19_49_w14
private theorem endpoint_19_49_w16 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 16 2 183309414547048914 = some 183309414547048914 := by decide +kernel
private theorem endpoint_19_49_p18 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 18 183309414547048914 = some 183309414547048914 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 16 2 183309414547048914 183309414547048914 183309414547048914 endpoint_19_49_p16 endpoint_19_49_w16
def endpoint_19_49 : CertifiedEndpoint :=
  ⟨⟨19, 49, 1744⟩, 183309414547048914, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_49_flag endpoint_19_49_sources 18 183309414547048914 183309414547048914 rfl endpoint_19_49_base endpoint_19_49_p18) (by decide)⟩
private def endpoint_19_50_flag : Flag := ⟨19, 50, 1692⟩
private def endpoint_19_50_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_50_base : receiptBase endpoint_19_50_flag endpoint_19_50_sources = some 181053400096546015 := by decide +kernel
private theorem endpoint_19_50_w0 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 2 181053400096546015 = some 181053400096546015 := by decide +kernel
private theorem endpoint_19_50_w2 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 2 2 181053400096546015 = some 181053400096546015 := by decide +kernel
private theorem endpoint_19_50_p4 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 4 181053400096546015 = some 181053400096546015 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 2 2 181053400096546015 181053400096546015 181053400096546015 endpoint_19_50_w0 endpoint_19_50_w2
private theorem endpoint_19_50_w4 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 4 2 181053400096546015 = some 181053400096546015 := by decide +kernel
private theorem endpoint_19_50_p6 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 6 181053400096546015 = some 181053400096546015 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 4 2 181053400096546015 181053400096546015 181053400096546015 endpoint_19_50_p4 endpoint_19_50_w4
private theorem endpoint_19_50_w6 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 6 2 181053400096546015 = some 181053400096546015 := by decide +kernel
private theorem endpoint_19_50_p8 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 8 181053400096546015 = some 181053400096546015 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 6 2 181053400096546015 181053400096546015 181053400096546015 endpoint_19_50_p6 endpoint_19_50_w6
private theorem endpoint_19_50_w8 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 8 2 181053400096546015 = some 181053400096546015 := by decide +kernel
private theorem endpoint_19_50_p10 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 10 181053400096546015 = some 181053400096546015 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 8 2 181053400096546015 181053400096546015 181053400096546015 endpoint_19_50_p8 endpoint_19_50_w8
private theorem endpoint_19_50_w10 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 10 2 181053400096546015 = some 181053400096546015 := by decide +kernel
private theorem endpoint_19_50_p12 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 12 181053400096546015 = some 181053400096546015 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 10 2 181053400096546015 181053400096546015 181053400096546015 endpoint_19_50_p10 endpoint_19_50_w10
private theorem endpoint_19_50_w12 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 12 2 181053400096546015 = some 181053400096546015 := by decide +kernel
private theorem endpoint_19_50_p14 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 14 181053400096546015 = some 181053400096546015 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 12 2 181053400096546015 181053400096546015 181053400096546015 endpoint_19_50_p12 endpoint_19_50_w12
private theorem endpoint_19_50_w14 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 14 2 181053400096546015 = some 181053400096546015 := by decide +kernel
private theorem endpoint_19_50_p16 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 16 181053400096546015 = some 181053400096546015 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 14 2 181053400096546015 181053400096546015 181053400096546015 endpoint_19_50_p14 endpoint_19_50_w14
private theorem endpoint_19_50_w16 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 16 2 181053400096546015 = some 181053400096546015 := by decide +kernel
private theorem endpoint_19_50_p18 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 18 181053400096546015 = some 181053400096546015 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 16 2 181053400096546015 181053400096546015 181053400096546015 endpoint_19_50_p16 endpoint_19_50_w16
def endpoint_19_50 : CertifiedEndpoint :=
  ⟨⟨19, 50, 1692⟩, 181053400096546015, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_50_flag endpoint_19_50_sources 18 181053400096546015 181053400096546015 rfl endpoint_19_50_base endpoint_19_50_p18) (by decide)⟩
private def endpoint_19_51_flag : Flag := ⟨19, 51, 1640⟩
private def endpoint_19_51_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_51_base : receiptBase endpoint_19_51_flag endpoint_19_51_sources = some 178604956853185948 := by decide +kernel
private theorem endpoint_19_51_w0 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 2 178604956853185948 = some 178604956853185948 := by decide +kernel
private theorem endpoint_19_51_w2 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 2 2 178604956853185948 = some 178604956853185948 := by decide +kernel
private theorem endpoint_19_51_p4 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 4 178604956853185948 = some 178604956853185948 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 2 2 178604956853185948 178604956853185948 178604956853185948 endpoint_19_51_w0 endpoint_19_51_w2
private theorem endpoint_19_51_w4 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 4 2 178604956853185948 = some 178604956853185948 := by decide +kernel
private theorem endpoint_19_51_p6 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 6 178604956853185948 = some 178604956853185948 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 4 2 178604956853185948 178604956853185948 178604956853185948 endpoint_19_51_p4 endpoint_19_51_w4
private theorem endpoint_19_51_w6 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 6 2 178604956853185948 = some 178604956853185948 := by decide +kernel
private theorem endpoint_19_51_p8 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 8 178604956853185948 = some 178604956853185948 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 6 2 178604956853185948 178604956853185948 178604956853185948 endpoint_19_51_p6 endpoint_19_51_w6
private theorem endpoint_19_51_w8 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 8 2 178604956853185948 = some 178604956853185948 := by decide +kernel
private theorem endpoint_19_51_p10 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 10 178604956853185948 = some 178604956853185948 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 8 2 178604956853185948 178604956853185948 178604956853185948 endpoint_19_51_p8 endpoint_19_51_w8
private theorem endpoint_19_51_w10 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 10 2 178604956853185948 = some 178604956853185948 := by decide +kernel
private theorem endpoint_19_51_p12 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 12 178604956853185948 = some 178604956853185948 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 10 2 178604956853185948 178604956853185948 178604956853185948 endpoint_19_51_p10 endpoint_19_51_w10
private theorem endpoint_19_51_w12 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 12 2 178604956853185948 = some 178604956853185948 := by decide +kernel
private theorem endpoint_19_51_p14 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 14 178604956853185948 = some 178604956853185948 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 12 2 178604956853185948 178604956853185948 178604956853185948 endpoint_19_51_p12 endpoint_19_51_w12
private theorem endpoint_19_51_w14 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 14 2 178604956853185948 = some 178604956853185948 := by decide +kernel
private theorem endpoint_19_51_p16 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 16 178604956853185948 = some 178604956853185948 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 14 2 178604956853185948 178604956853185948 178604956853185948 endpoint_19_51_p14 endpoint_19_51_w14
private theorem endpoint_19_51_w16 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 16 2 178604956853185948 = some 178604956853185948 := by decide +kernel
private theorem endpoint_19_51_p18 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 18 178604956853185948 = some 178604956853185948 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 16 2 178604956853185948 178604956853185948 178604956853185948 endpoint_19_51_p16 endpoint_19_51_w16
def endpoint_19_51 : CertifiedEndpoint :=
  ⟨⟨19, 51, 1640⟩, 178604956853185948, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_51_flag endpoint_19_51_sources 18 178604956853185948 178604956853185948 rfl endpoint_19_51_base endpoint_19_51_p18) (by decide)⟩
private def endpoint_19_52_flag : Flag := ⟨19, 52, 1587⟩
private def endpoint_19_52_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_52_base : receiptBase endpoint_19_52_flag endpoint_19_52_sources = some 175854864270618737 := by decide +kernel
private theorem endpoint_19_52_w0 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 2 175854864270618737 = some 175854864270618737 := by decide +kernel
private theorem endpoint_19_52_w2 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 2 2 175854864270618737 = some 175854864270618737 := by decide +kernel
private theorem endpoint_19_52_p4 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 4 175854864270618737 = some 175854864270618737 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 2 2 175854864270618737 175854864270618737 175854864270618737 endpoint_19_52_w0 endpoint_19_52_w2
private theorem endpoint_19_52_w4 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 4 2 175854864270618737 = some 175854864270618737 := by decide +kernel
private theorem endpoint_19_52_p6 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 6 175854864270618737 = some 175854864270618737 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 4 2 175854864270618737 175854864270618737 175854864270618737 endpoint_19_52_p4 endpoint_19_52_w4
private theorem endpoint_19_52_w6 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 6 2 175854864270618737 = some 175854864270618737 := by decide +kernel
private theorem endpoint_19_52_p8 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 8 175854864270618737 = some 175854864270618737 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 6 2 175854864270618737 175854864270618737 175854864270618737 endpoint_19_52_p6 endpoint_19_52_w6
private theorem endpoint_19_52_w8 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 8 2 175854864270618737 = some 175854864270618737 := by decide +kernel
private theorem endpoint_19_52_p10 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 10 175854864270618737 = some 175854864270618737 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 8 2 175854864270618737 175854864270618737 175854864270618737 endpoint_19_52_p8 endpoint_19_52_w8
private theorem endpoint_19_52_w10 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 10 2 175854864270618737 = some 175854864270618737 := by decide +kernel
private theorem endpoint_19_52_p12 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 12 175854864270618737 = some 175854864270618737 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 10 2 175854864270618737 175854864270618737 175854864270618737 endpoint_19_52_p10 endpoint_19_52_w10
private theorem endpoint_19_52_w12 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 12 2 175854864270618737 = some 175854864270618737 := by decide +kernel
private theorem endpoint_19_52_p14 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 14 175854864270618737 = some 175854864270618737 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 12 2 175854864270618737 175854864270618737 175854864270618737 endpoint_19_52_p12 endpoint_19_52_w12
private theorem endpoint_19_52_w14 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 14 2 175854864270618737 = some 175854864270618737 := by decide +kernel
private theorem endpoint_19_52_p16 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 16 175854864270618737 = some 175854864270618737 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 14 2 175854864270618737 175854864270618737 175854864270618737 endpoint_19_52_p14 endpoint_19_52_w14
private theorem endpoint_19_52_w16 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 16 2 175854864270618737 = some 175854864270618737 := by decide +kernel
private theorem endpoint_19_52_p18 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 18 175854864270618737 = some 175854864270618737 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 16 2 175854864270618737 175854864270618737 175854864270618737 endpoint_19_52_p16 endpoint_19_52_w16
def endpoint_19_52 : CertifiedEndpoint :=
  ⟨⟨19, 52, 1587⟩, 175854864270618737, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_52_flag endpoint_19_52_sources 18 175854864270618737 175854864270618737 rfl endpoint_19_52_base endpoint_19_52_p18) (by decide)⟩
private def endpoint_19_53_flag : Flag := ⟨19, 53, 1532⟩
private def endpoint_19_53_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_53_base : receiptBase endpoint_19_53_flag endpoint_19_53_sources = some 172686571181814132 := by decide +kernel
private theorem endpoint_19_53_w0 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 2 172686571181814132 = some 172686571181814132 := by decide +kernel
private theorem endpoint_19_53_w2 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 2 2 172686571181814132 = some 172686571181814132 := by decide +kernel
private theorem endpoint_19_53_p4 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 4 172686571181814132 = some 172686571181814132 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 2 2 172686571181814132 172686571181814132 172686571181814132 endpoint_19_53_w0 endpoint_19_53_w2
private theorem endpoint_19_53_w4 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 4 2 172686571181814132 = some 172686571181814132 := by decide +kernel
private theorem endpoint_19_53_p6 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 6 172686571181814132 = some 172686571181814132 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 4 2 172686571181814132 172686571181814132 172686571181814132 endpoint_19_53_p4 endpoint_19_53_w4
private theorem endpoint_19_53_w6 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 6 2 172686571181814132 = some 172686571181814132 := by decide +kernel
private theorem endpoint_19_53_p8 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 8 172686571181814132 = some 172686571181814132 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 6 2 172686571181814132 172686571181814132 172686571181814132 endpoint_19_53_p6 endpoint_19_53_w6
private theorem endpoint_19_53_w8 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 8 2 172686571181814132 = some 172686571181814132 := by decide +kernel
private theorem endpoint_19_53_p10 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 10 172686571181814132 = some 172686571181814132 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 8 2 172686571181814132 172686571181814132 172686571181814132 endpoint_19_53_p8 endpoint_19_53_w8
private theorem endpoint_19_53_w10 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 10 2 172686571181814132 = some 172686571181814132 := by decide +kernel
private theorem endpoint_19_53_p12 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 12 172686571181814132 = some 172686571181814132 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 10 2 172686571181814132 172686571181814132 172686571181814132 endpoint_19_53_p10 endpoint_19_53_w10
private theorem endpoint_19_53_w12 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 12 2 172686571181814132 = some 172686571181814132 := by decide +kernel
private theorem endpoint_19_53_p14 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 14 172686571181814132 = some 172686571181814132 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 12 2 172686571181814132 172686571181814132 172686571181814132 endpoint_19_53_p12 endpoint_19_53_w12
private theorem endpoint_19_53_w14 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 14 2 172686571181814132 = some 172686571181814132 := by decide +kernel
private theorem endpoint_19_53_p16 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 16 172686571181814132 = some 172686571181814132 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 14 2 172686571181814132 172686571181814132 172686571181814132 endpoint_19_53_p14 endpoint_19_53_w14
private theorem endpoint_19_53_w16 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 16 2 172686571181814132 = some 172686571181814132 := by decide +kernel
private theorem endpoint_19_53_p18 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 18 172686571181814132 = some 172686571181814132 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 16 2 172686571181814132 172686571181814132 172686571181814132 endpoint_19_53_p16 endpoint_19_53_w16
def endpoint_19_53 : CertifiedEndpoint :=
  ⟨⟨19, 53, 1532⟩, 172686571181814132, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_53_flag endpoint_19_53_sources 18 172686571181814132 172686571181814132 rfl endpoint_19_53_base endpoint_19_53_p18) (by decide)⟩
private def endpoint_19_54_flag : Flag := ⟨19, 54, 1477⟩
private def endpoint_19_54_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_54_base : receiptBase endpoint_19_54_flag endpoint_19_54_sources = some 169314853369131950 := by decide +kernel
private theorem endpoint_19_54_w0 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 2 169314853369131950 = some 173016736344278818 := by decide +kernel
private theorem endpoint_19_54_w2 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 2 2 173016736344278818 = some 173016736344278818 := by decide +kernel
private theorem endpoint_19_54_p4 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 4 169314853369131950 = some 173016736344278818 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 2 2 169314853369131950 173016736344278818 173016736344278818 endpoint_19_54_w0 endpoint_19_54_w2
private theorem endpoint_19_54_w4 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 4 2 173016736344278818 = some 173016736344278818 := by decide +kernel
private theorem endpoint_19_54_p6 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 6 169314853369131950 = some 173016736344278818 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 4 2 169314853369131950 173016736344278818 173016736344278818 endpoint_19_54_p4 endpoint_19_54_w4
private theorem endpoint_19_54_w6 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 6 2 173016736344278818 = some 173016736344278818 := by decide +kernel
private theorem endpoint_19_54_p8 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 8 169314853369131950 = some 173016736344278818 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 6 2 169314853369131950 173016736344278818 173016736344278818 endpoint_19_54_p6 endpoint_19_54_w6
private theorem endpoint_19_54_w8 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 8 2 173016736344278818 = some 173016736344278818 := by decide +kernel
private theorem endpoint_19_54_p10 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 10 169314853369131950 = some 173016736344278818 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 8 2 169314853369131950 173016736344278818 173016736344278818 endpoint_19_54_p8 endpoint_19_54_w8
private theorem endpoint_19_54_w10 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 10 2 173016736344278818 = some 173016736344278818 := by decide +kernel
private theorem endpoint_19_54_p12 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 12 169314853369131950 = some 173016736344278818 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 10 2 169314853369131950 173016736344278818 173016736344278818 endpoint_19_54_p10 endpoint_19_54_w10
private theorem endpoint_19_54_w12 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 12 2 173016736344278818 = some 173016736344278818 := by decide +kernel
private theorem endpoint_19_54_p14 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 14 169314853369131950 = some 173016736344278818 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 12 2 169314853369131950 173016736344278818 173016736344278818 endpoint_19_54_p12 endpoint_19_54_w12
private theorem endpoint_19_54_w14 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 14 2 173016736344278818 = some 173016736344278818 := by decide +kernel
private theorem endpoint_19_54_p16 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 16 169314853369131950 = some 173016736344278818 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 14 2 169314853369131950 173016736344278818 173016736344278818 endpoint_19_54_p14 endpoint_19_54_w14
private theorem endpoint_19_54_w16 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 16 2 173016736344278818 = some 173016736344278818 := by decide +kernel
private theorem endpoint_19_54_p18 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 18 169314853369131950 = some 173016736344278818 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 16 2 169314853369131950 173016736344278818 173016736344278818 endpoint_19_54_p16 endpoint_19_54_w16
def endpoint_19_54 : CertifiedEndpoint :=
  ⟨⟨19, 54, 1477⟩, 173016736344278818, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_54_flag endpoint_19_54_sources 18 169314853369131950 173016736344278818 rfl endpoint_19_54_base endpoint_19_54_p18) (by decide)⟩
private def endpoint_19_55_flag : Flag := ⟨19, 55, 1421⟩
private def endpoint_19_55_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_19_55_base : receiptBase endpoint_19_55_flag endpoint_19_55_sources = some 165817904840371490 := by decide +kernel
private theorem endpoint_19_55_w0 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 2 165817904840371490 = some 170497535951087710 := by decide +kernel
private theorem endpoint_19_55_w2 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 2 2 170497535951087710 = some 170497535951087710 := by decide +kernel
private theorem endpoint_19_55_p4 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 4 165817904840371490 = some 170497535951087710 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 2 2 165817904840371490 170497535951087710 170497535951087710 endpoint_19_55_w0 endpoint_19_55_w2
private theorem endpoint_19_55_w4 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 4 2 170497535951087710 = some 170497535951087710 := by decide +kernel
private theorem endpoint_19_55_p6 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 6 165817904840371490 = some 170497535951087710 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 4 2 165817904840371490 170497535951087710 170497535951087710 endpoint_19_55_p4 endpoint_19_55_w4
private theorem endpoint_19_55_w6 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 6 2 170497535951087710 = some 170497535951087710 := by decide +kernel
private theorem endpoint_19_55_p8 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 8 165817904840371490 = some 170497535951087710 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 6 2 165817904840371490 170497535951087710 170497535951087710 endpoint_19_55_p6 endpoint_19_55_w6
private theorem endpoint_19_55_w8 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 8 2 170497535951087710 = some 170497535951087710 := by decide +kernel
private theorem endpoint_19_55_p10 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 10 165817904840371490 = some 170497535951087710 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 8 2 165817904840371490 170497535951087710 170497535951087710 endpoint_19_55_p8 endpoint_19_55_w8
private theorem endpoint_19_55_w10 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 10 2 170497535951087710 = some 170497535951087710 := by decide +kernel
private theorem endpoint_19_55_p12 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 12 165817904840371490 = some 170497535951087710 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 10 2 165817904840371490 170497535951087710 170497535951087710 endpoint_19_55_p10 endpoint_19_55_w10
private theorem endpoint_19_55_w12 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 12 2 170497535951087710 = some 170497535951087710 := by decide +kernel
private theorem endpoint_19_55_p14 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 14 165817904840371490 = some 170497535951087710 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 12 2 165817904840371490 170497535951087710 170497535951087710 endpoint_19_55_p12 endpoint_19_55_w12
private theorem endpoint_19_55_w14 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 14 2 170497535951087710 = some 170497535951087710 := by decide +kernel
private theorem endpoint_19_55_p16 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 16 165817904840371490 = some 170497535951087710 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 14 2 165817904840371490 170497535951087710 170497535951087710 endpoint_19_55_p14 endpoint_19_55_w14
private theorem endpoint_19_55_w16 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 16 2 170497535951087710 = some 170497535951087710 := by decide +kernel
private theorem endpoint_19_55_p18 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 18 165817904840371490 = some 170497535951087710 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 16 2 165817904840371490 170497535951087710 170497535951087710 endpoint_19_55_p16 endpoint_19_55_w16
def endpoint_19_55 : CertifiedEndpoint :=
  ⟨⟨19, 55, 1421⟩, 170497535951087710, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_19_55_flag endpoint_19_55_sources 18 165817904840371490 170497535951087710 rfl endpoint_19_55_base endpoint_19_55_p18) (by decide)⟩
private def endpoint_19_56_flag : Flag := ⟨19, 56, 1363⟩
private def endpoint_19_56_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_19_56_base : receiptBase endpoint_19_56_flag endpoint_19_56_sources = some 163200146594216339 := by decide +kernel
private theorem endpoint_19_56_w0 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 2 163200146594216339 = some 163391677253000240 := by decide +kernel
private theorem endpoint_19_56_w2 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 2 2 163391677253000240 = some 163391677253000240 := by decide +kernel
private theorem endpoint_19_56_p4 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 4 163200146594216339 = some 163391677253000240 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 2 2 163200146594216339 163391677253000240 163391677253000240 endpoint_19_56_w0 endpoint_19_56_w2
private theorem endpoint_19_56_w4 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 4 2 163391677253000240 = some 163391677253000240 := by decide +kernel
private theorem endpoint_19_56_p6 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 6 163200146594216339 = some 163391677253000240 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 4 2 163200146594216339 163391677253000240 163391677253000240 endpoint_19_56_p4 endpoint_19_56_w4
private theorem endpoint_19_56_w6 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 6 2 163391677253000240 = some 163391677253000240 := by decide +kernel
private theorem endpoint_19_56_p8 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 8 163200146594216339 = some 163391677253000240 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 6 2 163200146594216339 163391677253000240 163391677253000240 endpoint_19_56_p6 endpoint_19_56_w6
private theorem endpoint_19_56_w8 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 8 2 163391677253000240 = some 163391677253000240 := by decide +kernel
private theorem endpoint_19_56_p10 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 10 163200146594216339 = some 163391677253000240 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 8 2 163200146594216339 163391677253000240 163391677253000240 endpoint_19_56_p8 endpoint_19_56_w8
private theorem endpoint_19_56_w10 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 10 2 163391677253000240 = some 163391677253000240 := by decide +kernel
private theorem endpoint_19_56_p12 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 12 163200146594216339 = some 163391677253000240 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 10 2 163200146594216339 163391677253000240 163391677253000240 endpoint_19_56_p10 endpoint_19_56_w10
private theorem endpoint_19_56_w12 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 12 2 163391677253000240 = some 163391677253000240 := by decide +kernel
private theorem endpoint_19_56_p14 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 14 163200146594216339 = some 163391677253000240 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 12 2 163200146594216339 163391677253000240 163391677253000240 endpoint_19_56_p12 endpoint_19_56_w12
private theorem endpoint_19_56_w14 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 14 2 163391677253000240 = some 163391677253000240 := by decide +kernel
private theorem endpoint_19_56_p16 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 16 163200146594216339 = some 163391677253000240 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 14 2 163200146594216339 163391677253000240 163391677253000240 endpoint_19_56_p14 endpoint_19_56_w14
private theorem endpoint_19_56_w16 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 16 2 163391677253000240 = some 163391677253000240 := by decide +kernel
private theorem endpoint_19_56_p18 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 18 163200146594216339 = some 163391677253000240 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 16 2 163200146594216339 163391677253000240 163391677253000240 endpoint_19_56_p16 endpoint_19_56_w16
def endpoint_19_56 : CertifiedEndpoint :=
  ⟨⟨19, 56, 1363⟩, 163391677253000240, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_19_56_flag endpoint_19_56_sources 18 163200146594216339 163391677253000240 rfl endpoint_19_56_base endpoint_19_56_p18) (by decide)⟩
private def endpoint_19_57_flag : Flag := ⟨19, 57, 1305⟩
private def endpoint_19_57_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_19_57_base : receiptBase endpoint_19_57_flag endpoint_19_57_sources = some 157427710821991886 := by decide +kernel
private theorem endpoint_19_57_w0 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 2 157427710821991886 = some 169975130722788512 := by decide +kernel
private theorem endpoint_19_57_w2 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 2 2 169975130722788512 = some 169975130722788512 := by decide +kernel
private theorem endpoint_19_57_p4 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 4 157427710821991886 = some 169975130722788512 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 2 2 157427710821991886 169975130722788512 169975130722788512 endpoint_19_57_w0 endpoint_19_57_w2
private theorem endpoint_19_57_w4 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 4 2 169975130722788512 = some 169975130722788512 := by decide +kernel
private theorem endpoint_19_57_p6 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 6 157427710821991886 = some 169975130722788512 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 4 2 157427710821991886 169975130722788512 169975130722788512 endpoint_19_57_p4 endpoint_19_57_w4
private theorem endpoint_19_57_w6 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 6 2 169975130722788512 = some 169975130722788512 := by decide +kernel
private theorem endpoint_19_57_p8 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 8 157427710821991886 = some 169975130722788512 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 6 2 157427710821991886 169975130722788512 169975130722788512 endpoint_19_57_p6 endpoint_19_57_w6
private theorem endpoint_19_57_w8 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 8 2 169975130722788512 = some 169975130722788512 := by decide +kernel
private theorem endpoint_19_57_p10 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 10 157427710821991886 = some 169975130722788512 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 8 2 157427710821991886 169975130722788512 169975130722788512 endpoint_19_57_p8 endpoint_19_57_w8
private theorem endpoint_19_57_w10 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 10 2 169975130722788512 = some 169975130722788512 := by decide +kernel
private theorem endpoint_19_57_p12 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 12 157427710821991886 = some 169975130722788512 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 10 2 157427710821991886 169975130722788512 169975130722788512 endpoint_19_57_p10 endpoint_19_57_w10
private theorem endpoint_19_57_w12 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 12 2 169975130722788512 = some 169975130722788512 := by decide +kernel
private theorem endpoint_19_57_p14 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 14 157427710821991886 = some 169975130722788512 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 12 2 157427710821991886 169975130722788512 169975130722788512 endpoint_19_57_p12 endpoint_19_57_w12
private theorem endpoint_19_57_w14 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 14 2 169975130722788512 = some 169975130722788512 := by decide +kernel
private theorem endpoint_19_57_p16 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 16 157427710821991886 = some 169975130722788512 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 14 2 157427710821991886 169975130722788512 169975130722788512 endpoint_19_57_p14 endpoint_19_57_w14
private theorem endpoint_19_57_w16 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 16 2 169975130722788512 = some 169975130722788512 := by decide +kernel
private theorem endpoint_19_57_p18 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 18 157427710821991886 = some 169975130722788512 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 16 2 157427710821991886 169975130722788512 169975130722788512 endpoint_19_57_p16 endpoint_19_57_w16
def endpoint_19_57 : CertifiedEndpoint :=
  ⟨⟨19, 57, 1305⟩, 169975130722788512, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_19_57_flag endpoint_19_57_sources 18 157427710821991886 169975130722788512 rfl endpoint_19_57_base endpoint_19_57_p18) (by decide)⟩
private def endpoint_19_58_flag : Flag := ⟨19, 58, 1245⟩
private def endpoint_19_58_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_19_58_base : receiptBase endpoint_19_58_flag endpoint_19_58_sources = some 153919973864734929 := by decide +kernel
private theorem endpoint_19_58_w0 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 2 153919973864734929 = some 162071745419415646 := by decide +kernel
private theorem endpoint_19_58_w2 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 2 2 162071745419415646 = some 162071745419415646 := by decide +kernel
private theorem endpoint_19_58_p4 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 4 153919973864734929 = some 162071745419415646 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 2 2 153919973864734929 162071745419415646 162071745419415646 endpoint_19_58_w0 endpoint_19_58_w2
private theorem endpoint_19_58_w4 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 4 2 162071745419415646 = some 162071745419415646 := by decide +kernel
private theorem endpoint_19_58_p6 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 6 153919973864734929 = some 162071745419415646 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 4 2 153919973864734929 162071745419415646 162071745419415646 endpoint_19_58_p4 endpoint_19_58_w4
private theorem endpoint_19_58_w6 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 6 2 162071745419415646 = some 162071745419415646 := by decide +kernel
private theorem endpoint_19_58_p8 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 8 153919973864734929 = some 162071745419415646 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 6 2 153919973864734929 162071745419415646 162071745419415646 endpoint_19_58_p6 endpoint_19_58_w6
private theorem endpoint_19_58_w8 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 8 2 162071745419415646 = some 162071745419415646 := by decide +kernel
private theorem endpoint_19_58_p10 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 10 153919973864734929 = some 162071745419415646 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 8 2 153919973864734929 162071745419415646 162071745419415646 endpoint_19_58_p8 endpoint_19_58_w8
private theorem endpoint_19_58_w10 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 10 2 162071745419415646 = some 162071745419415646 := by decide +kernel
private theorem endpoint_19_58_p12 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 12 153919973864734929 = some 162071745419415646 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 10 2 153919973864734929 162071745419415646 162071745419415646 endpoint_19_58_p10 endpoint_19_58_w10
private theorem endpoint_19_58_w12 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 12 2 162071745419415646 = some 162071745419415646 := by decide +kernel
private theorem endpoint_19_58_p14 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 14 153919973864734929 = some 162071745419415646 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 12 2 153919973864734929 162071745419415646 162071745419415646 endpoint_19_58_p12 endpoint_19_58_w12
private theorem endpoint_19_58_w14 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 14 2 162071745419415646 = some 162071745419415646 := by decide +kernel
private theorem endpoint_19_58_p16 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 16 153919973864734929 = some 162071745419415646 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 14 2 153919973864734929 162071745419415646 162071745419415646 endpoint_19_58_p14 endpoint_19_58_w14
private theorem endpoint_19_58_w16 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 16 2 162071745419415646 = some 162071745419415646 := by decide +kernel
private theorem endpoint_19_58_p18 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 18 153919973864734929 = some 162071745419415646 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 16 2 153919973864734929 162071745419415646 162071745419415646 endpoint_19_58_p16 endpoint_19_58_w16
def endpoint_19_58 : CertifiedEndpoint :=
  ⟨⟨19, 58, 1245⟩, 162071745419415646, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_19_58_flag endpoint_19_58_sources 18 153919973864734929 162071745419415646 rfl endpoint_19_58_base endpoint_19_58_p18) (by decide)⟩
private def endpoint_19_59_flag : Flag := ⟨19, 59, 1184⟩
private def endpoint_19_59_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_19_59_base : receiptBase endpoint_19_59_flag endpoint_19_59_sources = some 148703037359814499 := by decide +kernel
private theorem endpoint_19_59_w0 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 2 148703037359814499 = some 160998507367783147 := by decide +kernel
private theorem endpoint_19_59_w2 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 2 2 160998507367783147 = some 160998507367783147 := by decide +kernel
private theorem endpoint_19_59_p4 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 4 148703037359814499 = some 160998507367783147 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 2 2 148703037359814499 160998507367783147 160998507367783147 endpoint_19_59_w0 endpoint_19_59_w2
private theorem endpoint_19_59_w4 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 4 2 160998507367783147 = some 160998507367783147 := by decide +kernel
private theorem endpoint_19_59_p6 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 6 148703037359814499 = some 160998507367783147 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 4 2 148703037359814499 160998507367783147 160998507367783147 endpoint_19_59_p4 endpoint_19_59_w4
private theorem endpoint_19_59_w6 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 6 2 160998507367783147 = some 160998507367783147 := by decide +kernel
private theorem endpoint_19_59_p8 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 8 148703037359814499 = some 160998507367783147 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 6 2 148703037359814499 160998507367783147 160998507367783147 endpoint_19_59_p6 endpoint_19_59_w6
private theorem endpoint_19_59_w8 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 8 2 160998507367783147 = some 160998507367783147 := by decide +kernel
private theorem endpoint_19_59_p10 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 10 148703037359814499 = some 160998507367783147 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 8 2 148703037359814499 160998507367783147 160998507367783147 endpoint_19_59_p8 endpoint_19_59_w8
private theorem endpoint_19_59_w10 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 10 2 160998507367783147 = some 160998507367783147 := by decide +kernel
private theorem endpoint_19_59_p12 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 12 148703037359814499 = some 160998507367783147 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 10 2 148703037359814499 160998507367783147 160998507367783147 endpoint_19_59_p10 endpoint_19_59_w10
private theorem endpoint_19_59_w12 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 12 2 160998507367783147 = some 160998507367783147 := by decide +kernel
private theorem endpoint_19_59_p14 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 14 148703037359814499 = some 160998507367783147 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 12 2 148703037359814499 160998507367783147 160998507367783147 endpoint_19_59_p12 endpoint_19_59_w12
private theorem endpoint_19_59_w14 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 14 2 160998507367783147 = some 160998507367783147 := by decide +kernel
private theorem endpoint_19_59_p16 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 16 148703037359814499 = some 160998507367783147 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 14 2 148703037359814499 160998507367783147 160998507367783147 endpoint_19_59_p14 endpoint_19_59_w14
private theorem endpoint_19_59_w16 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 16 2 160998507367783147 = some 160998507367783147 := by decide +kernel
private theorem endpoint_19_59_p18 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 18 148703037359814499 = some 160998507367783147 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 16 2 148703037359814499 160998507367783147 160998507367783147 endpoint_19_59_p16 endpoint_19_59_w16
def endpoint_19_59 : CertifiedEndpoint :=
  ⟨⟨19, 59, 1184⟩, 160998507367783147, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_19_59_flag endpoint_19_59_sources 18 148703037359814499 160998507367783147 rfl endpoint_19_59_base endpoint_19_59_p18) (by decide)⟩
def endpoint_19_60 : CertifiedEndpoint :=
  ⟨⟨19, 60, 1122⟩, 259660124660853370, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_61 : CertifiedEndpoint :=
  ⟨⟨19, 61, 1058⟩, 249140162807972813, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_62 : CertifiedEndpoint :=
  ⟨⟨19, 62, 993⟩, 237755714231350125, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_63 : CertifiedEndpoint :=
  ⟨⟨19, 63, 927⟩, 225492450565009732, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_64 : CertifiedEndpoint :=
  ⟨⟨19, 64, 860⟩, 212336043442976060, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_65 : CertifiedEndpoint :=
  ⟨⟨19, 65, 791⟩, 198009469146505512, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_66 : CertifiedEndpoint :=
  ⟨⟨19, 66, 721⟩, 182751542418406821, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_67 : CertifiedEndpoint :=
  ⟨⟨19, 67, 649⟩, 166275687295952674, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_68 : CertifiedEndpoint :=
  ⟨⟨19, 68, 576⟩, 148830270765935520, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_69 : CertifiedEndpoint :=
  ⟨⟨19, 69, 501⟩, 130119164621644330, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_70 : CertifiedEndpoint :=
  ⟨⟨19, 70, 424⟩, 110113712131127956, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_71 : CertifiedEndpoint :=
  ⟨⟨19, 71, 346⟩, 89076608647154421, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_72 : CertifiedEndpoint :=
  ⟨⟨19, 72, 265⟩, 66401269390326093, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_73 : CertifiedEndpoint :=
  ⟨⟨19, 73, 183⟩, 42646517920122024, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_74 : CertifiedEndpoint :=
  ⟨⟨19, 74, 100⟩, 17798025870566640, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_20 : CertifiedEndpoint :=
  ⟨⟨20, 20, 2629⟩, 142707798168607589, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_21 : CertifiedEndpoint :=
  ⟨⟨20, 21, 2594⟩, 145061548907081134, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_22 : CertifiedEndpoint :=
  ⟨⟨20, 22, 2559⟩, 147299246734474629, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_23 : CertifiedEndpoint :=
  ⟨⟨20, 23, 2523⟩, 157802014096250028, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_24 : CertifiedEndpoint :=
  ⟨⟨20, 24, 2487⟩, 167937312136584397, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_25 : CertifiedEndpoint :=
  ⟨⟨20, 25, 2450⟩, 177632141727787735, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_26 : CertifiedEndpoint :=
  ⟨⟨20, 26, 2412⟩, 186871401390896712, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_27 : CertifiedEndpoint :=
  ⟨⟨20, 27, 2374⟩, 195723056427280219, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_28 : CertifiedEndpoint :=
  ⟨⟨20, 28, 2336⟩, 204187106836938256, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_29 : CertifiedEndpoint :=
  ⟨⟨20, 29, 2297⟩, 212170418186896382, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_30 : CertifiedEndpoint :=
  ⟨⟨20, 30, 2257⟩, 219657888998191267, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_31 : CertifiedEndpoint :=
  ⟨⟨20, 31, 2217⟩, 226737619877476242, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_32 : CertifiedEndpoint :=
  ⟨⟨20, 32, 2176⟩, 233301374912813536, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_33 : CertifiedEndpoint :=
  ⟨⟨20, 33, 2135⟩, 239447322363498700, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_34 : CertifiedEndpoint :=
  ⟨⟨20, 34, 2093⟩, 245057158664951743, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_35 : CertifiedEndpoint :=
  ⟨⟨20, 35, 2050⟩, 250115782338209335, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_36 : CertifiedEndpoint :=
  ⟨⟨20, 36, 2007⟩, 254736463121530357, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_37 : CertifiedEndpoint :=
  ⟨⟨20, 37, 1963⟩, 258785795971371488, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_20_38_flag : Flag := ⟨20, 38, 1919⟩
private def endpoint_20_38_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_38_base : receiptBase endpoint_20_38_flag endpoint_20_38_sources = some 162936288311565141 := by decide +kernel
private theorem endpoint_20_38_w0 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 2 162936288311565141 = some 162936288311565141 := by decide +kernel
private theorem endpoint_20_38_w2 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 2 2 162936288311565141 = some 162936288311565141 := by decide +kernel
private theorem endpoint_20_38_p4 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 4 162936288311565141 = some 162936288311565141 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 2 2 162936288311565141 162936288311565141 162936288311565141 endpoint_20_38_w0 endpoint_20_38_w2
private theorem endpoint_20_38_w4 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 4 2 162936288311565141 = some 162936288311565141 := by decide +kernel
private theorem endpoint_20_38_p6 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 6 162936288311565141 = some 162936288311565141 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 4 2 162936288311565141 162936288311565141 162936288311565141 endpoint_20_38_p4 endpoint_20_38_w4
private theorem endpoint_20_38_w6 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 6 2 162936288311565141 = some 162936288311565141 := by decide +kernel
private theorem endpoint_20_38_p8 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 8 162936288311565141 = some 162936288311565141 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 6 2 162936288311565141 162936288311565141 162936288311565141 endpoint_20_38_p6 endpoint_20_38_w6
private theorem endpoint_20_38_w8 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 8 2 162936288311565141 = some 162936288311565141 := by decide +kernel
private theorem endpoint_20_38_p10 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 10 162936288311565141 = some 162936288311565141 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 8 2 162936288311565141 162936288311565141 162936288311565141 endpoint_20_38_p8 endpoint_20_38_w8
private theorem endpoint_20_38_w10 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 10 2 162936288311565141 = some 162936288311565141 := by decide +kernel
private theorem endpoint_20_38_p12 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 12 162936288311565141 = some 162936288311565141 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 10 2 162936288311565141 162936288311565141 162936288311565141 endpoint_20_38_p10 endpoint_20_38_w10
private theorem endpoint_20_38_w12 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 12 2 162936288311565141 = some 162936288311565141 := by decide +kernel
private theorem endpoint_20_38_p14 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 14 162936288311565141 = some 162936288311565141 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 12 2 162936288311565141 162936288311565141 162936288311565141 endpoint_20_38_p12 endpoint_20_38_w12
private theorem endpoint_20_38_w14 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 14 2 162936288311565141 = some 162936288311565141 := by decide +kernel
private theorem endpoint_20_38_p16 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 16 162936288311565141 = some 162936288311565141 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 14 2 162936288311565141 162936288311565141 162936288311565141 endpoint_20_38_p14 endpoint_20_38_w14
private theorem endpoint_20_38_w16 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 16 2 162936288311565141 = some 162936288311565141 := by decide +kernel
private theorem endpoint_20_38_p18 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 18 162936288311565141 = some 162936288311565141 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 16 2 162936288311565141 162936288311565141 162936288311565141 endpoint_20_38_p16 endpoint_20_38_w16
private theorem endpoint_20_38_w18 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 18 1 162936288311565141 = some 162936288311565141 := by decide +kernel
private theorem endpoint_20_38_p19 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 19 162936288311565141 = some 162936288311565141 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 18 1 162936288311565141 162936288311565141 162936288311565141 endpoint_20_38_p18 endpoint_20_38_w18
def endpoint_20_38 : CertifiedEndpoint :=
  ⟨⟨20, 38, 1919⟩, 162936288311565141, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_38_flag endpoint_20_38_sources 19 162936288311565141 162936288311565141 rfl endpoint_20_38_base endpoint_20_38_p19) (by decide)⟩
private def endpoint_20_39_flag : Flag := ⟨20, 39, 1873⟩
private def endpoint_20_39_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_39_base : receiptBase endpoint_20_39_flag endpoint_20_39_sources = some 162762203298776918 := by decide +kernel
private theorem endpoint_20_39_w0 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 2 162762203298776918 = some 162762203298776918 := by decide +kernel
private theorem endpoint_20_39_w2 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 2 2 162762203298776918 = some 162762203298776918 := by decide +kernel
private theorem endpoint_20_39_p4 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 4 162762203298776918 = some 162762203298776918 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 2 2 162762203298776918 162762203298776918 162762203298776918 endpoint_20_39_w0 endpoint_20_39_w2
private theorem endpoint_20_39_w4 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 4 2 162762203298776918 = some 162762203298776918 := by decide +kernel
private theorem endpoint_20_39_p6 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 6 162762203298776918 = some 162762203298776918 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 4 2 162762203298776918 162762203298776918 162762203298776918 endpoint_20_39_p4 endpoint_20_39_w4
private theorem endpoint_20_39_w6 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 6 2 162762203298776918 = some 162762203298776918 := by decide +kernel
private theorem endpoint_20_39_p8 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 8 162762203298776918 = some 162762203298776918 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 6 2 162762203298776918 162762203298776918 162762203298776918 endpoint_20_39_p6 endpoint_20_39_w6
private theorem endpoint_20_39_w8 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 8 2 162762203298776918 = some 162762203298776918 := by decide +kernel
private theorem endpoint_20_39_p10 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 10 162762203298776918 = some 162762203298776918 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 8 2 162762203298776918 162762203298776918 162762203298776918 endpoint_20_39_p8 endpoint_20_39_w8
private theorem endpoint_20_39_w10 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 10 2 162762203298776918 = some 162762203298776918 := by decide +kernel
private theorem endpoint_20_39_p12 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 12 162762203298776918 = some 162762203298776918 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 10 2 162762203298776918 162762203298776918 162762203298776918 endpoint_20_39_p10 endpoint_20_39_w10
private theorem endpoint_20_39_w12 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 12 2 162762203298776918 = some 162762203298776918 := by decide +kernel
private theorem endpoint_20_39_p14 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 14 162762203298776918 = some 162762203298776918 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 12 2 162762203298776918 162762203298776918 162762203298776918 endpoint_20_39_p12 endpoint_20_39_w12
private theorem endpoint_20_39_w14 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 14 2 162762203298776918 = some 162762203298776918 := by decide +kernel
private theorem endpoint_20_39_p16 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 16 162762203298776918 = some 162762203298776918 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 14 2 162762203298776918 162762203298776918 162762203298776918 endpoint_20_39_p14 endpoint_20_39_w14
private theorem endpoint_20_39_w16 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 16 2 162762203298776918 = some 162762203298776918 := by decide +kernel
private theorem endpoint_20_39_p18 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 18 162762203298776918 = some 162762203298776918 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 16 2 162762203298776918 162762203298776918 162762203298776918 endpoint_20_39_p16 endpoint_20_39_w16
private theorem endpoint_20_39_w18 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 18 1 162762203298776918 = some 162762203298776918 := by decide +kernel
private theorem endpoint_20_39_p19 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 19 162762203298776918 = some 162762203298776918 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 18 1 162762203298776918 162762203298776918 162762203298776918 endpoint_20_39_p18 endpoint_20_39_w18
def endpoint_20_39 : CertifiedEndpoint :=
  ⟨⟨20, 39, 1873⟩, 162762203298776918, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_39_flag endpoint_20_39_sources 19 162762203298776918 162762203298776918 rfl endpoint_20_39_base endpoint_20_39_p19) (by decide)⟩
private def endpoint_20_40_flag : Flag := ⟨20, 40, 1827⟩
private def endpoint_20_40_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_40_base : receiptBase endpoint_20_40_flag endpoint_20_40_sources = some 162414961186867048 := by decide +kernel
private theorem endpoint_20_40_w0 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 2 162414961186867048 = some 162414961186867048 := by decide +kernel
private theorem endpoint_20_40_w2 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 2 2 162414961186867048 = some 162414961186867048 := by decide +kernel
private theorem endpoint_20_40_p4 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 4 162414961186867048 = some 162414961186867048 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 2 2 162414961186867048 162414961186867048 162414961186867048 endpoint_20_40_w0 endpoint_20_40_w2
private theorem endpoint_20_40_w4 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 4 2 162414961186867048 = some 162414961186867048 := by decide +kernel
private theorem endpoint_20_40_p6 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 6 162414961186867048 = some 162414961186867048 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 4 2 162414961186867048 162414961186867048 162414961186867048 endpoint_20_40_p4 endpoint_20_40_w4
private theorem endpoint_20_40_w6 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 6 2 162414961186867048 = some 162414961186867048 := by decide +kernel
private theorem endpoint_20_40_p8 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 8 162414961186867048 = some 162414961186867048 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 6 2 162414961186867048 162414961186867048 162414961186867048 endpoint_20_40_p6 endpoint_20_40_w6
private theorem endpoint_20_40_w8 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 8 2 162414961186867048 = some 162414961186867048 := by decide +kernel
private theorem endpoint_20_40_p10 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 10 162414961186867048 = some 162414961186867048 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 8 2 162414961186867048 162414961186867048 162414961186867048 endpoint_20_40_p8 endpoint_20_40_w8
private theorem endpoint_20_40_w10 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 10 2 162414961186867048 = some 162414961186867048 := by decide +kernel
private theorem endpoint_20_40_p12 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 12 162414961186867048 = some 162414961186867048 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 10 2 162414961186867048 162414961186867048 162414961186867048 endpoint_20_40_p10 endpoint_20_40_w10
private theorem endpoint_20_40_w12 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 12 2 162414961186867048 = some 162414961186867048 := by decide +kernel
private theorem endpoint_20_40_p14 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 14 162414961186867048 = some 162414961186867048 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 12 2 162414961186867048 162414961186867048 162414961186867048 endpoint_20_40_p12 endpoint_20_40_w12
private theorem endpoint_20_40_w14 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 14 2 162414961186867048 = some 162414961186867048 := by decide +kernel
private theorem endpoint_20_40_p16 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 16 162414961186867048 = some 162414961186867048 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 14 2 162414961186867048 162414961186867048 162414961186867048 endpoint_20_40_p14 endpoint_20_40_w14
private theorem endpoint_20_40_w16 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 16 2 162414961186867048 = some 162414961186867048 := by decide +kernel
private theorem endpoint_20_40_p18 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 18 162414961186867048 = some 162414961186867048 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 16 2 162414961186867048 162414961186867048 162414961186867048 endpoint_20_40_p16 endpoint_20_40_w16
private theorem endpoint_20_40_w18 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 18 1 162414961186867048 = some 162414961186867048 := by decide +kernel
private theorem endpoint_20_40_p19 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 19 162414961186867048 = some 162414961186867048 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 18 1 162414961186867048 162414961186867048 162414961186867048 endpoint_20_40_p18 endpoint_20_40_w18
def endpoint_20_40 : CertifiedEndpoint :=
  ⟨⟨20, 40, 1827⟩, 162414961186867048, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_40_flag endpoint_20_40_sources 19 162414961186867048 162414961186867048 rfl endpoint_20_40_base endpoint_20_40_p19) (by decide)⟩
private def endpoint_20_41_flag : Flag := ⟨20, 41, 1780⟩
private def endpoint_20_41_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_41_base : receiptBase endpoint_20_41_flag endpoint_20_41_sources = some 161806365050678157 := by decide +kernel
private theorem endpoint_20_41_w0 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 2 161806365050678157 = some 163101964735988661 := by decide +kernel
private theorem endpoint_20_41_w2 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 2 2 163101964735988661 = some 163101964735988661 := by decide +kernel
private theorem endpoint_20_41_p4 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 4 161806365050678157 = some 163101964735988661 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 2 2 161806365050678157 163101964735988661 163101964735988661 endpoint_20_41_w0 endpoint_20_41_w2
private theorem endpoint_20_41_w4 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 4 2 163101964735988661 = some 163101964735988661 := by decide +kernel
private theorem endpoint_20_41_p6 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 6 161806365050678157 = some 163101964735988661 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 4 2 161806365050678157 163101964735988661 163101964735988661 endpoint_20_41_p4 endpoint_20_41_w4
private theorem endpoint_20_41_w6 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 6 2 163101964735988661 = some 163101964735988661 := by decide +kernel
private theorem endpoint_20_41_p8 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 8 161806365050678157 = some 163101964735988661 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 6 2 161806365050678157 163101964735988661 163101964735988661 endpoint_20_41_p6 endpoint_20_41_w6
private theorem endpoint_20_41_w8 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 8 2 163101964735988661 = some 163101964735988661 := by decide +kernel
private theorem endpoint_20_41_p10 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 10 161806365050678157 = some 163101964735988661 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 8 2 161806365050678157 163101964735988661 163101964735988661 endpoint_20_41_p8 endpoint_20_41_w8
private theorem endpoint_20_41_w10 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 10 2 163101964735988661 = some 163101964735988661 := by decide +kernel
private theorem endpoint_20_41_p12 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 12 161806365050678157 = some 163101964735988661 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 10 2 161806365050678157 163101964735988661 163101964735988661 endpoint_20_41_p10 endpoint_20_41_w10
private theorem endpoint_20_41_w12 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 12 2 163101964735988661 = some 163101964735988661 := by decide +kernel
private theorem endpoint_20_41_p14 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 14 161806365050678157 = some 163101964735988661 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 12 2 161806365050678157 163101964735988661 163101964735988661 endpoint_20_41_p12 endpoint_20_41_w12
private theorem endpoint_20_41_w14 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 14 2 163101964735988661 = some 163101964735988661 := by decide +kernel
private theorem endpoint_20_41_p16 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 16 161806365050678157 = some 163101964735988661 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 14 2 161806365050678157 163101964735988661 163101964735988661 endpoint_20_41_p14 endpoint_20_41_w14
private theorem endpoint_20_41_w16 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 16 2 163101964735988661 = some 163101964735988661 := by decide +kernel
private theorem endpoint_20_41_p18 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 18 161806365050678157 = some 163101964735988661 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 16 2 161806365050678157 163101964735988661 163101964735988661 endpoint_20_41_p16 endpoint_20_41_w16
private theorem endpoint_20_41_w18 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 18 1 163101964735988661 = some 163101964735988661 := by decide +kernel
private theorem endpoint_20_41_p19 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 19 161806365050678157 = some 163101964735988661 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 18 1 161806365050678157 163101964735988661 163101964735988661 endpoint_20_41_p18 endpoint_20_41_w18
def endpoint_20_41 : CertifiedEndpoint :=
  ⟨⟨20, 41, 1780⟩, 163101964735988661, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_41_flag endpoint_20_41_sources 19 161806365050678157 163101964735988661 rfl endpoint_20_41_base endpoint_20_41_p19) (by decide)⟩
private def endpoint_20_42_flag : Flag := ⟨20, 42, 1733⟩
private def endpoint_20_42_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_42_base : receiptBase endpoint_20_42_flag endpoint_20_42_sources = some 161020887837444385 := by decide +kernel
private theorem endpoint_20_42_w0 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 2 161020887837444385 = some 166190825759006810 := by decide +kernel
private theorem endpoint_20_42_w2 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 2 2 166190825759006810 = some 166190825759006810 := by decide +kernel
private theorem endpoint_20_42_p4 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 4 161020887837444385 = some 166190825759006810 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 2 2 161020887837444385 166190825759006810 166190825759006810 endpoint_20_42_w0 endpoint_20_42_w2
private theorem endpoint_20_42_w4 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 4 2 166190825759006810 = some 166190825759006810 := by decide +kernel
private theorem endpoint_20_42_p6 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 6 161020887837444385 = some 166190825759006810 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 4 2 161020887837444385 166190825759006810 166190825759006810 endpoint_20_42_p4 endpoint_20_42_w4
private theorem endpoint_20_42_w6 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 6 2 166190825759006810 = some 166190825759006810 := by decide +kernel
private theorem endpoint_20_42_p8 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 8 161020887837444385 = some 166190825759006810 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 6 2 161020887837444385 166190825759006810 166190825759006810 endpoint_20_42_p6 endpoint_20_42_w6
private theorem endpoint_20_42_w8 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 8 2 166190825759006810 = some 166190825759006810 := by decide +kernel
private theorem endpoint_20_42_p10 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 10 161020887837444385 = some 166190825759006810 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 8 2 161020887837444385 166190825759006810 166190825759006810 endpoint_20_42_p8 endpoint_20_42_w8
private theorem endpoint_20_42_w10 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 10 2 166190825759006810 = some 166190825759006810 := by decide +kernel
private theorem endpoint_20_42_p12 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 12 161020887837444385 = some 166190825759006810 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 10 2 161020887837444385 166190825759006810 166190825759006810 endpoint_20_42_p10 endpoint_20_42_w10
private theorem endpoint_20_42_w12 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 12 2 166190825759006810 = some 166190825759006810 := by decide +kernel
private theorem endpoint_20_42_p14 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 14 161020887837444385 = some 166190825759006810 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 12 2 161020887837444385 166190825759006810 166190825759006810 endpoint_20_42_p12 endpoint_20_42_w12
private theorem endpoint_20_42_w14 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 14 2 166190825759006810 = some 166190825759006810 := by decide +kernel
private theorem endpoint_20_42_p16 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 16 161020887837444385 = some 166190825759006810 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 14 2 161020887837444385 166190825759006810 166190825759006810 endpoint_20_42_p14 endpoint_20_42_w14
private theorem endpoint_20_42_w16 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 16 2 166190825759006810 = some 166190825759006810 := by decide +kernel
private theorem endpoint_20_42_p18 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 18 161020887837444385 = some 166190825759006810 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 16 2 161020887837444385 166190825759006810 166190825759006810 endpoint_20_42_p16 endpoint_20_42_w16
private theorem endpoint_20_42_w18 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 18 1 166190825759006810 = some 166190825759006810 := by decide +kernel
private theorem endpoint_20_42_p19 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 19 161020887837444385 = some 166190825759006810 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 18 1 161020887837444385 166190825759006810 166190825759006810 endpoint_20_42_p18 endpoint_20_42_w18
def endpoint_20_42 : CertifiedEndpoint :=
  ⟨⟨20, 42, 1733⟩, 166190825759006810, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_42_flag endpoint_20_42_sources 19 161020887837444385 166190825759006810 rfl endpoint_20_42_base endpoint_20_42_p19) (by decide)⟩
private def endpoint_20_43_flag : Flag := ⟨20, 43, 1685⟩
private def endpoint_20_43_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_20_43_base : receiptBase endpoint_20_43_flag endpoint_20_43_sources = some 161488142998252089 := by decide +kernel
private theorem endpoint_20_43_w0 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 2 161488142998252089 = some 161488142998252089 := by decide +kernel
private theorem endpoint_20_43_w2 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 2 2 161488142998252089 = some 161488142998252089 := by decide +kernel
private theorem endpoint_20_43_p4 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 4 161488142998252089 = some 161488142998252089 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 2 2 161488142998252089 161488142998252089 161488142998252089 endpoint_20_43_w0 endpoint_20_43_w2
private theorem endpoint_20_43_w4 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 4 2 161488142998252089 = some 161488142998252089 := by decide +kernel
private theorem endpoint_20_43_p6 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 6 161488142998252089 = some 161488142998252089 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 4 2 161488142998252089 161488142998252089 161488142998252089 endpoint_20_43_p4 endpoint_20_43_w4
private theorem endpoint_20_43_w6 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 6 2 161488142998252089 = some 161488142998252089 := by decide +kernel
private theorem endpoint_20_43_p8 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 8 161488142998252089 = some 161488142998252089 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 6 2 161488142998252089 161488142998252089 161488142998252089 endpoint_20_43_p6 endpoint_20_43_w6
private theorem endpoint_20_43_w8 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 8 2 161488142998252089 = some 161488142998252089 := by decide +kernel
private theorem endpoint_20_43_p10 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 10 161488142998252089 = some 161488142998252089 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 8 2 161488142998252089 161488142998252089 161488142998252089 endpoint_20_43_p8 endpoint_20_43_w8
private theorem endpoint_20_43_w10 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 10 2 161488142998252089 = some 161488142998252089 := by decide +kernel
private theorem endpoint_20_43_p12 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 12 161488142998252089 = some 161488142998252089 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 10 2 161488142998252089 161488142998252089 161488142998252089 endpoint_20_43_p10 endpoint_20_43_w10
private theorem endpoint_20_43_w12 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 12 2 161488142998252089 = some 161488142998252089 := by decide +kernel
private theorem endpoint_20_43_p14 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 14 161488142998252089 = some 161488142998252089 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 12 2 161488142998252089 161488142998252089 161488142998252089 endpoint_20_43_p12 endpoint_20_43_w12
private theorem endpoint_20_43_w14 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 14 2 161488142998252089 = some 161488142998252089 := by decide +kernel
private theorem endpoint_20_43_p16 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 16 161488142998252089 = some 161488142998252089 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 14 2 161488142998252089 161488142998252089 161488142998252089 endpoint_20_43_p14 endpoint_20_43_w14
private theorem endpoint_20_43_w16 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 16 2 161488142998252089 = some 161488142998252089 := by decide +kernel
private theorem endpoint_20_43_p18 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 18 161488142998252089 = some 161488142998252089 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 16 2 161488142998252089 161488142998252089 161488142998252089 endpoint_20_43_p16 endpoint_20_43_w16
private theorem endpoint_20_43_w18 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 18 1 161488142998252089 = some 161488142998252089 := by decide +kernel
private theorem endpoint_20_43_p19 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 19 161488142998252089 = some 161488142998252089 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 18 1 161488142998252089 161488142998252089 161488142998252089 endpoint_20_43_p18 endpoint_20_43_w18
def endpoint_20_43 : CertifiedEndpoint :=
  ⟨⟨20, 43, 1685⟩, 161488142998252089, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_20_43_flag endpoint_20_43_sources 19 161488142998252089 161488142998252089 rfl endpoint_20_43_base endpoint_20_43_p19) (by decide)⟩
private def endpoint_20_44_flag : Flag := ⟨20, 44, 1636⟩
private def endpoint_20_44_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_20_44_base : receiptBase endpoint_20_44_flag endpoint_20_44_sources = some 160090818732993335 := by decide +kernel
private theorem endpoint_20_44_w0 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 2 160090818732993335 = some 160090818732993335 := by decide +kernel
private theorem endpoint_20_44_w2 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 2 2 160090818732993335 = some 160090818732993335 := by decide +kernel
private theorem endpoint_20_44_p4 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 4 160090818732993335 = some 160090818732993335 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 2 2 160090818732993335 160090818732993335 160090818732993335 endpoint_20_44_w0 endpoint_20_44_w2
private theorem endpoint_20_44_w4 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 4 2 160090818732993335 = some 160090818732993335 := by decide +kernel
private theorem endpoint_20_44_p6 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 6 160090818732993335 = some 160090818732993335 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 4 2 160090818732993335 160090818732993335 160090818732993335 endpoint_20_44_p4 endpoint_20_44_w4
private theorem endpoint_20_44_w6 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 6 2 160090818732993335 = some 160090818732993335 := by decide +kernel
private theorem endpoint_20_44_p8 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 8 160090818732993335 = some 160090818732993335 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 6 2 160090818732993335 160090818732993335 160090818732993335 endpoint_20_44_p6 endpoint_20_44_w6
private theorem endpoint_20_44_w8 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 8 2 160090818732993335 = some 160090818732993335 := by decide +kernel
private theorem endpoint_20_44_p10 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 10 160090818732993335 = some 160090818732993335 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 8 2 160090818732993335 160090818732993335 160090818732993335 endpoint_20_44_p8 endpoint_20_44_w8
private theorem endpoint_20_44_w10 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 10 2 160090818732993335 = some 160090818732993335 := by decide +kernel
private theorem endpoint_20_44_p12 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 12 160090818732993335 = some 160090818732993335 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 10 2 160090818732993335 160090818732993335 160090818732993335 endpoint_20_44_p10 endpoint_20_44_w10
private theorem endpoint_20_44_w12 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 12 2 160090818732993335 = some 160090818732993335 := by decide +kernel
private theorem endpoint_20_44_p14 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 14 160090818732993335 = some 160090818732993335 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 12 2 160090818732993335 160090818732993335 160090818732993335 endpoint_20_44_p12 endpoint_20_44_w12
private theorem endpoint_20_44_w14 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 14 2 160090818732993335 = some 160090818732993335 := by decide +kernel
private theorem endpoint_20_44_p16 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 16 160090818732993335 = some 160090818732993335 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 14 2 160090818732993335 160090818732993335 160090818732993335 endpoint_20_44_p14 endpoint_20_44_w14
private theorem endpoint_20_44_w16 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 16 2 160090818732993335 = some 160090818732993335 := by decide +kernel
private theorem endpoint_20_44_p18 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 18 160090818732993335 = some 160090818732993335 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 16 2 160090818732993335 160090818732993335 160090818732993335 endpoint_20_44_p16 endpoint_20_44_w16
private theorem endpoint_20_44_w18 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 18 1 160090818732993335 = some 160090818732993335 := by decide +kernel
private theorem endpoint_20_44_p19 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 19 160090818732993335 = some 160090818732993335 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 18 1 160090818732993335 160090818732993335 160090818732993335 endpoint_20_44_p18 endpoint_20_44_w18
def endpoint_20_44 : CertifiedEndpoint :=
  ⟨⟨20, 44, 1636⟩, 160090818732993335, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_20_44_flag endpoint_20_44_sources 19 160090818732993335 160090818732993335 rfl endpoint_20_44_base endpoint_20_44_p19) (by decide)⟩
private def endpoint_20_45_flag : Flag := ⟨20, 45, 1586⟩
private def endpoint_20_45_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_20_45_base : receiptBase endpoint_20_45_flag endpoint_20_45_sources = some 158408697979260709 := by decide +kernel
private theorem endpoint_20_45_w0 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 2 158408697979260709 = some 161065284160335983 := by decide +kernel
private theorem endpoint_20_45_w2 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 2 2 161065284160335983 = some 161065284160335983 := by decide +kernel
private theorem endpoint_20_45_p4 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 4 158408697979260709 = some 161065284160335983 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 2 2 158408697979260709 161065284160335983 161065284160335983 endpoint_20_45_w0 endpoint_20_45_w2
private theorem endpoint_20_45_w4 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 4 2 161065284160335983 = some 161065284160335983 := by decide +kernel
private theorem endpoint_20_45_p6 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 6 158408697979260709 = some 161065284160335983 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 4 2 158408697979260709 161065284160335983 161065284160335983 endpoint_20_45_p4 endpoint_20_45_w4
private theorem endpoint_20_45_w6 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 6 2 161065284160335983 = some 161065284160335983 := by decide +kernel
private theorem endpoint_20_45_p8 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 8 158408697979260709 = some 161065284160335983 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 6 2 158408697979260709 161065284160335983 161065284160335983 endpoint_20_45_p6 endpoint_20_45_w6
private theorem endpoint_20_45_w8 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 8 2 161065284160335983 = some 161065284160335983 := by decide +kernel
private theorem endpoint_20_45_p10 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 10 158408697979260709 = some 161065284160335983 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 8 2 158408697979260709 161065284160335983 161065284160335983 endpoint_20_45_p8 endpoint_20_45_w8
private theorem endpoint_20_45_w10 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 10 2 161065284160335983 = some 161065284160335983 := by decide +kernel
private theorem endpoint_20_45_p12 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 12 158408697979260709 = some 161065284160335983 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 10 2 158408697979260709 161065284160335983 161065284160335983 endpoint_20_45_p10 endpoint_20_45_w10
private theorem endpoint_20_45_w12 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 12 2 161065284160335983 = some 161065284160335983 := by decide +kernel
private theorem endpoint_20_45_p14 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 14 158408697979260709 = some 161065284160335983 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 12 2 158408697979260709 161065284160335983 161065284160335983 endpoint_20_45_p12 endpoint_20_45_w12
private theorem endpoint_20_45_w14 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 14 2 161065284160335983 = some 161065284160335983 := by decide +kernel
private theorem endpoint_20_45_p16 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 16 158408697979260709 = some 161065284160335983 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 14 2 158408697979260709 161065284160335983 161065284160335983 endpoint_20_45_p14 endpoint_20_45_w14
private theorem endpoint_20_45_w16 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 16 2 161065284160335983 = some 161065284160335983 := by decide +kernel
private theorem endpoint_20_45_p18 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 18 158408697979260709 = some 161065284160335983 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 16 2 158408697979260709 161065284160335983 161065284160335983 endpoint_20_45_p16 endpoint_20_45_w16
private theorem endpoint_20_45_w18 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 18 1 161065284160335983 = some 161065284160335983 := by decide +kernel
private theorem endpoint_20_45_p19 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 19 158408697979260709 = some 161065284160335983 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 18 1 158408697979260709 161065284160335983 161065284160335983 endpoint_20_45_p18 endpoint_20_45_w18
def endpoint_20_45 : CertifiedEndpoint :=
  ⟨⟨20, 45, 1586⟩, 161065284160335983, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_20_45_flag endpoint_20_45_sources 19 158408697979260709 161065284160335983 rfl endpoint_20_45_base endpoint_20_45_p19) (by decide)⟩
private def endpoint_20_46_flag : Flag := ⟨20, 46, 1535⟩
private def endpoint_20_46_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_20_46_base : receiptBase endpoint_20_46_flag endpoint_20_46_sources = some 156436100267071608 := by decide +kernel
private theorem endpoint_20_46_w0 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 2 156436100267071608 = some 162931440548516186 := by decide +kernel
private theorem endpoint_20_46_w2 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 2 2 162931440548516186 = some 162931440548516186 := by decide +kernel
private theorem endpoint_20_46_p4 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 4 156436100267071608 = some 162931440548516186 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 2 2 156436100267071608 162931440548516186 162931440548516186 endpoint_20_46_w0 endpoint_20_46_w2
private theorem endpoint_20_46_w4 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 4 2 162931440548516186 = some 162931440548516186 := by decide +kernel
private theorem endpoint_20_46_p6 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 6 156436100267071608 = some 162931440548516186 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 4 2 156436100267071608 162931440548516186 162931440548516186 endpoint_20_46_p4 endpoint_20_46_w4
private theorem endpoint_20_46_w6 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 6 2 162931440548516186 = some 162931440548516186 := by decide +kernel
private theorem endpoint_20_46_p8 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 8 156436100267071608 = some 162931440548516186 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 6 2 156436100267071608 162931440548516186 162931440548516186 endpoint_20_46_p6 endpoint_20_46_w6
private theorem endpoint_20_46_w8 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 8 2 162931440548516186 = some 162931440548516186 := by decide +kernel
private theorem endpoint_20_46_p10 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 10 156436100267071608 = some 162931440548516186 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 8 2 156436100267071608 162931440548516186 162931440548516186 endpoint_20_46_p8 endpoint_20_46_w8
private theorem endpoint_20_46_w10 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 10 2 162931440548516186 = some 162931440548516186 := by decide +kernel
private theorem endpoint_20_46_p12 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 12 156436100267071608 = some 162931440548516186 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 10 2 156436100267071608 162931440548516186 162931440548516186 endpoint_20_46_p10 endpoint_20_46_w10
private theorem endpoint_20_46_w12 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 12 2 162931440548516186 = some 162931440548516186 := by decide +kernel
private theorem endpoint_20_46_p14 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 14 156436100267071608 = some 162931440548516186 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 12 2 156436100267071608 162931440548516186 162931440548516186 endpoint_20_46_p12 endpoint_20_46_w12
private theorem endpoint_20_46_w14 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 14 2 162931440548516186 = some 162931440548516186 := by decide +kernel
private theorem endpoint_20_46_p16 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 16 156436100267071608 = some 162931440548516186 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 14 2 156436100267071608 162931440548516186 162931440548516186 endpoint_20_46_p14 endpoint_20_46_w14
private theorem endpoint_20_46_w16 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 16 2 162931440548516186 = some 162931440548516186 := by decide +kernel
private theorem endpoint_20_46_p18 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 18 156436100267071608 = some 162931440548516186 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 16 2 156436100267071608 162931440548516186 162931440548516186 endpoint_20_46_p16 endpoint_20_46_w16
private theorem endpoint_20_46_w18 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 18 1 162931440548516186 = some 162931440548516186 := by decide +kernel
private theorem endpoint_20_46_p19 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 19 156436100267071608 = some 162931440548516186 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 18 1 156436100267071608 162931440548516186 162931440548516186 endpoint_20_46_p18 endpoint_20_46_w18
def endpoint_20_46 : CertifiedEndpoint :=
  ⟨⟨20, 46, 1535⟩, 162931440548516186, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_20_46_flag endpoint_20_46_sources 19 156436100267071608 162931440548516186 rfl endpoint_20_46_base endpoint_20_46_p19) (by decide)⟩
private def endpoint_20_47_flag : Flag := ⟨20, 47, 1484⟩
private def endpoint_20_47_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_20_47_base : receiptBase endpoint_20_47_flag endpoint_20_47_sources = some 155833158006157069 := by decide +kernel
private theorem endpoint_20_47_w0 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 2 155833158006157069 = some 155833158006157069 := by decide +kernel
private theorem endpoint_20_47_w2 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 2 2 155833158006157069 = some 155833158006157069 := by decide +kernel
private theorem endpoint_20_47_p4 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 4 155833158006157069 = some 155833158006157069 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 2 2 155833158006157069 155833158006157069 155833158006157069 endpoint_20_47_w0 endpoint_20_47_w2
private theorem endpoint_20_47_w4 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 4 2 155833158006157069 = some 155833158006157069 := by decide +kernel
private theorem endpoint_20_47_p6 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 6 155833158006157069 = some 155833158006157069 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 4 2 155833158006157069 155833158006157069 155833158006157069 endpoint_20_47_p4 endpoint_20_47_w4
private theorem endpoint_20_47_w6 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 6 2 155833158006157069 = some 155833158006157069 := by decide +kernel
private theorem endpoint_20_47_p8 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 8 155833158006157069 = some 155833158006157069 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 6 2 155833158006157069 155833158006157069 155833158006157069 endpoint_20_47_p6 endpoint_20_47_w6
private theorem endpoint_20_47_w8 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 8 2 155833158006157069 = some 155833158006157069 := by decide +kernel
private theorem endpoint_20_47_p10 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 10 155833158006157069 = some 155833158006157069 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 8 2 155833158006157069 155833158006157069 155833158006157069 endpoint_20_47_p8 endpoint_20_47_w8
private theorem endpoint_20_47_w10 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 10 2 155833158006157069 = some 155833158006157069 := by decide +kernel
private theorem endpoint_20_47_p12 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 12 155833158006157069 = some 155833158006157069 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 10 2 155833158006157069 155833158006157069 155833158006157069 endpoint_20_47_p10 endpoint_20_47_w10
private theorem endpoint_20_47_w12 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 12 2 155833158006157069 = some 155833158006157069 := by decide +kernel
private theorem endpoint_20_47_p14 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 14 155833158006157069 = some 155833158006157069 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 12 2 155833158006157069 155833158006157069 155833158006157069 endpoint_20_47_p12 endpoint_20_47_w12
private theorem endpoint_20_47_w14 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 14 2 155833158006157069 = some 155833158006157069 := by decide +kernel
private theorem endpoint_20_47_p16 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 16 155833158006157069 = some 155833158006157069 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 14 2 155833158006157069 155833158006157069 155833158006157069 endpoint_20_47_p14 endpoint_20_47_w14
private theorem endpoint_20_47_w16 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 16 2 155833158006157069 = some 155833158006157069 := by decide +kernel
private theorem endpoint_20_47_p18 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 18 155833158006157069 = some 155833158006157069 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 16 2 155833158006157069 155833158006157069 155833158006157069 endpoint_20_47_p16 endpoint_20_47_w16
private theorem endpoint_20_47_w18 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 18 1 155833158006157069 = some 155833158006157069 := by decide +kernel
private theorem endpoint_20_47_p19 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 19 155833158006157069 = some 155833158006157069 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 18 1 155833158006157069 155833158006157069 155833158006157069 endpoint_20_47_p18 endpoint_20_47_w18
def endpoint_20_47 : CertifiedEndpoint :=
  ⟨⟨20, 47, 1484⟩, 155833158006157069, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_20_47_flag endpoint_20_47_sources 19 155833158006157069 155833158006157069 rfl endpoint_20_47_base endpoint_20_47_p19) (by decide)⟩
private def endpoint_20_48_flag : Flag := ⟨20, 48, 1432⟩
private def endpoint_20_48_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_20_48_base : receiptBase endpoint_20_48_flag endpoint_20_48_sources = some 153224029479450417 := by decide +kernel
private theorem endpoint_20_48_w0 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 2 153224029479450417 = some 153468442976159592 := by decide +kernel
private theorem endpoint_20_48_w2 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 2 2 153468442976159592 = some 153468442976159592 := by decide +kernel
private theorem endpoint_20_48_p4 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 4 153224029479450417 = some 153468442976159592 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 2 2 153224029479450417 153468442976159592 153468442976159592 endpoint_20_48_w0 endpoint_20_48_w2
private theorem endpoint_20_48_w4 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 4 2 153468442976159592 = some 153468442976159592 := by decide +kernel
private theorem endpoint_20_48_p6 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 6 153224029479450417 = some 153468442976159592 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 4 2 153224029479450417 153468442976159592 153468442976159592 endpoint_20_48_p4 endpoint_20_48_w4
private theorem endpoint_20_48_w6 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 6 2 153468442976159592 = some 153468442976159592 := by decide +kernel
private theorem endpoint_20_48_p8 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 8 153224029479450417 = some 153468442976159592 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 6 2 153224029479450417 153468442976159592 153468442976159592 endpoint_20_48_p6 endpoint_20_48_w6
private theorem endpoint_20_48_w8 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 8 2 153468442976159592 = some 153468442976159592 := by decide +kernel
private theorem endpoint_20_48_p10 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 10 153224029479450417 = some 153468442976159592 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 8 2 153224029479450417 153468442976159592 153468442976159592 endpoint_20_48_p8 endpoint_20_48_w8
private theorem endpoint_20_48_w10 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 10 2 153468442976159592 = some 153468442976159592 := by decide +kernel
private theorem endpoint_20_48_p12 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 12 153224029479450417 = some 153468442976159592 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 10 2 153224029479450417 153468442976159592 153468442976159592 endpoint_20_48_p10 endpoint_20_48_w10
private theorem endpoint_20_48_w12 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 12 2 153468442976159592 = some 153468442976159592 := by decide +kernel
private theorem endpoint_20_48_p14 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 14 153224029479450417 = some 153468442976159592 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 12 2 153224029479450417 153468442976159592 153468442976159592 endpoint_20_48_p12 endpoint_20_48_w12
private theorem endpoint_20_48_w14 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 14 2 153468442976159592 = some 153468442976159592 := by decide +kernel
private theorem endpoint_20_48_p16 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 16 153224029479450417 = some 153468442976159592 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 14 2 153224029479450417 153468442976159592 153468442976159592 endpoint_20_48_p14 endpoint_20_48_w14
private theorem endpoint_20_48_w16 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 16 2 153468442976159592 = some 153468442976159592 := by decide +kernel
private theorem endpoint_20_48_p18 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 18 153224029479450417 = some 153468442976159592 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 16 2 153224029479450417 153468442976159592 153468442976159592 endpoint_20_48_p16 endpoint_20_48_w16
private theorem endpoint_20_48_w18 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 18 1 153468442976159592 = some 153468442976159592 := by decide +kernel
private theorem endpoint_20_48_p19 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 19 153224029479450417 = some 153468442976159592 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 18 1 153224029479450417 153468442976159592 153468442976159592 endpoint_20_48_p18 endpoint_20_48_w18
def endpoint_20_48 : CertifiedEndpoint :=
  ⟨⟨20, 48, 1432⟩, 153468442976159592, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_20_48_flag endpoint_20_48_sources 19 153224029479450417 153468442976159592 rfl endpoint_20_48_base endpoint_20_48_p19) (by decide)⟩
private def endpoint_20_49_flag : Flag := ⟨20, 49, 1378⟩
private def endpoint_20_49_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_20_49_base : receiptBase endpoint_20_49_flag endpoint_20_49_sources = some 150200888428146873 := by decide +kernel
private theorem endpoint_20_49_w0 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 2 150200888428146873 = some 154319930972972089 := by decide +kernel
private theorem endpoint_20_49_w2 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 2 2 154319930972972089 = some 154319930972972089 := by decide +kernel
private theorem endpoint_20_49_p4 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 4 150200888428146873 = some 154319930972972089 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 2 2 150200888428146873 154319930972972089 154319930972972089 endpoint_20_49_w0 endpoint_20_49_w2
private theorem endpoint_20_49_w4 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 4 2 154319930972972089 = some 154319930972972089 := by decide +kernel
private theorem endpoint_20_49_p6 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 6 150200888428146873 = some 154319930972972089 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 4 2 150200888428146873 154319930972972089 154319930972972089 endpoint_20_49_p4 endpoint_20_49_w4
private theorem endpoint_20_49_w6 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 6 2 154319930972972089 = some 154319930972972089 := by decide +kernel
private theorem endpoint_20_49_p8 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 8 150200888428146873 = some 154319930972972089 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 6 2 150200888428146873 154319930972972089 154319930972972089 endpoint_20_49_p6 endpoint_20_49_w6
private theorem endpoint_20_49_w8 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 8 2 154319930972972089 = some 154319930972972089 := by decide +kernel
private theorem endpoint_20_49_p10 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 10 150200888428146873 = some 154319930972972089 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 8 2 150200888428146873 154319930972972089 154319930972972089 endpoint_20_49_p8 endpoint_20_49_w8
private theorem endpoint_20_49_w10 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 10 2 154319930972972089 = some 154319930972972089 := by decide +kernel
private theorem endpoint_20_49_p12 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 12 150200888428146873 = some 154319930972972089 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 10 2 150200888428146873 154319930972972089 154319930972972089 endpoint_20_49_p10 endpoint_20_49_w10
private theorem endpoint_20_49_w12 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 12 2 154319930972972089 = some 154319930972972089 := by decide +kernel
private theorem endpoint_20_49_p14 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 14 150200888428146873 = some 154319930972972089 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 12 2 150200888428146873 154319930972972089 154319930972972089 endpoint_20_49_p12 endpoint_20_49_w12
private theorem endpoint_20_49_w14 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 14 2 154319930972972089 = some 154319930972972089 := by decide +kernel
private theorem endpoint_20_49_p16 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 16 150200888428146873 = some 154319930972972089 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 14 2 150200888428146873 154319930972972089 154319930972972089 endpoint_20_49_p14 endpoint_20_49_w14
private theorem endpoint_20_49_w16 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 16 2 154319930972972089 = some 154319930972972089 := by decide +kernel
private theorem endpoint_20_49_p18 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 18 150200888428146873 = some 154319930972972089 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 16 2 150200888428146873 154319930972972089 154319930972972089 endpoint_20_49_p16 endpoint_20_49_w16
private theorem endpoint_20_49_w18 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 18 1 154319930972972089 = some 154319930972972089 := by decide +kernel
private theorem endpoint_20_49_p19 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 19 150200888428146873 = some 154319930972972089 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 18 1 150200888428146873 154319930972972089 154319930972972089 endpoint_20_49_p18 endpoint_20_49_w18
def endpoint_20_49 : CertifiedEndpoint :=
  ⟨⟨20, 49, 1378⟩, 154319930972972089, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_20_49_flag endpoint_20_49_sources 19 150200888428146873 154319930972972089 rfl endpoint_20_49_base endpoint_20_49_p19) (by decide)⟩
def endpoint_20_50 : CertifiedEndpoint :=
  ⟨⟨20, 50, 1324⟩, 257335563001546984, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_51 : CertifiedEndpoint :=
  ⟨⟨20, 51, 1269⟩, 252532817159343214, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_52 : CertifiedEndpoint :=
  ⟨⟨20, 52, 1213⟩, 246962404157136263, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_53 : CertifiedEndpoint :=
  ⟨⟨20, 53, 1156⟩, 240609222515962801, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_54 : CertifiedEndpoint :=
  ⟨⟨20, 54, 1098⟩, 233458170756859498, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_55 : CertifiedEndpoint :=
  ⟨⟨20, 55, 1039⟩, 225494147400863024, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_56 : CertifiedEndpoint :=
  ⟨⟨20, 56, 979⟩, 216702050969010049, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_57 : CertifiedEndpoint :=
  ⟨⟨20, 57, 918⟩, 207066779982337243, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_58 : CertifiedEndpoint :=
  ⟨⟨20, 58, 856⟩, 196573232961881276, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_59 : CertifiedEndpoint :=
  ⟨⟨20, 59, 793⟩, 185206308428678818, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_60 : CertifiedEndpoint :=
  ⟨⟨20, 60, 728⟩, 172701721854837688, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_61 : CertifiedEndpoint :=
  ⟨⟨20, 61, 663⟩, 159537704032931148, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_62 : CertifiedEndpoint :=
  ⟨⟨20, 62, 596⟩, 145195753559817056, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_63 : CertifiedEndpoint :=
  ⟨⟨20, 63, 527⟩, 129645667477568752, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_64 : CertifiedEndpoint :=
  ⟨⟨20, 64, 458⟩, 113395879536686158, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_65 : CertifiedEndpoint :=
  ⟨⟨20, 65, 387⟩, 95897685376100472, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_66 : CertifiedEndpoint :=
  ⟨⟨20, 66, 315⟩, 77400268044740545, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_67 : CertifiedEndpoint :=
  ⟨⟨20, 67, 241⟩, 57604106230466426, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_68 : CertifiedEndpoint :=
  ⟨⟨20, 68, 166⟩, 36768450634849186, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_69 : CertifiedEndpoint :=
  ⟨⟨20, 69, 89⟩, 14583712293106654, .intrinsic (by decide +kernel) (by decide)⟩

def endpointBlock12 : List CertifiedEndpoint := [
  endpoint_18_58, endpoint_18_59, endpoint_18_60, endpoint_18_61, endpoint_18_62, endpoint_18_63, endpoint_18_64,
  endpoint_18_65, endpoint_18_66, endpoint_18_67, endpoint_18_68, endpoint_18_69, endpoint_18_70, endpoint_18_71,
  endpoint_18_72, endpoint_18_73, endpoint_18_74, endpoint_18_75, endpoint_18_76, endpoint_18_77, endpoint_18_78,
  endpoint_19_19, endpoint_19_20, endpoint_19_21, endpoint_19_22, endpoint_19_23, endpoint_19_24, endpoint_19_25,
  endpoint_19_26, endpoint_19_27, endpoint_19_28, endpoint_19_29, endpoint_19_30, endpoint_19_31, endpoint_19_32,
  endpoint_19_33, endpoint_19_34, endpoint_19_35, endpoint_19_36, endpoint_19_37, endpoint_19_38, endpoint_19_39,
  endpoint_19_40, endpoint_19_41, endpoint_19_42, endpoint_19_43, endpoint_19_44, endpoint_19_45, endpoint_19_46,
  endpoint_19_47, endpoint_19_48, endpoint_19_49, endpoint_19_50, endpoint_19_51, endpoint_19_52, endpoint_19_53,
  endpoint_19_54, endpoint_19_55, endpoint_19_56, endpoint_19_57, endpoint_19_58, endpoint_19_59, endpoint_19_60,
  endpoint_19_61, endpoint_19_62, endpoint_19_63, endpoint_19_64, endpoint_19_65, endpoint_19_66, endpoint_19_67,
  endpoint_19_68, endpoint_19_69, endpoint_19_70, endpoint_19_71, endpoint_19_72, endpoint_19_73, endpoint_19_74,
  endpoint_20_20, endpoint_20_21, endpoint_20_22, endpoint_20_23, endpoint_20_24, endpoint_20_25, endpoint_20_26,
  endpoint_20_27, endpoint_20_28, endpoint_20_29, endpoint_20_30, endpoint_20_31, endpoint_20_32, endpoint_20_33,
  endpoint_20_34, endpoint_20_35, endpoint_20_36, endpoint_20_37, endpoint_20_38, endpoint_20_39, endpoint_20_40,
  endpoint_20_41, endpoint_20_42, endpoint_20_43, endpoint_20_44, endpoint_20_45, endpoint_20_46, endpoint_20_47,
  endpoint_20_48, endpoint_20_49, endpoint_20_50, endpoint_20_51, endpoint_20_52, endpoint_20_53, endpoint_20_54,
  endpoint_20_55, endpoint_20_56, endpoint_20_57, endpoint_20_58, endpoint_20_59, endpoint_20_60, endpoint_20_61,
  endpoint_20_62, endpoint_20_63, endpoint_20_64, endpoint_20_65, endpoint_20_66, endpoint_20_67, endpoint_20_68,
  endpoint_20_69
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
