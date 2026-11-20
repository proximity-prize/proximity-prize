import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def endpoint_18_73 : CertifiedEndpoint :=
  ⟨⟨18, 73, 728⟩, 197105999172942665, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_74 : CertifiedEndpoint :=
  ⟨⟨18, 74, 646⟩, 176164684002978838, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_75 : CertifiedEndpoint :=
  ⟨⟨18, 75, 563⟩, 154181864921386568, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_76 : CertifiedEndpoint :=
  ⟨⟨18, 76, 478⟩, 130843503260216978, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_77 : CertifiedEndpoint :=
  ⟨⟨18, 77, 390⟩, 105817486680870767, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_78 : CertifiedEndpoint :=
  ⟨⟨18, 78, 300⟩, 79372669674670752, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_79 : CertifiedEndpoint :=
  ⟨⟨18, 79, 208⟩, 51481941735641297, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_80 : CertifiedEndpoint :=
  ⟨⟨18, 80, 113⟩, 21799635272195283, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_19 : CertifiedEndpoint :=
  ⟨⟨19, 19, 3057⟩, 150341776922181670, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_20 : CertifiedEndpoint :=
  ⟨⟨19, 20, 3026⟩, 153534167061364546, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_21 : CertifiedEndpoint :=
  ⟨⟨19, 21, 2995⟩, 156629093368776300, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_22 : CertifiedEndpoint :=
  ⟨⟨19, 22, 2963⟩, 168996584683785935, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_23 : CertifiedEndpoint :=
  ⟨⟨19, 23, 2930⟩, 180991529840214813, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_24 : CertifiedEndpoint :=
  ⟨⟨19, 24, 2898⟩, 192733349174291050, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_25 : CertifiedEndpoint :=
  ⟨⟨19, 25, 2864⟩, 204021419632709111, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_26 : CertifiedEndpoint :=
  ⟨⟨19, 26, 2831⟩, 215056364268774531, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_27 : CertifiedEndpoint :=
  ⟨⟨19, 27, 2796⟩, 225608903297230627, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_28 : CertifiedEndpoint :=
  ⟨⟨19, 28, 2762⟩, 235908316503334082, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_29 : CertifiedEndpoint :=
  ⟨⟨19, 29, 2726⟩, 245696667369877065, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_30 : CertifiedEndpoint :=
  ⟨⟨19, 30, 2690⟩, 255136361331014414, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_19_31_flag : Flag := ⟨19, 31, 2654⟩
private def endpoint_19_31_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_31_base : receiptBase endpoint_19_31_flag endpoint_19_31_sources = some 176477754634166464 := by decide +kernel
private theorem endpoint_19_31_w0 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 2 176477754634166464 = some 176477754634166464 := by decide +kernel
private theorem endpoint_19_31_w2 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 2 2 176477754634166464 = some 176477754634166464 := by decide +kernel
private theorem endpoint_19_31_p4 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 4 176477754634166464 = some 176477754634166464 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 2 2 176477754634166464 176477754634166464 176477754634166464 endpoint_19_31_w0 endpoint_19_31_w2
private theorem endpoint_19_31_w4 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 4 2 176477754634166464 = some 176477754634166464 := by decide +kernel
private theorem endpoint_19_31_p6 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 6 176477754634166464 = some 176477754634166464 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 4 2 176477754634166464 176477754634166464 176477754634166464 endpoint_19_31_p4 endpoint_19_31_w4
private theorem endpoint_19_31_w6 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 6 2 176477754634166464 = some 176477754634166464 := by decide +kernel
private theorem endpoint_19_31_p8 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 8 176477754634166464 = some 176477754634166464 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 6 2 176477754634166464 176477754634166464 176477754634166464 endpoint_19_31_p6 endpoint_19_31_w6
private theorem endpoint_19_31_w8 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 8 2 176477754634166464 = some 176477754634166464 := by decide +kernel
private theorem endpoint_19_31_p10 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 10 176477754634166464 = some 176477754634166464 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 8 2 176477754634166464 176477754634166464 176477754634166464 endpoint_19_31_p8 endpoint_19_31_w8
private theorem endpoint_19_31_w10 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 10 2 176477754634166464 = some 176477754634166464 := by decide +kernel
private theorem endpoint_19_31_p12 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 12 176477754634166464 = some 176477754634166464 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 10 2 176477754634166464 176477754634166464 176477754634166464 endpoint_19_31_p10 endpoint_19_31_w10
private theorem endpoint_19_31_w12 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 12 2 176477754634166464 = some 176477754634166464 := by decide +kernel
private theorem endpoint_19_31_p14 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 14 176477754634166464 = some 176477754634166464 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 12 2 176477754634166464 176477754634166464 176477754634166464 endpoint_19_31_p12 endpoint_19_31_w12
private theorem endpoint_19_31_w14 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 14 2 176477754634166464 = some 176477754634166464 := by decide +kernel
private theorem endpoint_19_31_p16 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 16 176477754634166464 = some 176477754634166464 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 14 2 176477754634166464 176477754634166464 176477754634166464 endpoint_19_31_p14 endpoint_19_31_w14
private theorem endpoint_19_31_w16 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 16 2 176477754634166464 = some 176477754634166464 := by decide +kernel
private theorem endpoint_19_31_p18 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 18 176477754634166464 = some 176477754634166464 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 16 2 176477754634166464 176477754634166464 176477754634166464 endpoint_19_31_p16 endpoint_19_31_w16
def endpoint_19_31 : CertifiedEndpoint :=
  ⟨⟨19, 31, 2654⟩, 176477754634166464, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_31_flag endpoint_19_31_sources 18 176477754634166464 176477754634166464 rfl endpoint_19_31_base endpoint_19_31_p18) (by decide)⟩
private def endpoint_19_32_flag : Flag := ⟨19, 32, 2617⟩
private def endpoint_19_32_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_32_base : receiptBase endpoint_19_32_flag endpoint_19_32_sources = some 178733575637124303 := by decide +kernel
private theorem endpoint_19_32_w0 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 2 178733575637124303 = some 178733575637124303 := by decide +kernel
private theorem endpoint_19_32_w2 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 2 2 178733575637124303 = some 178733575637124303 := by decide +kernel
private theorem endpoint_19_32_p4 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 4 178733575637124303 = some 178733575637124303 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 2 2 178733575637124303 178733575637124303 178733575637124303 endpoint_19_32_w0 endpoint_19_32_w2
private theorem endpoint_19_32_w4 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 4 2 178733575637124303 = some 178733575637124303 := by decide +kernel
private theorem endpoint_19_32_p6 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 6 178733575637124303 = some 178733575637124303 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 4 2 178733575637124303 178733575637124303 178733575637124303 endpoint_19_32_p4 endpoint_19_32_w4
private theorem endpoint_19_32_w6 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 6 2 178733575637124303 = some 178733575637124303 := by decide +kernel
private theorem endpoint_19_32_p8 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 8 178733575637124303 = some 178733575637124303 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 6 2 178733575637124303 178733575637124303 178733575637124303 endpoint_19_32_p6 endpoint_19_32_w6
private theorem endpoint_19_32_w8 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 8 2 178733575637124303 = some 178733575637124303 := by decide +kernel
private theorem endpoint_19_32_p10 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 10 178733575637124303 = some 178733575637124303 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 8 2 178733575637124303 178733575637124303 178733575637124303 endpoint_19_32_p8 endpoint_19_32_w8
private theorem endpoint_19_32_w10 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 10 2 178733575637124303 = some 178733575637124303 := by decide +kernel
private theorem endpoint_19_32_p12 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 12 178733575637124303 = some 178733575637124303 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 10 2 178733575637124303 178733575637124303 178733575637124303 endpoint_19_32_p10 endpoint_19_32_w10
private theorem endpoint_19_32_w12 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 12 2 178733575637124303 = some 178733575637124303 := by decide +kernel
private theorem endpoint_19_32_p14 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 14 178733575637124303 = some 178733575637124303 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 12 2 178733575637124303 178733575637124303 178733575637124303 endpoint_19_32_p12 endpoint_19_32_w12
private theorem endpoint_19_32_w14 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 14 2 178733575637124303 = some 178733575637124303 := by decide +kernel
private theorem endpoint_19_32_p16 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 16 178733575637124303 = some 178733575637124303 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 14 2 178733575637124303 178733575637124303 178733575637124303 endpoint_19_32_p14 endpoint_19_32_w14
private theorem endpoint_19_32_w16 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 16 2 178733575637124303 = some 178733575637124303 := by decide +kernel
private theorem endpoint_19_32_p18 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 18 178733575637124303 = some 178733575637124303 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 16 2 178733575637124303 178733575637124303 178733575637124303 endpoint_19_32_p16 endpoint_19_32_w16
def endpoint_19_32 : CertifiedEndpoint :=
  ⟨⟨19, 32, 2617⟩, 178733575637124303, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_32_flag endpoint_19_32_sources 18 178733575637124303 178733575637124303 rfl endpoint_19_32_base endpoint_19_32_p18) (by decide)⟩
private def endpoint_19_33_flag : Flag := ⟨19, 33, 2579⟩
private def endpoint_19_33_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_33_base : receiptBase endpoint_19_33_flag endpoint_19_33_sources = some 180788869988344854 := by decide +kernel
private theorem endpoint_19_33_w0 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 2 180788869988344854 = some 180788869988344854 := by decide +kernel
private theorem endpoint_19_33_w2 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 2 2 180788869988344854 = some 180788869988344854 := by decide +kernel
private theorem endpoint_19_33_p4 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 4 180788869988344854 = some 180788869988344854 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 2 2 180788869988344854 180788869988344854 180788869988344854 endpoint_19_33_w0 endpoint_19_33_w2
private theorem endpoint_19_33_w4 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 4 2 180788869988344854 = some 180788869988344854 := by decide +kernel
private theorem endpoint_19_33_p6 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 6 180788869988344854 = some 180788869988344854 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 4 2 180788869988344854 180788869988344854 180788869988344854 endpoint_19_33_p4 endpoint_19_33_w4
private theorem endpoint_19_33_w6 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 6 2 180788869988344854 = some 180788869988344854 := by decide +kernel
private theorem endpoint_19_33_p8 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 8 180788869988344854 = some 180788869988344854 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 6 2 180788869988344854 180788869988344854 180788869988344854 endpoint_19_33_p6 endpoint_19_33_w6
private theorem endpoint_19_33_w8 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 8 2 180788869988344854 = some 180788869988344854 := by decide +kernel
private theorem endpoint_19_33_p10 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 10 180788869988344854 = some 180788869988344854 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 8 2 180788869988344854 180788869988344854 180788869988344854 endpoint_19_33_p8 endpoint_19_33_w8
private theorem endpoint_19_33_w10 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 10 2 180788869988344854 = some 180788869988344854 := by decide +kernel
private theorem endpoint_19_33_p12 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 12 180788869988344854 = some 180788869988344854 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 10 2 180788869988344854 180788869988344854 180788869988344854 endpoint_19_33_p10 endpoint_19_33_w10
private theorem endpoint_19_33_w12 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 12 2 180788869988344854 = some 180788869988344854 := by decide +kernel
private theorem endpoint_19_33_p14 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 14 180788869988344854 = some 180788869988344854 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 12 2 180788869988344854 180788869988344854 180788869988344854 endpoint_19_33_p12 endpoint_19_33_w12
private theorem endpoint_19_33_w14 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 14 2 180788869988344854 = some 180788869988344854 := by decide +kernel
private theorem endpoint_19_33_p16 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 16 180788869988344854 = some 180788869988344854 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 14 2 180788869988344854 180788869988344854 180788869988344854 endpoint_19_33_p14 endpoint_19_33_w14
private theorem endpoint_19_33_w16 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 16 2 180788869988344854 = some 180788869988344854 := by decide +kernel
private theorem endpoint_19_33_p18 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 18 180788869988344854 = some 180788869988344854 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 16 2 180788869988344854 180788869988344854 180788869988344854 endpoint_19_33_p16 endpoint_19_33_w16
def endpoint_19_33 : CertifiedEndpoint :=
  ⟨⟨19, 33, 2579⟩, 180788869988344854, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_33_flag endpoint_19_33_sources 18 180788869988344854 180788869988344854 rfl endpoint_19_33_base endpoint_19_33_p18) (by decide)⟩
private def endpoint_19_34_flag : Flag := ⟨19, 34, 2541⟩
private def endpoint_19_34_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_34_base : receiptBase endpoint_19_34_flag endpoint_19_34_sources = some 182709283069027321 := by decide +kernel
private theorem endpoint_19_34_w0 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 2 182709283069027321 = some 182709283069027321 := by decide +kernel
private theorem endpoint_19_34_w2 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 2 2 182709283069027321 = some 182709283069027321 := by decide +kernel
private theorem endpoint_19_34_p4 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 4 182709283069027321 = some 182709283069027321 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 2 2 182709283069027321 182709283069027321 182709283069027321 endpoint_19_34_w0 endpoint_19_34_w2
private theorem endpoint_19_34_w4 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 4 2 182709283069027321 = some 182709283069027321 := by decide +kernel
private theorem endpoint_19_34_p6 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 6 182709283069027321 = some 182709283069027321 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 4 2 182709283069027321 182709283069027321 182709283069027321 endpoint_19_34_p4 endpoint_19_34_w4
private theorem endpoint_19_34_w6 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 6 2 182709283069027321 = some 182709283069027321 := by decide +kernel
private theorem endpoint_19_34_p8 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 8 182709283069027321 = some 182709283069027321 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 6 2 182709283069027321 182709283069027321 182709283069027321 endpoint_19_34_p6 endpoint_19_34_w6
private theorem endpoint_19_34_w8 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 8 2 182709283069027321 = some 182709283069027321 := by decide +kernel
private theorem endpoint_19_34_p10 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 10 182709283069027321 = some 182709283069027321 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 8 2 182709283069027321 182709283069027321 182709283069027321 endpoint_19_34_p8 endpoint_19_34_w8
private theorem endpoint_19_34_w10 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 10 2 182709283069027321 = some 182709283069027321 := by decide +kernel
private theorem endpoint_19_34_p12 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 12 182709283069027321 = some 182709283069027321 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 10 2 182709283069027321 182709283069027321 182709283069027321 endpoint_19_34_p10 endpoint_19_34_w10
private theorem endpoint_19_34_w12 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 12 2 182709283069027321 = some 182709283069027321 := by decide +kernel
private theorem endpoint_19_34_p14 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 14 182709283069027321 = some 182709283069027321 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 12 2 182709283069027321 182709283069027321 182709283069027321 endpoint_19_34_p12 endpoint_19_34_w12
private theorem endpoint_19_34_w14 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 14 2 182709283069027321 = some 182709283069027321 := by decide +kernel
private theorem endpoint_19_34_p16 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 16 182709283069027321 = some 182709283069027321 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 14 2 182709283069027321 182709283069027321 182709283069027321 endpoint_19_34_p14 endpoint_19_34_w14
private theorem endpoint_19_34_w16 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 16 2 182709283069027321 = some 182709283069027321 := by decide +kernel
private theorem endpoint_19_34_p18 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 18 182709283069027321 = some 182709283069027321 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 16 2 182709283069027321 182709283069027321 182709283069027321 endpoint_19_34_p16 endpoint_19_34_w16
def endpoint_19_34 : CertifiedEndpoint :=
  ⟨⟨19, 34, 2541⟩, 182709283069027321, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_34_flag endpoint_19_34_sources 18 182709283069027321 182709283069027321 rfl endpoint_19_34_base endpoint_19_34_p18) (by decide)⟩
private def endpoint_19_35_flag : Flag := ⟨19, 35, 2502⟩
private def endpoint_19_35_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_35_base : receiptBase endpoint_19_35_flag endpoint_19_35_sources = some 184422162678723768 := by decide +kernel
private theorem endpoint_19_35_w0 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 2 184422162678723768 = some 184422162678723768 := by decide +kernel
private theorem endpoint_19_35_w2 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 2 2 184422162678723768 = some 184422162678723768 := by decide +kernel
private theorem endpoint_19_35_p4 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 4 184422162678723768 = some 184422162678723768 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 2 2 184422162678723768 184422162678723768 184422162678723768 endpoint_19_35_w0 endpoint_19_35_w2
private theorem endpoint_19_35_w4 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 4 2 184422162678723768 = some 184422162678723768 := by decide +kernel
private theorem endpoint_19_35_p6 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 6 184422162678723768 = some 184422162678723768 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 4 2 184422162678723768 184422162678723768 184422162678723768 endpoint_19_35_p4 endpoint_19_35_w4
private theorem endpoint_19_35_w6 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 6 2 184422162678723768 = some 184422162678723768 := by decide +kernel
private theorem endpoint_19_35_p8 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 8 184422162678723768 = some 184422162678723768 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 6 2 184422162678723768 184422162678723768 184422162678723768 endpoint_19_35_p6 endpoint_19_35_w6
private theorem endpoint_19_35_w8 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 8 2 184422162678723768 = some 184422162678723768 := by decide +kernel
private theorem endpoint_19_35_p10 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 10 184422162678723768 = some 184422162678723768 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 8 2 184422162678723768 184422162678723768 184422162678723768 endpoint_19_35_p8 endpoint_19_35_w8
private theorem endpoint_19_35_w10 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 10 2 184422162678723768 = some 184422162678723768 := by decide +kernel
private theorem endpoint_19_35_p12 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 12 184422162678723768 = some 184422162678723768 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 10 2 184422162678723768 184422162678723768 184422162678723768 endpoint_19_35_p10 endpoint_19_35_w10
private theorem endpoint_19_35_w12 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 12 2 184422162678723768 = some 184422162678723768 := by decide +kernel
private theorem endpoint_19_35_p14 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 14 184422162678723768 = some 184422162678723768 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 12 2 184422162678723768 184422162678723768 184422162678723768 endpoint_19_35_p12 endpoint_19_35_w12
private theorem endpoint_19_35_w14 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 14 2 184422162678723768 = some 184422162678723768 := by decide +kernel
private theorem endpoint_19_35_p16 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 16 184422162678723768 = some 184422162678723768 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 14 2 184422162678723768 184422162678723768 184422162678723768 endpoint_19_35_p14 endpoint_19_35_w14
private theorem endpoint_19_35_w16 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 16 2 184422162678723768 = some 184422162678723768 := by decide +kernel
private theorem endpoint_19_35_p18 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 18 184422162678723768 = some 184422162678723768 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 16 2 184422162678723768 184422162678723768 184422162678723768 endpoint_19_35_p16 endpoint_19_35_w16
def endpoint_19_35 : CertifiedEndpoint :=
  ⟨⟨19, 35, 2502⟩, 184422162678723768, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_35_flag endpoint_19_35_sources 18 184422162678723768 184422162678723768 rfl endpoint_19_35_base endpoint_19_35_p18) (by decide)⟩
private def endpoint_19_36_flag : Flag := ⟨19, 36, 2463⟩
private def endpoint_19_36_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_19_36_base : receiptBase endpoint_19_36_flag endpoint_19_36_sources = some 191721743771719595 := by decide +kernel
private theorem endpoint_19_36_w0 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 2 191721743771719595 = some 191721743771719595 := by decide +kernel
private theorem endpoint_19_36_w2 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 2 2 191721743771719595 = some 191721743771719595 := by decide +kernel
private theorem endpoint_19_36_p4 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 4 191721743771719595 = some 191721743771719595 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 2 2 191721743771719595 191721743771719595 191721743771719595 endpoint_19_36_w0 endpoint_19_36_w2
private theorem endpoint_19_36_w4 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 4 2 191721743771719595 = some 191721743771719595 := by decide +kernel
private theorem endpoint_19_36_p6 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 6 191721743771719595 = some 191721743771719595 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 4 2 191721743771719595 191721743771719595 191721743771719595 endpoint_19_36_p4 endpoint_19_36_w4
private theorem endpoint_19_36_w6 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 6 2 191721743771719595 = some 191721743771719595 := by decide +kernel
private theorem endpoint_19_36_p8 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 8 191721743771719595 = some 191721743771719595 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 6 2 191721743771719595 191721743771719595 191721743771719595 endpoint_19_36_p6 endpoint_19_36_w6
private theorem endpoint_19_36_w8 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 8 2 191721743771719595 = some 191721743771719595 := by decide +kernel
private theorem endpoint_19_36_p10 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 10 191721743771719595 = some 191721743771719595 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 8 2 191721743771719595 191721743771719595 191721743771719595 endpoint_19_36_p8 endpoint_19_36_w8
private theorem endpoint_19_36_w10 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 10 2 191721743771719595 = some 191721743771719595 := by decide +kernel
private theorem endpoint_19_36_p12 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 12 191721743771719595 = some 191721743771719595 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 10 2 191721743771719595 191721743771719595 191721743771719595 endpoint_19_36_p10 endpoint_19_36_w10
private theorem endpoint_19_36_w12 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 12 2 191721743771719595 = some 191721743771719595 := by decide +kernel
private theorem endpoint_19_36_p14 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 14 191721743771719595 = some 191721743771719595 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 12 2 191721743771719595 191721743771719595 191721743771719595 endpoint_19_36_p12 endpoint_19_36_w12
private theorem endpoint_19_36_w14 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 14 2 191721743771719595 = some 191721743771719595 := by decide +kernel
private theorem endpoint_19_36_p16 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 16 191721743771719595 = some 191721743771719595 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 14 2 191721743771719595 191721743771719595 191721743771719595 endpoint_19_36_p14 endpoint_19_36_w14
private theorem endpoint_19_36_w16 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 16 2 191721743771719595 = some 191721743771719595 := by decide +kernel
private theorem endpoint_19_36_p18 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 18 191721743771719595 = some 191721743771719595 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 16 2 191721743771719595 191721743771719595 191721743771719595 endpoint_19_36_p16 endpoint_19_36_w16
def endpoint_19_36 : CertifiedEndpoint :=
  ⟨⟨19, 36, 2463⟩, 191721743771719595, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_19_36_flag endpoint_19_36_sources 18 191721743771719595 191721743771719595 rfl endpoint_19_36_base endpoint_19_36_p18) (by decide)⟩
private def endpoint_19_37_flag : Flag := ⟨19, 37, 2422⟩
private def endpoint_19_37_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_19_37_base : receiptBase endpoint_19_37_flag endpoint_19_37_sources = some 193050772310704401 := by decide +kernel
private theorem endpoint_19_37_w0 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 2 193050772310704401 = some 193050772310704401 := by decide +kernel
private theorem endpoint_19_37_w2 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 2 2 193050772310704401 = some 193050772310704401 := by decide +kernel
private theorem endpoint_19_37_p4 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 4 193050772310704401 = some 193050772310704401 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 2 2 193050772310704401 193050772310704401 193050772310704401 endpoint_19_37_w0 endpoint_19_37_w2
private theorem endpoint_19_37_w4 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 4 2 193050772310704401 = some 193050772310704401 := by decide +kernel
private theorem endpoint_19_37_p6 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 6 193050772310704401 = some 193050772310704401 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 4 2 193050772310704401 193050772310704401 193050772310704401 endpoint_19_37_p4 endpoint_19_37_w4
private theorem endpoint_19_37_w6 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 6 2 193050772310704401 = some 193050772310704401 := by decide +kernel
private theorem endpoint_19_37_p8 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 8 193050772310704401 = some 193050772310704401 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 6 2 193050772310704401 193050772310704401 193050772310704401 endpoint_19_37_p6 endpoint_19_37_w6
private theorem endpoint_19_37_w8 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 8 2 193050772310704401 = some 193050772310704401 := by decide +kernel
private theorem endpoint_19_37_p10 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 10 193050772310704401 = some 193050772310704401 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 8 2 193050772310704401 193050772310704401 193050772310704401 endpoint_19_37_p8 endpoint_19_37_w8
private theorem endpoint_19_37_w10 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 10 2 193050772310704401 = some 193050772310704401 := by decide +kernel
private theorem endpoint_19_37_p12 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 12 193050772310704401 = some 193050772310704401 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 10 2 193050772310704401 193050772310704401 193050772310704401 endpoint_19_37_p10 endpoint_19_37_w10
private theorem endpoint_19_37_w12 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 12 2 193050772310704401 = some 193050772310704401 := by decide +kernel
private theorem endpoint_19_37_p14 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 14 193050772310704401 = some 193050772310704401 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 12 2 193050772310704401 193050772310704401 193050772310704401 endpoint_19_37_p12 endpoint_19_37_w12
private theorem endpoint_19_37_w14 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 14 2 193050772310704401 = some 193050772310704401 := by decide +kernel
private theorem endpoint_19_37_p16 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 16 193050772310704401 = some 193050772310704401 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 14 2 193050772310704401 193050772310704401 193050772310704401 endpoint_19_37_p14 endpoint_19_37_w14
private theorem endpoint_19_37_w16 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 16 2 193050772310704401 = some 193050772310704401 := by decide +kernel
private theorem endpoint_19_37_p18 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 18 193050772310704401 = some 193050772310704401 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 16 2 193050772310704401 193050772310704401 193050772310704401 endpoint_19_37_p16 endpoint_19_37_w16
def endpoint_19_37 : CertifiedEndpoint :=
  ⟨⟨19, 37, 2422⟩, 193050772310704401, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_19_37_flag endpoint_19_37_sources 18 193050772310704401 193050772310704401 rfl endpoint_19_37_base endpoint_19_37_p18) (by decide)⟩
private def endpoint_19_38_flag : Flag := ⟨19, 38, 2382⟩
private def endpoint_19_38_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_38_base : receiptBase endpoint_19_38_flag endpoint_19_38_sources = some 194889492668827494 := by decide +kernel
private theorem endpoint_19_38_w0 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 2 194889492668827494 = some 194889492668827494 := by decide +kernel
private theorem endpoint_19_38_w2 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 2 2 194889492668827494 = some 194889492668827494 := by decide +kernel
private theorem endpoint_19_38_p4 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 4 194889492668827494 = some 194889492668827494 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 2 2 194889492668827494 194889492668827494 194889492668827494 endpoint_19_38_w0 endpoint_19_38_w2
private theorem endpoint_19_38_w4 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 4 2 194889492668827494 = some 194889492668827494 := by decide +kernel
private theorem endpoint_19_38_p6 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 6 194889492668827494 = some 194889492668827494 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 4 2 194889492668827494 194889492668827494 194889492668827494 endpoint_19_38_p4 endpoint_19_38_w4
private theorem endpoint_19_38_w6 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 6 2 194889492668827494 = some 194889492668827494 := by decide +kernel
private theorem endpoint_19_38_p8 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 8 194889492668827494 = some 194889492668827494 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 6 2 194889492668827494 194889492668827494 194889492668827494 endpoint_19_38_p6 endpoint_19_38_w6
private theorem endpoint_19_38_w8 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 8 2 194889492668827494 = some 194889492668827494 := by decide +kernel
private theorem endpoint_19_38_p10 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 10 194889492668827494 = some 194889492668827494 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 8 2 194889492668827494 194889492668827494 194889492668827494 endpoint_19_38_p8 endpoint_19_38_w8
private theorem endpoint_19_38_w10 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 10 2 194889492668827494 = some 194889492668827494 := by decide +kernel
private theorem endpoint_19_38_p12 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 12 194889492668827494 = some 194889492668827494 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 10 2 194889492668827494 194889492668827494 194889492668827494 endpoint_19_38_p10 endpoint_19_38_w10
private theorem endpoint_19_38_w12 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 12 2 194889492668827494 = some 194889492668827494 := by decide +kernel
private theorem endpoint_19_38_p14 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 14 194889492668827494 = some 194889492668827494 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 12 2 194889492668827494 194889492668827494 194889492668827494 endpoint_19_38_p12 endpoint_19_38_w12
private theorem endpoint_19_38_w14 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 14 2 194889492668827494 = some 194889492668827494 := by decide +kernel
private theorem endpoint_19_38_p16 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 16 194889492668827494 = some 194889492668827494 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 14 2 194889492668827494 194889492668827494 194889492668827494 endpoint_19_38_p14 endpoint_19_38_w14
private theorem endpoint_19_38_w16 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 16 2 194889492668827494 = some 194889492668827494 := by decide +kernel
private theorem endpoint_19_38_p18 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 18 194889492668827494 = some 194889492668827494 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 16 2 194889492668827494 194889492668827494 194889492668827494 endpoint_19_38_p16 endpoint_19_38_w16
def endpoint_19_38 : CertifiedEndpoint :=
  ⟨⟨19, 38, 2382⟩, 194889492668827494, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_38_flag endpoint_19_38_sources 18 194889492668827494 194889492668827494 rfl endpoint_19_38_base endpoint_19_38_p18) (by decide)⟩
private def endpoint_19_39_flag : Flag := ⟨19, 39, 2340⟩
private def endpoint_19_39_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_39_base : receiptBase endpoint_19_39_flag endpoint_19_39_sources = some 195856495278814542 := by decide +kernel
private theorem endpoint_19_39_w0 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 2 195856495278814542 = some 195856495278814542 := by decide +kernel
private theorem endpoint_19_39_w2 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 2 2 195856495278814542 = some 195856495278814542 := by decide +kernel
private theorem endpoint_19_39_p4 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 4 195856495278814542 = some 195856495278814542 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 2 2 195856495278814542 195856495278814542 195856495278814542 endpoint_19_39_w0 endpoint_19_39_w2
private theorem endpoint_19_39_w4 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 4 2 195856495278814542 = some 195856495278814542 := by decide +kernel
private theorem endpoint_19_39_p6 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 6 195856495278814542 = some 195856495278814542 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 4 2 195856495278814542 195856495278814542 195856495278814542 endpoint_19_39_p4 endpoint_19_39_w4
private theorem endpoint_19_39_w6 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 6 2 195856495278814542 = some 195856495278814542 := by decide +kernel
private theorem endpoint_19_39_p8 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 8 195856495278814542 = some 195856495278814542 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 6 2 195856495278814542 195856495278814542 195856495278814542 endpoint_19_39_p6 endpoint_19_39_w6
private theorem endpoint_19_39_w8 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 8 2 195856495278814542 = some 195856495278814542 := by decide +kernel
private theorem endpoint_19_39_p10 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 10 195856495278814542 = some 195856495278814542 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 8 2 195856495278814542 195856495278814542 195856495278814542 endpoint_19_39_p8 endpoint_19_39_w8
private theorem endpoint_19_39_w10 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 10 2 195856495278814542 = some 195856495278814542 := by decide +kernel
private theorem endpoint_19_39_p12 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 12 195856495278814542 = some 195856495278814542 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 10 2 195856495278814542 195856495278814542 195856495278814542 endpoint_19_39_p10 endpoint_19_39_w10
private theorem endpoint_19_39_w12 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 12 2 195856495278814542 = some 195856495278814542 := by decide +kernel
private theorem endpoint_19_39_p14 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 14 195856495278814542 = some 195856495278814542 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 12 2 195856495278814542 195856495278814542 195856495278814542 endpoint_19_39_p12 endpoint_19_39_w12
private theorem endpoint_19_39_w14 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 14 2 195856495278814542 = some 195856495278814542 := by decide +kernel
private theorem endpoint_19_39_p16 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 16 195856495278814542 = some 195856495278814542 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 14 2 195856495278814542 195856495278814542 195856495278814542 endpoint_19_39_p14 endpoint_19_39_w14
private theorem endpoint_19_39_w16 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 16 2 195856495278814542 = some 195856495278814542 := by decide +kernel
private theorem endpoint_19_39_p18 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 18 195856495278814542 = some 195856495278814542 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 16 2 195856495278814542 195856495278814542 195856495278814542 endpoint_19_39_p16 endpoint_19_39_w16
def endpoint_19_39 : CertifiedEndpoint :=
  ⟨⟨19, 39, 2340⟩, 195856495278814542, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_39_flag endpoint_19_39_sources 18 195856495278814542 195856495278814542 rfl endpoint_19_39_base endpoint_19_39_p18) (by decide)⟩
private def endpoint_19_40_flag : Flag := ⟨19, 40, 2298⟩
private def endpoint_19_40_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_40_base : receiptBase endpoint_19_40_flag endpoint_19_40_sources = some 196671077945984091 := by decide +kernel
private theorem endpoint_19_40_w0 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 2 196671077945984091 = some 196671077945984091 := by decide +kernel
private theorem endpoint_19_40_w2 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 2 2 196671077945984091 = some 196671077945984091 := by decide +kernel
private theorem endpoint_19_40_p4 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 4 196671077945984091 = some 196671077945984091 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 2 2 196671077945984091 196671077945984091 196671077945984091 endpoint_19_40_w0 endpoint_19_40_w2
private theorem endpoint_19_40_w4 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 4 2 196671077945984091 = some 196671077945984091 := by decide +kernel
private theorem endpoint_19_40_p6 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 6 196671077945984091 = some 196671077945984091 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 4 2 196671077945984091 196671077945984091 196671077945984091 endpoint_19_40_p4 endpoint_19_40_w4
private theorem endpoint_19_40_w6 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 6 2 196671077945984091 = some 196671077945984091 := by decide +kernel
private theorem endpoint_19_40_p8 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 8 196671077945984091 = some 196671077945984091 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 6 2 196671077945984091 196671077945984091 196671077945984091 endpoint_19_40_p6 endpoint_19_40_w6
private theorem endpoint_19_40_w8 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 8 2 196671077945984091 = some 196671077945984091 := by decide +kernel
private theorem endpoint_19_40_p10 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 10 196671077945984091 = some 196671077945984091 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 8 2 196671077945984091 196671077945984091 196671077945984091 endpoint_19_40_p8 endpoint_19_40_w8
private theorem endpoint_19_40_w10 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 10 2 196671077945984091 = some 196671077945984091 := by decide +kernel
private theorem endpoint_19_40_p12 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 12 196671077945984091 = some 196671077945984091 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 10 2 196671077945984091 196671077945984091 196671077945984091 endpoint_19_40_p10 endpoint_19_40_w10
private theorem endpoint_19_40_w12 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 12 2 196671077945984091 = some 196671077945984091 := by decide +kernel
private theorem endpoint_19_40_p14 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 14 196671077945984091 = some 196671077945984091 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 12 2 196671077945984091 196671077945984091 196671077945984091 endpoint_19_40_p12 endpoint_19_40_w12
private theorem endpoint_19_40_w14 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 14 2 196671077945984091 = some 196671077945984091 := by decide +kernel
private theorem endpoint_19_40_p16 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 16 196671077945984091 = some 196671077945984091 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 14 2 196671077945984091 196671077945984091 196671077945984091 endpoint_19_40_p14 endpoint_19_40_w14
private theorem endpoint_19_40_w16 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 16 2 196671077945984091 = some 196671077945984091 := by decide +kernel
private theorem endpoint_19_40_p18 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 18 196671077945984091 = some 196671077945984091 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 16 2 196671077945984091 196671077945984091 196671077945984091 endpoint_19_40_p16 endpoint_19_40_w16
def endpoint_19_40 : CertifiedEndpoint :=
  ⟨⟨19, 40, 2298⟩, 196671077945984091, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_40_flag endpoint_19_40_sources 18 196671077945984091 196671077945984091 rfl endpoint_19_40_base endpoint_19_40_p18) (by decide)⟩
private def endpoint_19_41_flag : Flag := ⟨19, 41, 2255⟩
private def endpoint_19_41_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_41_base : receiptBase endpoint_19_41_flag endpoint_19_41_sources = some 197247843595102941 := by decide +kernel
private theorem endpoint_19_41_w0 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 2 197247843595102941 = some 197247843595102941 := by decide +kernel
private theorem endpoint_19_41_w2 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 2 2 197247843595102941 = some 197247843595102941 := by decide +kernel
private theorem endpoint_19_41_p4 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 4 197247843595102941 = some 197247843595102941 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 2 2 197247843595102941 197247843595102941 197247843595102941 endpoint_19_41_w0 endpoint_19_41_w2
private theorem endpoint_19_41_w4 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 4 2 197247843595102941 = some 197247843595102941 := by decide +kernel
private theorem endpoint_19_41_p6 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 6 197247843595102941 = some 197247843595102941 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 4 2 197247843595102941 197247843595102941 197247843595102941 endpoint_19_41_p4 endpoint_19_41_w4
private theorem endpoint_19_41_w6 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 6 2 197247843595102941 = some 197247843595102941 := by decide +kernel
private theorem endpoint_19_41_p8 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 8 197247843595102941 = some 197247843595102941 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 6 2 197247843595102941 197247843595102941 197247843595102941 endpoint_19_41_p6 endpoint_19_41_w6
private theorem endpoint_19_41_w8 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 8 2 197247843595102941 = some 197247843595102941 := by decide +kernel
private theorem endpoint_19_41_p10 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 10 197247843595102941 = some 197247843595102941 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 8 2 197247843595102941 197247843595102941 197247843595102941 endpoint_19_41_p8 endpoint_19_41_w8
private theorem endpoint_19_41_w10 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 10 2 197247843595102941 = some 197247843595102941 := by decide +kernel
private theorem endpoint_19_41_p12 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 12 197247843595102941 = some 197247843595102941 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 10 2 197247843595102941 197247843595102941 197247843595102941 endpoint_19_41_p10 endpoint_19_41_w10
private theorem endpoint_19_41_w12 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 12 2 197247843595102941 = some 197247843595102941 := by decide +kernel
private theorem endpoint_19_41_p14 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 14 197247843595102941 = some 197247843595102941 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 12 2 197247843595102941 197247843595102941 197247843595102941 endpoint_19_41_p12 endpoint_19_41_w12
private theorem endpoint_19_41_w14 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 14 2 197247843595102941 = some 197247843595102941 := by decide +kernel
private theorem endpoint_19_41_p16 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 16 197247843595102941 = some 197247843595102941 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 14 2 197247843595102941 197247843595102941 197247843595102941 endpoint_19_41_p14 endpoint_19_41_w14
private theorem endpoint_19_41_w16 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 16 2 197247843595102941 = some 197247843595102941 := by decide +kernel
private theorem endpoint_19_41_p18 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 18 197247843595102941 = some 197247843595102941 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 16 2 197247843595102941 197247843595102941 197247843595102941 endpoint_19_41_p16 endpoint_19_41_w16
def endpoint_19_41 : CertifiedEndpoint :=
  ⟨⟨19, 41, 2255⟩, 197247843595102941, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_41_flag endpoint_19_41_sources 18 197247843595102941 197247843595102941 rfl endpoint_19_41_base endpoint_19_41_p18) (by decide)⟩
private def endpoint_19_42_flag : Flag := ⟨19, 42, 2212⟩
private def endpoint_19_42_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_42_base : receiptBase endpoint_19_42_flag endpoint_19_42_sources = some 197668602764530732 := by decide +kernel
private theorem endpoint_19_42_w0 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 2 197668602764530732 = some 197668602764530732 := by decide +kernel
private theorem endpoint_19_42_w2 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 2 2 197668602764530732 = some 197668602764530732 := by decide +kernel
private theorem endpoint_19_42_p4 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 4 197668602764530732 = some 197668602764530732 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 2 2 197668602764530732 197668602764530732 197668602764530732 endpoint_19_42_w0 endpoint_19_42_w2
private theorem endpoint_19_42_w4 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 4 2 197668602764530732 = some 197668602764530732 := by decide +kernel
private theorem endpoint_19_42_p6 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 6 197668602764530732 = some 197668602764530732 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 4 2 197668602764530732 197668602764530732 197668602764530732 endpoint_19_42_p4 endpoint_19_42_w4
private theorem endpoint_19_42_w6 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 6 2 197668602764530732 = some 197668602764530732 := by decide +kernel
private theorem endpoint_19_42_p8 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 8 197668602764530732 = some 197668602764530732 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 6 2 197668602764530732 197668602764530732 197668602764530732 endpoint_19_42_p6 endpoint_19_42_w6
private theorem endpoint_19_42_w8 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 8 2 197668602764530732 = some 197668602764530732 := by decide +kernel
private theorem endpoint_19_42_p10 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 10 197668602764530732 = some 197668602764530732 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 8 2 197668602764530732 197668602764530732 197668602764530732 endpoint_19_42_p8 endpoint_19_42_w8
private theorem endpoint_19_42_w10 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 10 2 197668602764530732 = some 197668602764530732 := by decide +kernel
private theorem endpoint_19_42_p12 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 12 197668602764530732 = some 197668602764530732 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 10 2 197668602764530732 197668602764530732 197668602764530732 endpoint_19_42_p10 endpoint_19_42_w10
private theorem endpoint_19_42_w12 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 12 2 197668602764530732 = some 197668602764530732 := by decide +kernel
private theorem endpoint_19_42_p14 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 14 197668602764530732 = some 197668602764530732 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 12 2 197668602764530732 197668602764530732 197668602764530732 endpoint_19_42_p12 endpoint_19_42_w12
private theorem endpoint_19_42_w14 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 14 2 197668602764530732 = some 197668602764530732 := by decide +kernel
private theorem endpoint_19_42_p16 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 16 197668602764530732 = some 197668602764530732 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 14 2 197668602764530732 197668602764530732 197668602764530732 endpoint_19_42_p14 endpoint_19_42_w14
private theorem endpoint_19_42_w16 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 16 2 197668602764530732 = some 197668602764530732 := by decide +kernel
private theorem endpoint_19_42_p18 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 18 197668602764530732 = some 197668602764530732 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 16 2 197668602764530732 197668602764530732 197668602764530732 endpoint_19_42_p16 endpoint_19_42_w16
def endpoint_19_42 : CertifiedEndpoint :=
  ⟨⟨19, 42, 2212⟩, 197668602764530732, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_42_flag endpoint_19_42_sources 18 197668602764530732 197668602764530732 rfl endpoint_19_42_base endpoint_19_42_p18) (by decide)⟩
private def endpoint_19_43_flag : Flag := ⟨19, 43, 2167⟩
private def endpoint_19_43_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_43_base : receiptBase endpoint_19_43_flag endpoint_19_43_sources = some 197755388230053948 := by decide +kernel
private theorem endpoint_19_43_w0 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 2 197755388230053948 = some 197755388230053948 := by decide +kernel
private theorem endpoint_19_43_w2 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 2 2 197755388230053948 = some 197755388230053948 := by decide +kernel
private theorem endpoint_19_43_p4 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 4 197755388230053948 = some 197755388230053948 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 2 2 197755388230053948 197755388230053948 197755388230053948 endpoint_19_43_w0 endpoint_19_43_w2
private theorem endpoint_19_43_w4 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 4 2 197755388230053948 = some 197755388230053948 := by decide +kernel
private theorem endpoint_19_43_p6 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 6 197755388230053948 = some 197755388230053948 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 4 2 197755388230053948 197755388230053948 197755388230053948 endpoint_19_43_p4 endpoint_19_43_w4
private theorem endpoint_19_43_w6 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 6 2 197755388230053948 = some 197755388230053948 := by decide +kernel
private theorem endpoint_19_43_p8 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 8 197755388230053948 = some 197755388230053948 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 6 2 197755388230053948 197755388230053948 197755388230053948 endpoint_19_43_p6 endpoint_19_43_w6
private theorem endpoint_19_43_w8 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 8 2 197755388230053948 = some 197755388230053948 := by decide +kernel
private theorem endpoint_19_43_p10 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 10 197755388230053948 = some 197755388230053948 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 8 2 197755388230053948 197755388230053948 197755388230053948 endpoint_19_43_p8 endpoint_19_43_w8
private theorem endpoint_19_43_w10 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 10 2 197755388230053948 = some 197755388230053948 := by decide +kernel
private theorem endpoint_19_43_p12 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 12 197755388230053948 = some 197755388230053948 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 10 2 197755388230053948 197755388230053948 197755388230053948 endpoint_19_43_p10 endpoint_19_43_w10
private theorem endpoint_19_43_w12 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 12 2 197755388230053948 = some 197755388230053948 := by decide +kernel
private theorem endpoint_19_43_p14 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 14 197755388230053948 = some 197755388230053948 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 12 2 197755388230053948 197755388230053948 197755388230053948 endpoint_19_43_p12 endpoint_19_43_w12
private theorem endpoint_19_43_w14 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 14 2 197755388230053948 = some 197755388230053948 := by decide +kernel
private theorem endpoint_19_43_p16 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 16 197755388230053948 = some 197755388230053948 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 14 2 197755388230053948 197755388230053948 197755388230053948 endpoint_19_43_p14 endpoint_19_43_w14
private theorem endpoint_19_43_w16 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 16 2 197755388230053948 = some 197755388230053948 := by decide +kernel
private theorem endpoint_19_43_p18 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 18 197755388230053948 = some 197755388230053948 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 16 2 197755388230053948 197755388230053948 197755388230053948 endpoint_19_43_p16 endpoint_19_43_w16
def endpoint_19_43 : CertifiedEndpoint :=
  ⟨⟨19, 43, 2167⟩, 197755388230053948, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_43_flag endpoint_19_43_sources 18 197755388230053948 197755388230053948 rfl endpoint_19_43_base endpoint_19_43_p18) (by decide)⟩
private def endpoint_19_44_flag : Flag := ⟨19, 44, 2122⟩
private def endpoint_19_44_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_44_base : receiptBase endpoint_19_44_flag endpoint_19_44_sources = some 197678994142138986 := by decide +kernel
private theorem endpoint_19_44_w0 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 2 197678994142138986 = some 197678994142138986 := by decide +kernel
private theorem endpoint_19_44_w2 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 2 2 197678994142138986 = some 197678994142138986 := by decide +kernel
private theorem endpoint_19_44_p4 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 4 197678994142138986 = some 197678994142138986 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 2 2 197678994142138986 197678994142138986 197678994142138986 endpoint_19_44_w0 endpoint_19_44_w2
private theorem endpoint_19_44_w4 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 4 2 197678994142138986 = some 197678994142138986 := by decide +kernel
private theorem endpoint_19_44_p6 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 6 197678994142138986 = some 197678994142138986 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 4 2 197678994142138986 197678994142138986 197678994142138986 endpoint_19_44_p4 endpoint_19_44_w4
private theorem endpoint_19_44_w6 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 6 2 197678994142138986 = some 197678994142138986 := by decide +kernel
private theorem endpoint_19_44_p8 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 8 197678994142138986 = some 197678994142138986 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 6 2 197678994142138986 197678994142138986 197678994142138986 endpoint_19_44_p6 endpoint_19_44_w6
private theorem endpoint_19_44_w8 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 8 2 197678994142138986 = some 197678994142138986 := by decide +kernel
private theorem endpoint_19_44_p10 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 10 197678994142138986 = some 197678994142138986 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 8 2 197678994142138986 197678994142138986 197678994142138986 endpoint_19_44_p8 endpoint_19_44_w8
private theorem endpoint_19_44_w10 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 10 2 197678994142138986 = some 197678994142138986 := by decide +kernel
private theorem endpoint_19_44_p12 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 12 197678994142138986 = some 197678994142138986 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 10 2 197678994142138986 197678994142138986 197678994142138986 endpoint_19_44_p10 endpoint_19_44_w10
private theorem endpoint_19_44_w12 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 12 2 197678994142138986 = some 197678994142138986 := by decide +kernel
private theorem endpoint_19_44_p14 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 14 197678994142138986 = some 197678994142138986 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 12 2 197678994142138986 197678994142138986 197678994142138986 endpoint_19_44_p12 endpoint_19_44_w12
private theorem endpoint_19_44_w14 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 14 2 197678994142138986 = some 197678994142138986 := by decide +kernel
private theorem endpoint_19_44_p16 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 16 197678994142138986 = some 197678994142138986 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 14 2 197678994142138986 197678994142138986 197678994142138986 endpoint_19_44_p14 endpoint_19_44_w14
private theorem endpoint_19_44_w16 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 16 2 197678994142138986 = some 197678994142138986 := by decide +kernel
private theorem endpoint_19_44_p18 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 18 197678994142138986 = some 197678994142138986 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 16 2 197678994142138986 197678994142138986 197678994142138986 endpoint_19_44_p16 endpoint_19_44_w16
def endpoint_19_44 : CertifiedEndpoint :=
  ⟨⟨19, 44, 2122⟩, 197678994142138986, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_44_flag endpoint_19_44_sources 18 197678994142138986 197678994142138986 rfl endpoint_19_44_base endpoint_19_44_p18) (by decide)⟩
private def endpoint_19_45_flag : Flag := ⟨19, 45, 2076⟩
private def endpoint_19_45_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_45_base : receiptBase endpoint_19_45_flag endpoint_19_45_sources = some 199553942000022561 := by decide +kernel
private theorem endpoint_19_45_w0 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 2 199553942000022561 = some 199553942000022561 := by decide +kernel
private theorem endpoint_19_45_w2 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 2 2 199553942000022561 = some 199553942000022561 := by decide +kernel
private theorem endpoint_19_45_p4 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 4 199553942000022561 = some 199553942000022561 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 2 2 199553942000022561 199553942000022561 199553942000022561 endpoint_19_45_w0 endpoint_19_45_w2
private theorem endpoint_19_45_w4 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 4 2 199553942000022561 = some 199553942000022561 := by decide +kernel
private theorem endpoint_19_45_p6 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 6 199553942000022561 = some 199553942000022561 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 4 2 199553942000022561 199553942000022561 199553942000022561 endpoint_19_45_p4 endpoint_19_45_w4
private theorem endpoint_19_45_w6 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 6 2 199553942000022561 = some 199553942000022561 := by decide +kernel
private theorem endpoint_19_45_p8 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 8 199553942000022561 = some 199553942000022561 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 6 2 199553942000022561 199553942000022561 199553942000022561 endpoint_19_45_p6 endpoint_19_45_w6
private theorem endpoint_19_45_w8 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 8 2 199553942000022561 = some 199553942000022561 := by decide +kernel
private theorem endpoint_19_45_p10 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 10 199553942000022561 = some 199553942000022561 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 8 2 199553942000022561 199553942000022561 199553942000022561 endpoint_19_45_p8 endpoint_19_45_w8
private theorem endpoint_19_45_w10 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 10 2 199553942000022561 = some 199553942000022561 := by decide +kernel
private theorem endpoint_19_45_p12 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 12 199553942000022561 = some 199553942000022561 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 10 2 199553942000022561 199553942000022561 199553942000022561 endpoint_19_45_p10 endpoint_19_45_w10
private theorem endpoint_19_45_w12 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 12 2 199553942000022561 = some 199553942000022561 := by decide +kernel
private theorem endpoint_19_45_p14 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 14 199553942000022561 = some 199553942000022561 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 12 2 199553942000022561 199553942000022561 199553942000022561 endpoint_19_45_p12 endpoint_19_45_w12
private theorem endpoint_19_45_w14 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 14 2 199553942000022561 = some 199553942000022561 := by decide +kernel
private theorem endpoint_19_45_p16 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 16 199553942000022561 = some 199553942000022561 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 14 2 199553942000022561 199553942000022561 199553942000022561 endpoint_19_45_p14 endpoint_19_45_w14
private theorem endpoint_19_45_w16 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 16 2 199553942000022561 = some 199553942000022561 := by decide +kernel
private theorem endpoint_19_45_p18 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 18 199553942000022561 = some 199553942000022561 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 16 2 199553942000022561 199553942000022561 199553942000022561 endpoint_19_45_p16 endpoint_19_45_w16
def endpoint_19_45 : CertifiedEndpoint :=
  ⟨⟨19, 45, 2076⟩, 199553942000022561, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_45_flag endpoint_19_45_sources 18 199553942000022561 199553942000022561 rfl endpoint_19_45_base endpoint_19_45_p18) (by decide)⟩
private def endpoint_19_46_flag : Flag := ⟨19, 46, 2030⟩
private def endpoint_19_46_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_46_base : receiptBase endpoint_19_46_flag endpoint_19_46_sources = some 199002838894653139 := by decide +kernel
private theorem endpoint_19_46_w0 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 2 199002838894653139 = some 199002838894653139 := by decide +kernel
private theorem endpoint_19_46_w2 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 2 2 199002838894653139 = some 199002838894653139 := by decide +kernel
private theorem endpoint_19_46_p4 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 4 199002838894653139 = some 199002838894653139 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 2 2 199002838894653139 199002838894653139 199002838894653139 endpoint_19_46_w0 endpoint_19_46_w2
private theorem endpoint_19_46_w4 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 4 2 199002838894653139 = some 199002838894653139 := by decide +kernel
private theorem endpoint_19_46_p6 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 6 199002838894653139 = some 199002838894653139 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 4 2 199002838894653139 199002838894653139 199002838894653139 endpoint_19_46_p4 endpoint_19_46_w4
private theorem endpoint_19_46_w6 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 6 2 199002838894653139 = some 199002838894653139 := by decide +kernel
private theorem endpoint_19_46_p8 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 8 199002838894653139 = some 199002838894653139 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 6 2 199002838894653139 199002838894653139 199002838894653139 endpoint_19_46_p6 endpoint_19_46_w6
private theorem endpoint_19_46_w8 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 8 2 199002838894653139 = some 199002838894653139 := by decide +kernel
private theorem endpoint_19_46_p10 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 10 199002838894653139 = some 199002838894653139 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 8 2 199002838894653139 199002838894653139 199002838894653139 endpoint_19_46_p8 endpoint_19_46_w8
private theorem endpoint_19_46_w10 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 10 2 199002838894653139 = some 199002838894653139 := by decide +kernel
private theorem endpoint_19_46_p12 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 12 199002838894653139 = some 199002838894653139 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 10 2 199002838894653139 199002838894653139 199002838894653139 endpoint_19_46_p10 endpoint_19_46_w10
private theorem endpoint_19_46_w12 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 12 2 199002838894653139 = some 199002838894653139 := by decide +kernel
private theorem endpoint_19_46_p14 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 14 199002838894653139 = some 199002838894653139 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 12 2 199002838894653139 199002838894653139 199002838894653139 endpoint_19_46_p12 endpoint_19_46_w12
private theorem endpoint_19_46_w14 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 14 2 199002838894653139 = some 199002838894653139 := by decide +kernel
private theorem endpoint_19_46_p16 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 16 199002838894653139 = some 199002838894653139 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 14 2 199002838894653139 199002838894653139 199002838894653139 endpoint_19_46_p14 endpoint_19_46_w14
private theorem endpoint_19_46_w16 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 16 2 199002838894653139 = some 199002838894653139 := by decide +kernel
private theorem endpoint_19_46_p18 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 18 199002838894653139 = some 199002838894653139 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 16 2 199002838894653139 199002838894653139 199002838894653139 endpoint_19_46_p16 endpoint_19_46_w16
def endpoint_19_46 : CertifiedEndpoint :=
  ⟨⟨19, 46, 2030⟩, 199002838894653139, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_46_flag endpoint_19_46_sources 18 199002838894653139 199002838894653139 rfl endpoint_19_46_base endpoint_19_46_p18) (by decide)⟩
private def endpoint_19_47_flag : Flag := ⟨19, 47, 1982⟩
private def endpoint_19_47_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_47_base : receiptBase endpoint_19_47_flag endpoint_19_47_sources = some 198086224288742068 := by decide +kernel
private theorem endpoint_19_47_w0 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 2 198086224288742068 = some 198086224288742068 := by decide +kernel
private theorem endpoint_19_47_w2 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 2 2 198086224288742068 = some 198086224288742068 := by decide +kernel
private theorem endpoint_19_47_p4 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 4 198086224288742068 = some 198086224288742068 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 2 2 198086224288742068 198086224288742068 198086224288742068 endpoint_19_47_w0 endpoint_19_47_w2
private theorem endpoint_19_47_w4 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 4 2 198086224288742068 = some 198086224288742068 := by decide +kernel
private theorem endpoint_19_47_p6 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 6 198086224288742068 = some 198086224288742068 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 4 2 198086224288742068 198086224288742068 198086224288742068 endpoint_19_47_p4 endpoint_19_47_w4
private theorem endpoint_19_47_w6 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 6 2 198086224288742068 = some 198086224288742068 := by decide +kernel
private theorem endpoint_19_47_p8 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 8 198086224288742068 = some 198086224288742068 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 6 2 198086224288742068 198086224288742068 198086224288742068 endpoint_19_47_p6 endpoint_19_47_w6
private theorem endpoint_19_47_w8 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 8 2 198086224288742068 = some 198086224288742068 := by decide +kernel
private theorem endpoint_19_47_p10 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 10 198086224288742068 = some 198086224288742068 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 8 2 198086224288742068 198086224288742068 198086224288742068 endpoint_19_47_p8 endpoint_19_47_w8
private theorem endpoint_19_47_w10 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 10 2 198086224288742068 = some 198086224288742068 := by decide +kernel
private theorem endpoint_19_47_p12 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 12 198086224288742068 = some 198086224288742068 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 10 2 198086224288742068 198086224288742068 198086224288742068 endpoint_19_47_p10 endpoint_19_47_w10
private theorem endpoint_19_47_w12 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 12 2 198086224288742068 = some 198086224288742068 := by decide +kernel
private theorem endpoint_19_47_p14 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 14 198086224288742068 = some 198086224288742068 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 12 2 198086224288742068 198086224288742068 198086224288742068 endpoint_19_47_p12 endpoint_19_47_w12
private theorem endpoint_19_47_w14 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 14 2 198086224288742068 = some 198086224288742068 := by decide +kernel
private theorem endpoint_19_47_p16 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 16 198086224288742068 = some 198086224288742068 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 14 2 198086224288742068 198086224288742068 198086224288742068 endpoint_19_47_p14 endpoint_19_47_w14
private theorem endpoint_19_47_w16 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 16 2 198086224288742068 = some 198086224288742068 := by decide +kernel
private theorem endpoint_19_47_p18 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 18 198086224288742068 = some 198086224288742068 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 16 2 198086224288742068 198086224288742068 198086224288742068 endpoint_19_47_p16 endpoint_19_47_w16
def endpoint_19_47 : CertifiedEndpoint :=
  ⟨⟨19, 47, 1982⟩, 198086224288742068, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_47_flag endpoint_19_47_sources 18 198086224288742068 198086224288742068 rfl endpoint_19_47_base endpoint_19_47_p18) (by decide)⟩
private def endpoint_19_48_flag : Flag := ⟨19, 48, 1934⟩
private def endpoint_19_48_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_48_base : receiptBase endpoint_19_48_flag endpoint_19_48_sources = some 196992614918609448 := by decide +kernel
private theorem endpoint_19_48_w0 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 2 196992614918609448 = some 196992614918609448 := by decide +kernel
private theorem endpoint_19_48_w2 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 2 2 196992614918609448 = some 196992614918609448 := by decide +kernel
private theorem endpoint_19_48_p4 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 4 196992614918609448 = some 196992614918609448 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 2 2 196992614918609448 196992614918609448 196992614918609448 endpoint_19_48_w0 endpoint_19_48_w2
private theorem endpoint_19_48_w4 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 4 2 196992614918609448 = some 196992614918609448 := by decide +kernel
private theorem endpoint_19_48_p6 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 6 196992614918609448 = some 196992614918609448 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 4 2 196992614918609448 196992614918609448 196992614918609448 endpoint_19_48_p4 endpoint_19_48_w4
private theorem endpoint_19_48_w6 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 6 2 196992614918609448 = some 196992614918609448 := by decide +kernel
private theorem endpoint_19_48_p8 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 8 196992614918609448 = some 196992614918609448 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 6 2 196992614918609448 196992614918609448 196992614918609448 endpoint_19_48_p6 endpoint_19_48_w6
private theorem endpoint_19_48_w8 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 8 2 196992614918609448 = some 196992614918609448 := by decide +kernel
private theorem endpoint_19_48_p10 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 10 196992614918609448 = some 196992614918609448 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 8 2 196992614918609448 196992614918609448 196992614918609448 endpoint_19_48_p8 endpoint_19_48_w8
private theorem endpoint_19_48_w10 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 10 2 196992614918609448 = some 196992614918609448 := by decide +kernel
private theorem endpoint_19_48_p12 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 12 196992614918609448 = some 196992614918609448 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 10 2 196992614918609448 196992614918609448 196992614918609448 endpoint_19_48_p10 endpoint_19_48_w10
private theorem endpoint_19_48_w12 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 12 2 196992614918609448 = some 196992614918609448 := by decide +kernel
private theorem endpoint_19_48_p14 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 14 196992614918609448 = some 196992614918609448 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 12 2 196992614918609448 196992614918609448 196992614918609448 endpoint_19_48_p12 endpoint_19_48_w12
private theorem endpoint_19_48_w14 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 14 2 196992614918609448 = some 196992614918609448 := by decide +kernel
private theorem endpoint_19_48_p16 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 16 196992614918609448 = some 196992614918609448 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 14 2 196992614918609448 196992614918609448 196992614918609448 endpoint_19_48_p14 endpoint_19_48_w14
private theorem endpoint_19_48_w16 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 16 2 196992614918609448 = some 196992614918609448 := by decide +kernel
private theorem endpoint_19_48_p18 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 18 196992614918609448 = some 196992614918609448 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 16 2 196992614918609448 196992614918609448 196992614918609448 endpoint_19_48_p16 endpoint_19_48_w16
def endpoint_19_48 : CertifiedEndpoint :=
  ⟨⟨19, 48, 1934⟩, 196992614918609448, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_48_flag endpoint_19_48_sources 18 196992614918609448 196992614918609448 rfl endpoint_19_48_base endpoint_19_48_p18) (by decide)⟩
private def endpoint_19_49_flag : Flag := ⟨19, 49, 1884⟩
private def endpoint_19_49_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_49_base : receiptBase endpoint_19_49_flag endpoint_19_49_sources = some 197840597462972401 := by decide +kernel
private theorem endpoint_19_49_w0 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 2 197840597462972401 = some 197840597462972401 := by decide +kernel
private theorem endpoint_19_49_w2 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 2 2 197840597462972401 = some 197840597462972401 := by decide +kernel
private theorem endpoint_19_49_p4 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 4 197840597462972401 = some 197840597462972401 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 2 2 197840597462972401 197840597462972401 197840597462972401 endpoint_19_49_w0 endpoint_19_49_w2
private theorem endpoint_19_49_w4 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 4 2 197840597462972401 = some 197840597462972401 := by decide +kernel
private theorem endpoint_19_49_p6 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 6 197840597462972401 = some 197840597462972401 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 4 2 197840597462972401 197840597462972401 197840597462972401 endpoint_19_49_p4 endpoint_19_49_w4
private theorem endpoint_19_49_w6 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 6 2 197840597462972401 = some 197840597462972401 := by decide +kernel
private theorem endpoint_19_49_p8 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 8 197840597462972401 = some 197840597462972401 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 6 2 197840597462972401 197840597462972401 197840597462972401 endpoint_19_49_p6 endpoint_19_49_w6
private theorem endpoint_19_49_w8 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 8 2 197840597462972401 = some 197840597462972401 := by decide +kernel
private theorem endpoint_19_49_p10 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 10 197840597462972401 = some 197840597462972401 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 8 2 197840597462972401 197840597462972401 197840597462972401 endpoint_19_49_p8 endpoint_19_49_w8
private theorem endpoint_19_49_w10 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 10 2 197840597462972401 = some 197840597462972401 := by decide +kernel
private theorem endpoint_19_49_p12 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 12 197840597462972401 = some 197840597462972401 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 10 2 197840597462972401 197840597462972401 197840597462972401 endpoint_19_49_p10 endpoint_19_49_w10
private theorem endpoint_19_49_w12 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 12 2 197840597462972401 = some 197840597462972401 := by decide +kernel
private theorem endpoint_19_49_p14 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 14 197840597462972401 = some 197840597462972401 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 12 2 197840597462972401 197840597462972401 197840597462972401 endpoint_19_49_p12 endpoint_19_49_w12
private theorem endpoint_19_49_w14 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 14 2 197840597462972401 = some 197840597462972401 := by decide +kernel
private theorem endpoint_19_49_p16 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 16 197840597462972401 = some 197840597462972401 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 14 2 197840597462972401 197840597462972401 197840597462972401 endpoint_19_49_p14 endpoint_19_49_w14
private theorem endpoint_19_49_w16 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 16 2 197840597462972401 = some 197840597462972401 := by decide +kernel
private theorem endpoint_19_49_p18 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 18 197840597462972401 = some 197840597462972401 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 16 2 197840597462972401 197840597462972401 197840597462972401 endpoint_19_49_p16 endpoint_19_49_w16
def endpoint_19_49 : CertifiedEndpoint :=
  ⟨⟨19, 49, 1884⟩, 197840597462972401, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_49_flag endpoint_19_49_sources 18 197840597462972401 197840597462972401 rfl endpoint_19_49_base endpoint_19_49_p18) (by decide)⟩
private def endpoint_19_50_flag : Flag := ⟨19, 50, 1834⟩
private def endpoint_19_50_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_50_base : receiptBase endpoint_19_50_flag endpoint_19_50_sources = some 196052529969070230 := by decide +kernel
private theorem endpoint_19_50_w0 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 2 196052529969070230 = some 196052529969070230 := by decide +kernel
private theorem endpoint_19_50_w2 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 2 2 196052529969070230 = some 196052529969070230 := by decide +kernel
private theorem endpoint_19_50_p4 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 4 196052529969070230 = some 196052529969070230 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 2 2 196052529969070230 196052529969070230 196052529969070230 endpoint_19_50_w0 endpoint_19_50_w2
private theorem endpoint_19_50_w4 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 4 2 196052529969070230 = some 196052529969070230 := by decide +kernel
private theorem endpoint_19_50_p6 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 6 196052529969070230 = some 196052529969070230 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 4 2 196052529969070230 196052529969070230 196052529969070230 endpoint_19_50_p4 endpoint_19_50_w4
private theorem endpoint_19_50_w6 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 6 2 196052529969070230 = some 196052529969070230 := by decide +kernel
private theorem endpoint_19_50_p8 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 8 196052529969070230 = some 196052529969070230 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 6 2 196052529969070230 196052529969070230 196052529969070230 endpoint_19_50_p6 endpoint_19_50_w6
private theorem endpoint_19_50_w8 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 8 2 196052529969070230 = some 196052529969070230 := by decide +kernel
private theorem endpoint_19_50_p10 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 10 196052529969070230 = some 196052529969070230 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 8 2 196052529969070230 196052529969070230 196052529969070230 endpoint_19_50_p8 endpoint_19_50_w8
private theorem endpoint_19_50_w10 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 10 2 196052529969070230 = some 196052529969070230 := by decide +kernel
private theorem endpoint_19_50_p12 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 12 196052529969070230 = some 196052529969070230 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 10 2 196052529969070230 196052529969070230 196052529969070230 endpoint_19_50_p10 endpoint_19_50_w10
private theorem endpoint_19_50_w12 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 12 2 196052529969070230 = some 196052529969070230 := by decide +kernel
private theorem endpoint_19_50_p14 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 14 196052529969070230 = some 196052529969070230 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 12 2 196052529969070230 196052529969070230 196052529969070230 endpoint_19_50_p12 endpoint_19_50_w12
private theorem endpoint_19_50_w14 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 14 2 196052529969070230 = some 196052529969070230 := by decide +kernel
private theorem endpoint_19_50_p16 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 16 196052529969070230 = some 196052529969070230 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 14 2 196052529969070230 196052529969070230 196052529969070230 endpoint_19_50_p14 endpoint_19_50_w14
private theorem endpoint_19_50_w16 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 16 2 196052529969070230 = some 196052529969070230 := by decide +kernel
private theorem endpoint_19_50_p18 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 18 196052529969070230 = some 196052529969070230 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 16 2 196052529969070230 196052529969070230 196052529969070230 endpoint_19_50_p16 endpoint_19_50_w16
def endpoint_19_50 : CertifiedEndpoint :=
  ⟨⟨19, 50, 1834⟩, 196052529969070230, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_50_flag endpoint_19_50_sources 18 196052529969070230 196052529969070230 rfl endpoint_19_50_base endpoint_19_50_p18) (by decide)⟩
private def endpoint_19_51_flag : Flag := ⟨19, 51, 1783⟩
private def endpoint_19_51_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_51_base : receiptBase endpoint_19_51_flag endpoint_19_51_sources = some 193971976411704404 := by decide +kernel
private theorem endpoint_19_51_w0 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 2 193971976411704404 = some 193971976411704404 := by decide +kernel
private theorem endpoint_19_51_w2 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 2 2 193971976411704404 = some 193971976411704404 := by decide +kernel
private theorem endpoint_19_51_p4 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 4 193971976411704404 = some 193971976411704404 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 2 2 193971976411704404 193971976411704404 193971976411704404 endpoint_19_51_w0 endpoint_19_51_w2
private theorem endpoint_19_51_w4 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 4 2 193971976411704404 = some 193971976411704404 := by decide +kernel
private theorem endpoint_19_51_p6 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 6 193971976411704404 = some 193971976411704404 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 4 2 193971976411704404 193971976411704404 193971976411704404 endpoint_19_51_p4 endpoint_19_51_w4
private theorem endpoint_19_51_w6 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 6 2 193971976411704404 = some 193971976411704404 := by decide +kernel
private theorem endpoint_19_51_p8 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 8 193971976411704404 = some 193971976411704404 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 6 2 193971976411704404 193971976411704404 193971976411704404 endpoint_19_51_p6 endpoint_19_51_w6
private theorem endpoint_19_51_w8 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 8 2 193971976411704404 = some 193971976411704404 := by decide +kernel
private theorem endpoint_19_51_p10 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 10 193971976411704404 = some 193971976411704404 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 8 2 193971976411704404 193971976411704404 193971976411704404 endpoint_19_51_p8 endpoint_19_51_w8
private theorem endpoint_19_51_w10 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 10 2 193971976411704404 = some 193971976411704404 := by decide +kernel
private theorem endpoint_19_51_p12 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 12 193971976411704404 = some 193971976411704404 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 10 2 193971976411704404 193971976411704404 193971976411704404 endpoint_19_51_p10 endpoint_19_51_w10
private theorem endpoint_19_51_w12 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 12 2 193971976411704404 = some 193971976411704404 := by decide +kernel
private theorem endpoint_19_51_p14 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 14 193971976411704404 = some 193971976411704404 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 12 2 193971976411704404 193971976411704404 193971976411704404 endpoint_19_51_p12 endpoint_19_51_w12
private theorem endpoint_19_51_w14 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 14 2 193971976411704404 = some 193971976411704404 := by decide +kernel
private theorem endpoint_19_51_p16 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 16 193971976411704404 = some 193971976411704404 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 14 2 193971976411704404 193971976411704404 193971976411704404 endpoint_19_51_p14 endpoint_19_51_w14
private theorem endpoint_19_51_w16 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 16 2 193971976411704404 = some 193971976411704404 := by decide +kernel
private theorem endpoint_19_51_p18 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 18 193971976411704404 = some 193971976411704404 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 16 2 193971976411704404 193971976411704404 193971976411704404 endpoint_19_51_p16 endpoint_19_51_w16
def endpoint_19_51 : CertifiedEndpoint :=
  ⟨⟨19, 51, 1783⟩, 193971976411704404, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_51_flag endpoint_19_51_sources 18 193971976411704404 193971976411704404 rfl endpoint_19_51_base endpoint_19_51_p18) (by decide)⟩
private def endpoint_19_52_flag : Flag := ⟨19, 52, 1731⟩
private def endpoint_19_52_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_52_base : receiptBase endpoint_19_52_flag endpoint_19_52_sources = some 191593438825363043 := by decide +kernel
private theorem endpoint_19_52_w0 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 2 191593438825363043 = some 191593438825363043 := by decide +kernel
private theorem endpoint_19_52_w2 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 2 2 191593438825363043 = some 191593438825363043 := by decide +kernel
private theorem endpoint_19_52_p4 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 4 191593438825363043 = some 191593438825363043 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 2 2 191593438825363043 191593438825363043 191593438825363043 endpoint_19_52_w0 endpoint_19_52_w2
private theorem endpoint_19_52_w4 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 4 2 191593438825363043 = some 191593438825363043 := by decide +kernel
private theorem endpoint_19_52_p6 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 6 191593438825363043 = some 191593438825363043 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 4 2 191593438825363043 191593438825363043 191593438825363043 endpoint_19_52_p4 endpoint_19_52_w4
private theorem endpoint_19_52_w6 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 6 2 191593438825363043 = some 191593438825363043 := by decide +kernel
private theorem endpoint_19_52_p8 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 8 191593438825363043 = some 191593438825363043 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 6 2 191593438825363043 191593438825363043 191593438825363043 endpoint_19_52_p6 endpoint_19_52_w6
private theorem endpoint_19_52_w8 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 8 2 191593438825363043 = some 191593438825363043 := by decide +kernel
private theorem endpoint_19_52_p10 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 10 191593438825363043 = some 191593438825363043 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 8 2 191593438825363043 191593438825363043 191593438825363043 endpoint_19_52_p8 endpoint_19_52_w8
private theorem endpoint_19_52_w10 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 10 2 191593438825363043 = some 191593438825363043 := by decide +kernel
private theorem endpoint_19_52_p12 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 12 191593438825363043 = some 191593438825363043 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 10 2 191593438825363043 191593438825363043 191593438825363043 endpoint_19_52_p10 endpoint_19_52_w10
private theorem endpoint_19_52_w12 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 12 2 191593438825363043 = some 191593438825363043 := by decide +kernel
private theorem endpoint_19_52_p14 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 14 191593438825363043 = some 191593438825363043 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 12 2 191593438825363043 191593438825363043 191593438825363043 endpoint_19_52_p12 endpoint_19_52_w12
private theorem endpoint_19_52_w14 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 14 2 191593438825363043 = some 191593438825363043 := by decide +kernel
private theorem endpoint_19_52_p16 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 16 191593438825363043 = some 191593438825363043 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 14 2 191593438825363043 191593438825363043 191593438825363043 endpoint_19_52_p14 endpoint_19_52_w14
private theorem endpoint_19_52_w16 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 16 2 191593438825363043 = some 191593438825363043 := by decide +kernel
private theorem endpoint_19_52_p18 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 18 191593438825363043 = some 191593438825363043 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 16 2 191593438825363043 191593438825363043 191593438825363043 endpoint_19_52_p16 endpoint_19_52_w16
def endpoint_19_52 : CertifiedEndpoint :=
  ⟨⟨19, 52, 1731⟩, 191593438825363043, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_52_flag endpoint_19_52_sources 18 191593438825363043 191593438825363043 rfl endpoint_19_52_base endpoint_19_52_p18) (by decide)⟩
private def endpoint_19_53_flag : Flag := ⟨19, 53, 1678⟩
private def endpoint_19_53_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_53_base : receiptBase endpoint_19_53_flag endpoint_19_53_sources = some 188911419244534268 := by decide +kernel
private theorem endpoint_19_53_w0 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 2 188911419244534268 = some 188911419244534268 := by decide +kernel
private theorem endpoint_19_53_w2 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 2 2 188911419244534268 = some 188911419244534268 := by decide +kernel
private theorem endpoint_19_53_p4 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 4 188911419244534268 = some 188911419244534268 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 2 2 188911419244534268 188911419244534268 188911419244534268 endpoint_19_53_w0 endpoint_19_53_w2
private theorem endpoint_19_53_w4 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 4 2 188911419244534268 = some 188911419244534268 := by decide +kernel
private theorem endpoint_19_53_p6 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 6 188911419244534268 = some 188911419244534268 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 4 2 188911419244534268 188911419244534268 188911419244534268 endpoint_19_53_p4 endpoint_19_53_w4
private theorem endpoint_19_53_w6 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 6 2 188911419244534268 = some 188911419244534268 := by decide +kernel
private theorem endpoint_19_53_p8 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 8 188911419244534268 = some 188911419244534268 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 6 2 188911419244534268 188911419244534268 188911419244534268 endpoint_19_53_p6 endpoint_19_53_w6
private theorem endpoint_19_53_w8 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 8 2 188911419244534268 = some 188911419244534268 := by decide +kernel
private theorem endpoint_19_53_p10 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 10 188911419244534268 = some 188911419244534268 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 8 2 188911419244534268 188911419244534268 188911419244534268 endpoint_19_53_p8 endpoint_19_53_w8
private theorem endpoint_19_53_w10 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 10 2 188911419244534268 = some 188911419244534268 := by decide +kernel
private theorem endpoint_19_53_p12 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 12 188911419244534268 = some 188911419244534268 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 10 2 188911419244534268 188911419244534268 188911419244534268 endpoint_19_53_p10 endpoint_19_53_w10
private theorem endpoint_19_53_w12 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 12 2 188911419244534268 = some 188911419244534268 := by decide +kernel
private theorem endpoint_19_53_p14 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 14 188911419244534268 = some 188911419244534268 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 12 2 188911419244534268 188911419244534268 188911419244534268 endpoint_19_53_p12 endpoint_19_53_w12
private theorem endpoint_19_53_w14 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 14 2 188911419244534268 = some 188911419244534268 := by decide +kernel
private theorem endpoint_19_53_p16 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 16 188911419244534268 = some 188911419244534268 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 14 2 188911419244534268 188911419244534268 188911419244534268 endpoint_19_53_p14 endpoint_19_53_w14
private theorem endpoint_19_53_w16 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 16 2 188911419244534268 = some 188911419244534268 := by decide +kernel
private theorem endpoint_19_53_p18 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 18 188911419244534268 = some 188911419244534268 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 16 2 188911419244534268 188911419244534268 188911419244534268 endpoint_19_53_p16 endpoint_19_53_w16
def endpoint_19_53 : CertifiedEndpoint :=
  ⟨⟨19, 53, 1678⟩, 188911419244534268, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_53_flag endpoint_19_53_sources 18 188911419244534268 188911419244534268 rfl endpoint_19_53_base endpoint_19_53_p18) (by decide)⟩
private def endpoint_19_54_flag : Flag := ⟨19, 54, 1624⟩
private def endpoint_19_54_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_54_base : receiptBase endpoint_19_54_flag endpoint_19_54_sources = some 185920419703706200 := by decide +kernel
private theorem endpoint_19_54_w0 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 2 185920419703706200 = some 185920419703706200 := by decide +kernel
private theorem endpoint_19_54_w2 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 2 2 185920419703706200 = some 185920419703706200 := by decide +kernel
private theorem endpoint_19_54_p4 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 4 185920419703706200 = some 185920419703706200 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 2 2 185920419703706200 185920419703706200 185920419703706200 endpoint_19_54_w0 endpoint_19_54_w2
private theorem endpoint_19_54_w4 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 4 2 185920419703706200 = some 185920419703706200 := by decide +kernel
private theorem endpoint_19_54_p6 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 6 185920419703706200 = some 185920419703706200 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 4 2 185920419703706200 185920419703706200 185920419703706200 endpoint_19_54_p4 endpoint_19_54_w4
private theorem endpoint_19_54_w6 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 6 2 185920419703706200 = some 185920419703706200 := by decide +kernel
private theorem endpoint_19_54_p8 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 8 185920419703706200 = some 185920419703706200 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 6 2 185920419703706200 185920419703706200 185920419703706200 endpoint_19_54_p6 endpoint_19_54_w6
private theorem endpoint_19_54_w8 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 8 2 185920419703706200 = some 185920419703706200 := by decide +kernel
private theorem endpoint_19_54_p10 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 10 185920419703706200 = some 185920419703706200 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 8 2 185920419703706200 185920419703706200 185920419703706200 endpoint_19_54_p8 endpoint_19_54_w8
private theorem endpoint_19_54_w10 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 10 2 185920419703706200 = some 185920419703706200 := by decide +kernel
private theorem endpoint_19_54_p12 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 12 185920419703706200 = some 185920419703706200 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 10 2 185920419703706200 185920419703706200 185920419703706200 endpoint_19_54_p10 endpoint_19_54_w10
private theorem endpoint_19_54_w12 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 12 2 185920419703706200 = some 185920419703706200 := by decide +kernel
private theorem endpoint_19_54_p14 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 14 185920419703706200 = some 185920419703706200 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 12 2 185920419703706200 185920419703706200 185920419703706200 endpoint_19_54_p12 endpoint_19_54_w12
private theorem endpoint_19_54_w14 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 14 2 185920419703706200 = some 185920419703706200 := by decide +kernel
private theorem endpoint_19_54_p16 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 16 185920419703706200 = some 185920419703706200 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 14 2 185920419703706200 185920419703706200 185920419703706200 endpoint_19_54_p14 endpoint_19_54_w14
private theorem endpoint_19_54_w16 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 16 2 185920419703706200 = some 185920419703706200 := by decide +kernel
private theorem endpoint_19_54_p18 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 18 185920419703706200 = some 185920419703706200 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 16 2 185920419703706200 185920419703706200 185920419703706200 endpoint_19_54_p16 endpoint_19_54_w16
def endpoint_19_54 : CertifiedEndpoint :=
  ⟨⟨19, 54, 1624⟩, 185920419703706200, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_54_flag endpoint_19_54_sources 18 185920419703706200 185920419703706200 rfl endpoint_19_54_base endpoint_19_54_p18) (by decide)⟩
private def endpoint_19_55_flag : Flag := ⟨19, 55, 1569⟩
private def endpoint_19_55_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_19_55_base : receiptBase endpoint_19_55_flag endpoint_19_55_sources = some 182749084381876329 := by decide +kernel
private theorem endpoint_19_55_w0 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 2 182749084381876329 = some 182749084381876329 := by decide +kernel
private theorem endpoint_19_55_w2 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 2 2 182749084381876329 = some 182749084381876329 := by decide +kernel
private theorem endpoint_19_55_p4 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 4 182749084381876329 = some 182749084381876329 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 2 2 182749084381876329 182749084381876329 182749084381876329 endpoint_19_55_w0 endpoint_19_55_w2
private theorem endpoint_19_55_w4 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 4 2 182749084381876329 = some 182749084381876329 := by decide +kernel
private theorem endpoint_19_55_p6 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 6 182749084381876329 = some 182749084381876329 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 4 2 182749084381876329 182749084381876329 182749084381876329 endpoint_19_55_p4 endpoint_19_55_w4
private theorem endpoint_19_55_w6 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 6 2 182749084381876329 = some 182749084381876329 := by decide +kernel
private theorem endpoint_19_55_p8 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 8 182749084381876329 = some 182749084381876329 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 6 2 182749084381876329 182749084381876329 182749084381876329 endpoint_19_55_p6 endpoint_19_55_w6
private theorem endpoint_19_55_w8 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 8 2 182749084381876329 = some 182749084381876329 := by decide +kernel
private theorem endpoint_19_55_p10 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 10 182749084381876329 = some 182749084381876329 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 8 2 182749084381876329 182749084381876329 182749084381876329 endpoint_19_55_p8 endpoint_19_55_w8
private theorem endpoint_19_55_w10 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 10 2 182749084381876329 = some 182749084381876329 := by decide +kernel
private theorem endpoint_19_55_p12 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 12 182749084381876329 = some 182749084381876329 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 10 2 182749084381876329 182749084381876329 182749084381876329 endpoint_19_55_p10 endpoint_19_55_w10
private theorem endpoint_19_55_w12 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 12 2 182749084381876329 = some 182749084381876329 := by decide +kernel
private theorem endpoint_19_55_p14 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 14 182749084381876329 = some 182749084381876329 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 12 2 182749084381876329 182749084381876329 182749084381876329 endpoint_19_55_p12 endpoint_19_55_w12
private theorem endpoint_19_55_w14 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 14 2 182749084381876329 = some 182749084381876329 := by decide +kernel
private theorem endpoint_19_55_p16 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 16 182749084381876329 = some 182749084381876329 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 14 2 182749084381876329 182749084381876329 182749084381876329 endpoint_19_55_p14 endpoint_19_55_w14
private theorem endpoint_19_55_w16 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 16 2 182749084381876329 = some 182749084381876329 := by decide +kernel
private theorem endpoint_19_55_p18 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 18 182749084381876329 = some 182749084381876329 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 16 2 182749084381876329 182749084381876329 182749084381876329 endpoint_19_55_p16 endpoint_19_55_w16
def endpoint_19_55 : CertifiedEndpoint :=
  ⟨⟨19, 55, 1569⟩, 182749084381876329, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_19_55_flag endpoint_19_55_sources 18 182749084381876329 182749084381876329 rfl endpoint_19_55_base endpoint_19_55_p18) (by decide)⟩
private def endpoint_19_56_flag : Flag := ⟨19, 56, 1513⟩
private def endpoint_19_56_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_19_56_base : receiptBase endpoint_19_56_flag endpoint_19_56_sources = some 180902078169698207 := by decide +kernel
private theorem endpoint_19_56_w0 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 2 180902078169698207 = some 180902078169698207 := by decide +kernel
private theorem endpoint_19_56_w2 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 2 2 180902078169698207 = some 180902078169698207 := by decide +kernel
private theorem endpoint_19_56_p4 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 4 180902078169698207 = some 180902078169698207 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 2 2 180902078169698207 180902078169698207 180902078169698207 endpoint_19_56_w0 endpoint_19_56_w2
private theorem endpoint_19_56_w4 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 4 2 180902078169698207 = some 180902078169698207 := by decide +kernel
private theorem endpoint_19_56_p6 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 6 180902078169698207 = some 180902078169698207 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 4 2 180902078169698207 180902078169698207 180902078169698207 endpoint_19_56_p4 endpoint_19_56_w4
private theorem endpoint_19_56_w6 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 6 2 180902078169698207 = some 180902078169698207 := by decide +kernel
private theorem endpoint_19_56_p8 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 8 180902078169698207 = some 180902078169698207 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 6 2 180902078169698207 180902078169698207 180902078169698207 endpoint_19_56_p6 endpoint_19_56_w6
private theorem endpoint_19_56_w8 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 8 2 180902078169698207 = some 180902078169698207 := by decide +kernel
private theorem endpoint_19_56_p10 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 10 180902078169698207 = some 180902078169698207 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 8 2 180902078169698207 180902078169698207 180902078169698207 endpoint_19_56_p8 endpoint_19_56_w8
private theorem endpoint_19_56_w10 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 10 2 180902078169698207 = some 180902078169698207 := by decide +kernel
private theorem endpoint_19_56_p12 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 12 180902078169698207 = some 180902078169698207 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 10 2 180902078169698207 180902078169698207 180902078169698207 endpoint_19_56_p10 endpoint_19_56_w10
private theorem endpoint_19_56_w12 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 12 2 180902078169698207 = some 180902078169698207 := by decide +kernel
private theorem endpoint_19_56_p14 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 14 180902078169698207 = some 180902078169698207 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 12 2 180902078169698207 180902078169698207 180902078169698207 endpoint_19_56_p12 endpoint_19_56_w12
private theorem endpoint_19_56_w14 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 14 2 180902078169698207 = some 180902078169698207 := by decide +kernel
private theorem endpoint_19_56_p16 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 16 180902078169698207 = some 180902078169698207 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 14 2 180902078169698207 180902078169698207 180902078169698207 endpoint_19_56_p14 endpoint_19_56_w14
private theorem endpoint_19_56_w16 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 16 2 180902078169698207 = some 180902078169698207 := by decide +kernel
private theorem endpoint_19_56_p18 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 18 180902078169698207 = some 180902078169698207 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 16 2 180902078169698207 180902078169698207 180902078169698207 endpoint_19_56_p16 endpoint_19_56_w16
def endpoint_19_56 : CertifiedEndpoint :=
  ⟨⟨19, 56, 1513⟩, 180902078169698207, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_19_56_flag endpoint_19_56_sources 18 180902078169698207 180902078169698207 rfl endpoint_19_56_base endpoint_19_56_p18) (by decide)⟩
private def endpoint_19_57_flag : Flag := ⟨19, 57, 1456⟩
private def endpoint_19_57_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_19_57_base : receiptBase endpoint_19_57_flag endpoint_19_57_sources = some 175255996081832115 := by decide +kernel
private theorem endpoint_19_57_w0 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 2 175255996081832115 = some 180498917851795062 := by decide +kernel
private theorem endpoint_19_57_w2 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 2 2 180498917851795062 = some 180498917851795062 := by decide +kernel
private theorem endpoint_19_57_p4 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 4 175255996081832115 = some 180498917851795062 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 2 2 175255996081832115 180498917851795062 180498917851795062 endpoint_19_57_w0 endpoint_19_57_w2
private theorem endpoint_19_57_w4 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 4 2 180498917851795062 = some 180498917851795062 := by decide +kernel
private theorem endpoint_19_57_p6 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 6 175255996081832115 = some 180498917851795062 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 4 2 175255996081832115 180498917851795062 180498917851795062 endpoint_19_57_p4 endpoint_19_57_w4
private theorem endpoint_19_57_w6 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 6 2 180498917851795062 = some 180498917851795062 := by decide +kernel
private theorem endpoint_19_57_p8 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 8 175255996081832115 = some 180498917851795062 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 6 2 175255996081832115 180498917851795062 180498917851795062 endpoint_19_57_p6 endpoint_19_57_w6
private theorem endpoint_19_57_w8 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 8 2 180498917851795062 = some 180498917851795062 := by decide +kernel
private theorem endpoint_19_57_p10 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 10 175255996081832115 = some 180498917851795062 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 8 2 175255996081832115 180498917851795062 180498917851795062 endpoint_19_57_p8 endpoint_19_57_w8
private theorem endpoint_19_57_w10 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 10 2 180498917851795062 = some 180498917851795062 := by decide +kernel
private theorem endpoint_19_57_p12 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 12 175255996081832115 = some 180498917851795062 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 10 2 175255996081832115 180498917851795062 180498917851795062 endpoint_19_57_p10 endpoint_19_57_w10
private theorem endpoint_19_57_w12 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 12 2 180498917851795062 = some 180498917851795062 := by decide +kernel
private theorem endpoint_19_57_p14 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 14 175255996081832115 = some 180498917851795062 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 12 2 175255996081832115 180498917851795062 180498917851795062 endpoint_19_57_p12 endpoint_19_57_w12
private theorem endpoint_19_57_w14 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 14 2 180498917851795062 = some 180498917851795062 := by decide +kernel
private theorem endpoint_19_57_p16 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 16 175255996081832115 = some 180498917851795062 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 14 2 175255996081832115 180498917851795062 180498917851795062 endpoint_19_57_p14 endpoint_19_57_w14
private theorem endpoint_19_57_w16 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 16 2 180498917851795062 = some 180498917851795062 := by decide +kernel
private theorem endpoint_19_57_p18 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 18 175255996081832115 = some 180498917851795062 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 16 2 175255996081832115 180498917851795062 180498917851795062 endpoint_19_57_p16 endpoint_19_57_w16
def endpoint_19_57 : CertifiedEndpoint :=
  ⟨⟨19, 57, 1456⟩, 180498917851795062, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_19_57_flag endpoint_19_57_sources 18 175255996081832115 180498917851795062 rfl endpoint_19_57_base endpoint_19_57_p18) (by decide)⟩
private def endpoint_19_58_flag : Flag := ⟨19, 58, 1398⟩
private def endpoint_19_58_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_19_58_base : receiptBase endpoint_19_58_flag endpoint_19_58_sources = some 172541868576173858 := by decide +kernel
private theorem endpoint_19_58_w0 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 2 172541868576173858 = some 173108175515640248 := by decide +kernel
private theorem endpoint_19_58_w2 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 2 2 173108175515640248 = some 173108175515640248 := by decide +kernel
private theorem endpoint_19_58_p4 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 4 172541868576173858 = some 173108175515640248 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 2 2 172541868576173858 173108175515640248 173108175515640248 endpoint_19_58_w0 endpoint_19_58_w2
private theorem endpoint_19_58_w4 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 4 2 173108175515640248 = some 173108175515640248 := by decide +kernel
private theorem endpoint_19_58_p6 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 6 172541868576173858 = some 173108175515640248 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 4 2 172541868576173858 173108175515640248 173108175515640248 endpoint_19_58_p4 endpoint_19_58_w4
private theorem endpoint_19_58_w6 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 6 2 173108175515640248 = some 173108175515640248 := by decide +kernel
private theorem endpoint_19_58_p8 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 8 172541868576173858 = some 173108175515640248 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 6 2 172541868576173858 173108175515640248 173108175515640248 endpoint_19_58_p6 endpoint_19_58_w6
private theorem endpoint_19_58_w8 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 8 2 173108175515640248 = some 173108175515640248 := by decide +kernel
private theorem endpoint_19_58_p10 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 10 172541868576173858 = some 173108175515640248 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 8 2 172541868576173858 173108175515640248 173108175515640248 endpoint_19_58_p8 endpoint_19_58_w8
private theorem endpoint_19_58_w10 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 10 2 173108175515640248 = some 173108175515640248 := by decide +kernel
private theorem endpoint_19_58_p12 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 12 172541868576173858 = some 173108175515640248 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 10 2 172541868576173858 173108175515640248 173108175515640248 endpoint_19_58_p10 endpoint_19_58_w10
private theorem endpoint_19_58_w12 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 12 2 173108175515640248 = some 173108175515640248 := by decide +kernel
private theorem endpoint_19_58_p14 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 14 172541868576173858 = some 173108175515640248 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 12 2 172541868576173858 173108175515640248 173108175515640248 endpoint_19_58_p12 endpoint_19_58_w12
private theorem endpoint_19_58_w14 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 14 2 173108175515640248 = some 173108175515640248 := by decide +kernel
private theorem endpoint_19_58_p16 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 16 172541868576173858 = some 173108175515640248 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 14 2 172541868576173858 173108175515640248 173108175515640248 endpoint_19_58_p14 endpoint_19_58_w14
private theorem endpoint_19_58_w16 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 16 2 173108175515640248 = some 173108175515640248 := by decide +kernel
private theorem endpoint_19_58_p18 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 18 172541868576173858 = some 173108175515640248 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 16 2 172541868576173858 173108175515640248 173108175515640248 endpoint_19_58_p16 endpoint_19_58_w16
def endpoint_19_58 : CertifiedEndpoint :=
  ⟨⟨19, 58, 1398⟩, 173108175515640248, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_19_58_flag endpoint_19_58_sources 18 172541868576173858 173108175515640248 rfl endpoint_19_58_base endpoint_19_58_p18) (by decide)⟩
private def endpoint_19_59_flag : Flag := ⟨19, 59, 1338⟩
private def endpoint_19_59_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_19_59_base : receiptBase endpoint_19_59_flag endpoint_19_59_sources = some 167731497325428436 := by decide +kernel
private theorem endpoint_19_59_w0 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 2 167731497325428436 = some 172340102543727795 := by decide +kernel
private theorem endpoint_19_59_w2 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 2 2 172340102543727795 = some 172340102543727795 := by decide +kernel
private theorem endpoint_19_59_p4 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 4 167731497325428436 = some 172340102543727795 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 2 2 167731497325428436 172340102543727795 172340102543727795 endpoint_19_59_w0 endpoint_19_59_w2
private theorem endpoint_19_59_w4 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 4 2 172340102543727795 = some 172340102543727795 := by decide +kernel
private theorem endpoint_19_59_p6 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 6 167731497325428436 = some 172340102543727795 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 4 2 167731497325428436 172340102543727795 172340102543727795 endpoint_19_59_p4 endpoint_19_59_w4
private theorem endpoint_19_59_w6 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 6 2 172340102543727795 = some 172340102543727795 := by decide +kernel
private theorem endpoint_19_59_p8 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 8 167731497325428436 = some 172340102543727795 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 6 2 167731497325428436 172340102543727795 172340102543727795 endpoint_19_59_p6 endpoint_19_59_w6
private theorem endpoint_19_59_w8 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 8 2 172340102543727795 = some 172340102543727795 := by decide +kernel
private theorem endpoint_19_59_p10 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 10 167731497325428436 = some 172340102543727795 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 8 2 167731497325428436 172340102543727795 172340102543727795 endpoint_19_59_p8 endpoint_19_59_w8
private theorem endpoint_19_59_w10 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 10 2 172340102543727795 = some 172340102543727795 := by decide +kernel
private theorem endpoint_19_59_p12 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 12 167731497325428436 = some 172340102543727795 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 10 2 167731497325428436 172340102543727795 172340102543727795 endpoint_19_59_p10 endpoint_19_59_w10
private theorem endpoint_19_59_w12 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 12 2 172340102543727795 = some 172340102543727795 := by decide +kernel
private theorem endpoint_19_59_p14 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 14 167731497325428436 = some 172340102543727795 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 12 2 167731497325428436 172340102543727795 172340102543727795 endpoint_19_59_p12 endpoint_19_59_w12
private theorem endpoint_19_59_w14 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 14 2 172340102543727795 = some 172340102543727795 := by decide +kernel
private theorem endpoint_19_59_p16 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 16 167731497325428436 = some 172340102543727795 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 14 2 167731497325428436 172340102543727795 172340102543727795 endpoint_19_59_p14 endpoint_19_59_w14
private theorem endpoint_19_59_w16 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 16 2 172340102543727795 = some 172340102543727795 := by decide +kernel
private theorem endpoint_19_59_p18 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 18 167731497325428436 = some 172340102543727795 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 16 2 167731497325428436 172340102543727795 172340102543727795 endpoint_19_59_p16 endpoint_19_59_w16
def endpoint_19_59 : CertifiedEndpoint :=
  ⟨⟨19, 59, 1338⟩, 172340102543727795, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_19_59_flag endpoint_19_59_sources 18 167731497325428436 172340102543727795 rfl endpoint_19_59_base endpoint_19_59_p18) (by decide)⟩
private def endpoint_19_60_flag : Flag := ⟨19, 60, 1278⟩
private def endpoint_19_60_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_19_60_base : receiptBase endpoint_19_60_flag endpoint_19_60_sources = some 162697486711014861 := by decide +kernel
private theorem endpoint_19_60_w0 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 0 2 162697486711014861 = some 171389179652927096 := by decide +kernel
private theorem endpoint_19_60_w2 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 2 2 171389179652927096 = some 171389179652927096 := by decide +kernel
private theorem endpoint_19_60_p4 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 0 4 162697486711014861 = some 171389179652927096 :=
  join_receipt_window endpoint_19_60_flag endpoint_19_60_sources 0 2 2 162697486711014861 171389179652927096 171389179652927096 endpoint_19_60_w0 endpoint_19_60_w2
private theorem endpoint_19_60_w4 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 4 2 171389179652927096 = some 171389179652927096 := by decide +kernel
private theorem endpoint_19_60_p6 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 0 6 162697486711014861 = some 171389179652927096 :=
  join_receipt_window endpoint_19_60_flag endpoint_19_60_sources 0 4 2 162697486711014861 171389179652927096 171389179652927096 endpoint_19_60_p4 endpoint_19_60_w4
private theorem endpoint_19_60_w6 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 6 2 171389179652927096 = some 171389179652927096 := by decide +kernel
private theorem endpoint_19_60_p8 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 0 8 162697486711014861 = some 171389179652927096 :=
  join_receipt_window endpoint_19_60_flag endpoint_19_60_sources 0 6 2 162697486711014861 171389179652927096 171389179652927096 endpoint_19_60_p6 endpoint_19_60_w6
private theorem endpoint_19_60_w8 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 8 2 171389179652927096 = some 171389179652927096 := by decide +kernel
private theorem endpoint_19_60_p10 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 0 10 162697486711014861 = some 171389179652927096 :=
  join_receipt_window endpoint_19_60_flag endpoint_19_60_sources 0 8 2 162697486711014861 171389179652927096 171389179652927096 endpoint_19_60_p8 endpoint_19_60_w8
private theorem endpoint_19_60_w10 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 10 2 171389179652927096 = some 171389179652927096 := by decide +kernel
private theorem endpoint_19_60_p12 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 0 12 162697486711014861 = some 171389179652927096 :=
  join_receipt_window endpoint_19_60_flag endpoint_19_60_sources 0 10 2 162697486711014861 171389179652927096 171389179652927096 endpoint_19_60_p10 endpoint_19_60_w10
private theorem endpoint_19_60_w12 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 12 2 171389179652927096 = some 171389179652927096 := by decide +kernel
private theorem endpoint_19_60_p14 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 0 14 162697486711014861 = some 171389179652927096 :=
  join_receipt_window endpoint_19_60_flag endpoint_19_60_sources 0 12 2 162697486711014861 171389179652927096 171389179652927096 endpoint_19_60_p12 endpoint_19_60_w12
private theorem endpoint_19_60_w14 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 14 2 171389179652927096 = some 171389179652927096 := by decide +kernel
private theorem endpoint_19_60_p16 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 0 16 162697486711014861 = some 171389179652927096 :=
  join_receipt_window endpoint_19_60_flag endpoint_19_60_sources 0 14 2 162697486711014861 171389179652927096 171389179652927096 endpoint_19_60_p14 endpoint_19_60_w14
private theorem endpoint_19_60_w16 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 16 2 171389179652927096 = some 171389179652927096 := by decide +kernel
private theorem endpoint_19_60_p18 : receiptWindow endpoint_19_60_flag endpoint_19_60_sources 0 18 162697486711014861 = some 171389179652927096 :=
  join_receipt_window endpoint_19_60_flag endpoint_19_60_sources 0 16 2 162697486711014861 171389179652927096 171389179652927096 endpoint_19_60_p16 endpoint_19_60_w16
def endpoint_19_60 : CertifiedEndpoint :=
  ⟨⟨19, 60, 1278⟩, 171389179652927096, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_19_60_flag endpoint_19_60_sources 18 162697486711014861 171389179652927096 rfl endpoint_19_60_base endpoint_19_60_p18) (by decide)⟩
private def endpoint_19_61_flag : Flag := ⟨19, 61, 1216⟩
private def endpoint_19_61_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_19_61_base : receiptBase endpoint_19_61_flag endpoint_19_61_sources = some 157185506912570986 := by decide +kernel
private theorem endpoint_19_61_w0 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 0 2 157185506912570986 = some 170106006915825489 := by decide +kernel
private theorem endpoint_19_61_w2 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 2 2 170106006915825489 = some 170106006915825489 := by decide +kernel
private theorem endpoint_19_61_p4 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 0 4 157185506912570986 = some 170106006915825489 :=
  join_receipt_window endpoint_19_61_flag endpoint_19_61_sources 0 2 2 157185506912570986 170106006915825489 170106006915825489 endpoint_19_61_w0 endpoint_19_61_w2
private theorem endpoint_19_61_w4 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 4 2 170106006915825489 = some 170106006915825489 := by decide +kernel
private theorem endpoint_19_61_p6 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 0 6 157185506912570986 = some 170106006915825489 :=
  join_receipt_window endpoint_19_61_flag endpoint_19_61_sources 0 4 2 157185506912570986 170106006915825489 170106006915825489 endpoint_19_61_p4 endpoint_19_61_w4
private theorem endpoint_19_61_w6 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 6 2 170106006915825489 = some 170106006915825489 := by decide +kernel
private theorem endpoint_19_61_p8 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 0 8 157185506912570986 = some 170106006915825489 :=
  join_receipt_window endpoint_19_61_flag endpoint_19_61_sources 0 6 2 157185506912570986 170106006915825489 170106006915825489 endpoint_19_61_p6 endpoint_19_61_w6
private theorem endpoint_19_61_w8 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 8 2 170106006915825489 = some 170106006915825489 := by decide +kernel
private theorem endpoint_19_61_p10 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 0 10 157185506912570986 = some 170106006915825489 :=
  join_receipt_window endpoint_19_61_flag endpoint_19_61_sources 0 8 2 157185506912570986 170106006915825489 170106006915825489 endpoint_19_61_p8 endpoint_19_61_w8
private theorem endpoint_19_61_w10 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 10 2 170106006915825489 = some 170106006915825489 := by decide +kernel
private theorem endpoint_19_61_p12 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 0 12 157185506912570986 = some 170106006915825489 :=
  join_receipt_window endpoint_19_61_flag endpoint_19_61_sources 0 10 2 157185506912570986 170106006915825489 170106006915825489 endpoint_19_61_p10 endpoint_19_61_w10
private theorem endpoint_19_61_w12 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 12 2 170106006915825489 = some 170106006915825489 := by decide +kernel
private theorem endpoint_19_61_p14 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 0 14 157185506912570986 = some 170106006915825489 :=
  join_receipt_window endpoint_19_61_flag endpoint_19_61_sources 0 12 2 157185506912570986 170106006915825489 170106006915825489 endpoint_19_61_p12 endpoint_19_61_w12
private theorem endpoint_19_61_w14 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 14 2 170106006915825489 = some 170106006915825489 := by decide +kernel
private theorem endpoint_19_61_p16 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 0 16 157185506912570986 = some 170106006915825489 :=
  join_receipt_window endpoint_19_61_flag endpoint_19_61_sources 0 14 2 157185506912570986 170106006915825489 170106006915825489 endpoint_19_61_p14 endpoint_19_61_w14
private theorem endpoint_19_61_w16 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 16 2 170106006915825489 = some 170106006915825489 := by decide +kernel
private theorem endpoint_19_61_p18 : receiptWindow endpoint_19_61_flag endpoint_19_61_sources 0 18 157185506912570986 = some 170106006915825489 :=
  join_receipt_window endpoint_19_61_flag endpoint_19_61_sources 0 16 2 157185506912570986 170106006915825489 170106006915825489 endpoint_19_61_p16 endpoint_19_61_w16
def endpoint_19_61 : CertifiedEndpoint :=
  ⟨⟨19, 61, 1216⟩, 170106006915825489, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_19_61_flag endpoint_19_61_sources 18 157185506912570986 170106006915825489 rfl endpoint_19_61_base endpoint_19_61_p18) (by decide)⟩
private def endpoint_19_62_flag : Flag := ⟨19, 62, 1153⟩
private def endpoint_19_62_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_19_62_base : receiptBase endpoint_19_62_flag endpoint_19_62_sources = some 151313480893489220 := by decide +kernel
private theorem endpoint_19_62_w0 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 0 2 151313480893489220 = some 168557853816911570 := by decide +kernel
private theorem endpoint_19_62_w2 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 2 2 168557853816911570 = some 168557853816911570 := by decide +kernel
private theorem endpoint_19_62_p4 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 0 4 151313480893489220 = some 168557853816911570 :=
  join_receipt_window endpoint_19_62_flag endpoint_19_62_sources 0 2 2 151313480893489220 168557853816911570 168557853816911570 endpoint_19_62_w0 endpoint_19_62_w2
private theorem endpoint_19_62_w4 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 4 2 168557853816911570 = some 168557853816911570 := by decide +kernel
private theorem endpoint_19_62_p6 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 0 6 151313480893489220 = some 168557853816911570 :=
  join_receipt_window endpoint_19_62_flag endpoint_19_62_sources 0 4 2 151313480893489220 168557853816911570 168557853816911570 endpoint_19_62_p4 endpoint_19_62_w4
private theorem endpoint_19_62_w6 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 6 2 168557853816911570 = some 168557853816911570 := by decide +kernel
private theorem endpoint_19_62_p8 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 0 8 151313480893489220 = some 168557853816911570 :=
  join_receipt_window endpoint_19_62_flag endpoint_19_62_sources 0 6 2 151313480893489220 168557853816911570 168557853816911570 endpoint_19_62_p6 endpoint_19_62_w6
private theorem endpoint_19_62_w8 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 8 2 168557853816911570 = some 168557853816911570 := by decide +kernel
private theorem endpoint_19_62_p10 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 0 10 151313480893489220 = some 168557853816911570 :=
  join_receipt_window endpoint_19_62_flag endpoint_19_62_sources 0 8 2 151313480893489220 168557853816911570 168557853816911570 endpoint_19_62_p8 endpoint_19_62_w8
private theorem endpoint_19_62_w10 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 10 2 168557853816911570 = some 168557853816911570 := by decide +kernel
private theorem endpoint_19_62_p12 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 0 12 151313480893489220 = some 168557853816911570 :=
  join_receipt_window endpoint_19_62_flag endpoint_19_62_sources 0 10 2 151313480893489220 168557853816911570 168557853816911570 endpoint_19_62_p10 endpoint_19_62_w10
private theorem endpoint_19_62_w12 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 12 2 168557853816911570 = some 168557853816911570 := by decide +kernel
private theorem endpoint_19_62_p14 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 0 14 151313480893489220 = some 168557853816911570 :=
  join_receipt_window endpoint_19_62_flag endpoint_19_62_sources 0 12 2 151313480893489220 168557853816911570 168557853816911570 endpoint_19_62_p12 endpoint_19_62_w12
private theorem endpoint_19_62_w14 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 14 2 168557853816911570 = some 168557853816911570 := by decide +kernel
private theorem endpoint_19_62_p16 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 0 16 151313480893489220 = some 168557853816911570 :=
  join_receipt_window endpoint_19_62_flag endpoint_19_62_sources 0 14 2 151313480893489220 168557853816911570 168557853816911570 endpoint_19_62_p14 endpoint_19_62_w14
private theorem endpoint_19_62_w16 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 16 2 168557853816911570 = some 168557853816911570 := by decide +kernel
private theorem endpoint_19_62_p18 : receiptWindow endpoint_19_62_flag endpoint_19_62_sources 0 18 151313480893489220 = some 168557853816911570 :=
  join_receipt_window endpoint_19_62_flag endpoint_19_62_sources 0 16 2 151313480893489220 168557853816911570 168557853816911570 endpoint_19_62_p16 endpoint_19_62_w16
def endpoint_19_62 : CertifiedEndpoint :=
  ⟨⟨19, 62, 1153⟩, 168557853816911570, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_19_62_flag endpoint_19_62_sources 18 151313480893489220 168557853816911570 rfl endpoint_19_62_base endpoint_19_62_p18) (by decide)⟩
private def endpoint_19_63_flag : Flag := ⟨19, 63, 1088⟩
private def endpoint_19_63_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_19_63_base : receiptBase endpoint_19_63_flag endpoint_19_63_sources = some 144945001796799823 := by decide +kernel
private theorem endpoint_19_63_w0 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 0 2 144945001796799823 = some 166662589913261273 := by decide +kernel
private theorem endpoint_19_63_w2 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 2 2 166662589913261273 = some 166662589913261273 := by decide +kernel
private theorem endpoint_19_63_p4 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 0 4 144945001796799823 = some 166662589913261273 :=
  join_receipt_window endpoint_19_63_flag endpoint_19_63_sources 0 2 2 144945001796799823 166662589913261273 166662589913261273 endpoint_19_63_w0 endpoint_19_63_w2
private theorem endpoint_19_63_w4 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 4 2 166662589913261273 = some 166662589913261273 := by decide +kernel
private theorem endpoint_19_63_p6 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 0 6 144945001796799823 = some 166662589913261273 :=
  join_receipt_window endpoint_19_63_flag endpoint_19_63_sources 0 4 2 144945001796799823 166662589913261273 166662589913261273 endpoint_19_63_p4 endpoint_19_63_w4
private theorem endpoint_19_63_w6 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 6 2 166662589913261273 = some 166662589913261273 := by decide +kernel
private theorem endpoint_19_63_p8 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 0 8 144945001796799823 = some 166662589913261273 :=
  join_receipt_window endpoint_19_63_flag endpoint_19_63_sources 0 6 2 144945001796799823 166662589913261273 166662589913261273 endpoint_19_63_p6 endpoint_19_63_w6
private theorem endpoint_19_63_w8 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 8 2 166662589913261273 = some 166662589913261273 := by decide +kernel
private theorem endpoint_19_63_p10 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 0 10 144945001796799823 = some 166662589913261273 :=
  join_receipt_window endpoint_19_63_flag endpoint_19_63_sources 0 8 2 144945001796799823 166662589913261273 166662589913261273 endpoint_19_63_p8 endpoint_19_63_w8
private theorem endpoint_19_63_w10 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 10 2 166662589913261273 = some 166662589913261273 := by decide +kernel
private theorem endpoint_19_63_p12 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 0 12 144945001796799823 = some 166662589913261273 :=
  join_receipt_window endpoint_19_63_flag endpoint_19_63_sources 0 10 2 144945001796799823 166662589913261273 166662589913261273 endpoint_19_63_p10 endpoint_19_63_w10
private theorem endpoint_19_63_w12 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 12 2 166662589913261273 = some 166662589913261273 := by decide +kernel
private theorem endpoint_19_63_p14 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 0 14 144945001796799823 = some 166662589913261273 :=
  join_receipt_window endpoint_19_63_flag endpoint_19_63_sources 0 12 2 144945001796799823 166662589913261273 166662589913261273 endpoint_19_63_p12 endpoint_19_63_w12
private theorem endpoint_19_63_w14 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 14 2 166662589913261273 = some 166662589913261273 := by decide +kernel
private theorem endpoint_19_63_p16 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 0 16 144945001796799823 = some 166662589913261273 :=
  join_receipt_window endpoint_19_63_flag endpoint_19_63_sources 0 14 2 144945001796799823 166662589913261273 166662589913261273 endpoint_19_63_p14 endpoint_19_63_w14
private theorem endpoint_19_63_w16 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 16 2 166662589913261273 = some 166662589913261273 := by decide +kernel
private theorem endpoint_19_63_p18 : receiptWindow endpoint_19_63_flag endpoint_19_63_sources 0 18 144945001796799823 = some 166662589913261273 :=
  join_receipt_window endpoint_19_63_flag endpoint_19_63_sources 0 16 2 144945001796799823 166662589913261273 166662589913261273 endpoint_19_63_p16 endpoint_19_63_w16
def endpoint_19_63 : CertifiedEndpoint :=
  ⟨⟨19, 63, 1088⟩, 166662589913261273, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_19_63_flag endpoint_19_63_sources 18 144945001796799823 166662589913261273 rfl endpoint_19_63_base endpoint_19_63_p18) (by decide)⟩
def endpoint_19_64 : CertifiedEndpoint :=
  ⟨⟨19, 64, 1022⟩, 254118958828714790, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_65 : CertifiedEndpoint :=
  ⟨⟨19, 65, 955⟩, 241091507000461284, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_66 : CertifiedEndpoint :=
  ⟨⟨19, 66, 887⟩, 227151807228547067, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_67 : CertifiedEndpoint :=
  ⟨⟨19, 67, 817⟩, 212013283550244826, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_68 : CertifiedEndpoint :=
  ⟨⟨19, 68, 745⟩, 195647279233603413, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_69 : CertifiedEndpoint :=
  ⟨⟨19, 69, 672⟩, 178306937387407135, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_70 : CertifiedEndpoint :=
  ⟨⟨19, 70, 597⟩, 159691353682953105, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_71 : CertifiedEndpoint :=
  ⟨⟨19, 71, 521⟩, 140063223473009346, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_72 : CertifiedEndpoint :=
  ⟨⟨19, 72, 442⟩, 118815961978178226, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_73 : CertifiedEndpoint :=
  ⟨⟨19, 73, 362⟩, 96508392757938797, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_74 : CertifiedEndpoint :=
  ⟨⟨19, 74, 281⟩, 73126187446315485, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_75 : CertifiedEndpoint :=
  ⟨⟨19, 75, 197⟩, 48034104531959510, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_76 : CertifiedEndpoint :=
  ⟨⟨19, 76, 111⟩, 21504391611622611, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_20 : CertifiedEndpoint :=
  ⟨⟨20, 20, 2752⟩, 149421365874478232, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_21 : CertifiedEndpoint :=
  ⟨⟨20, 21, 2718⟩, 152035277906703678, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_22 : CertifiedEndpoint :=
  ⟨⟨20, 22, 2683⟩, 154478555176581833, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_23 : CertifiedEndpoint :=
  ⟨⟨20, 23, 2648⟩, 165668448477222653, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_24 : CertifiedEndpoint :=
  ⟨⟨20, 24, 2613⟩, 176500940109064663, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_25 : CertifiedEndpoint :=
  ⟨⟨20, 25, 2577⟩, 186903030944417862, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_26 : CertifiedEndpoint :=
  ⟨⟨20, 26, 2540⟩, 196859619504318920, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_27 : CertifiedEndpoint :=
  ⟨⟨20, 27, 2503⟩, 206438671090136728, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_28 : CertifiedEndpoint :=
  ⟨⟨20, 28, 2466⟩, 215640185701871286, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_29 : CertifiedEndpoint :=
  ⟨⟨20, 29, 2428⟩, 224371028906548153, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_30 : CertifiedEndpoint :=
  ⟨⟨20, 30, 2389⟩, 232616099225203999, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_31 : CertifiedEndpoint :=
  ⟨⟨20, 31, 2350⟩, 240463497264492155, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_32 : CertifiedEndpoint :=
  ⟨⟨20, 32, 2310⟩, 247804987112474850, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_33 : CertifiedEndpoint :=
  ⟨⟨20, 33, 2269⟩, 254625467290188754, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_34 : CertifiedEndpoint :=
  ⟨⟨20, 34, 2228⟩, 261028139883250528, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_20_35_flag : Flag := ⟨20, 35, 2187⟩
private def endpoint_20_35_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_35_base : receiptBase endpoint_20_35_flag endpoint_20_35_sources = some 172460843354259478 := by decide +kernel
private theorem endpoint_20_35_w0 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 2 172460843354259478 = some 172460843354259478 := by decide +kernel
private theorem endpoint_20_35_w2 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 2 2 172460843354259478 = some 172460843354259478 := by decide +kernel
private theorem endpoint_20_35_p4 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 4 172460843354259478 = some 172460843354259478 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 2 2 172460843354259478 172460843354259478 172460843354259478 endpoint_20_35_w0 endpoint_20_35_w2
private theorem endpoint_20_35_w4 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 4 2 172460843354259478 = some 172460843354259478 := by decide +kernel
private theorem endpoint_20_35_p6 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 6 172460843354259478 = some 172460843354259478 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 4 2 172460843354259478 172460843354259478 172460843354259478 endpoint_20_35_p4 endpoint_20_35_w4
private theorem endpoint_20_35_w6 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 6 2 172460843354259478 = some 172460843354259478 := by decide +kernel
private theorem endpoint_20_35_p8 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 8 172460843354259478 = some 172460843354259478 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 6 2 172460843354259478 172460843354259478 172460843354259478 endpoint_20_35_p6 endpoint_20_35_w6
private theorem endpoint_20_35_w8 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 8 2 172460843354259478 = some 172460843354259478 := by decide +kernel
private theorem endpoint_20_35_p10 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 10 172460843354259478 = some 172460843354259478 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 8 2 172460843354259478 172460843354259478 172460843354259478 endpoint_20_35_p8 endpoint_20_35_w8
private theorem endpoint_20_35_w10 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 10 2 172460843354259478 = some 172460843354259478 := by decide +kernel
private theorem endpoint_20_35_p12 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 12 172460843354259478 = some 172460843354259478 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 10 2 172460843354259478 172460843354259478 172460843354259478 endpoint_20_35_p10 endpoint_20_35_w10
private theorem endpoint_20_35_w12 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 12 2 172460843354259478 = some 172460843354259478 := by decide +kernel
private theorem endpoint_20_35_p14 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 14 172460843354259478 = some 172460843354259478 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 12 2 172460843354259478 172460843354259478 172460843354259478 endpoint_20_35_p12 endpoint_20_35_w12
private theorem endpoint_20_35_w14 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 14 2 172460843354259478 = some 172460843354259478 := by decide +kernel
private theorem endpoint_20_35_p16 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 16 172460843354259478 = some 172460843354259478 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 14 2 172460843354259478 172460843354259478 172460843354259478 endpoint_20_35_p14 endpoint_20_35_w14
private theorem endpoint_20_35_w16 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 16 2 172460843354259478 = some 172460843354259478 := by decide +kernel
private theorem endpoint_20_35_p18 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 18 172460843354259478 = some 172460843354259478 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 16 2 172460843354259478 172460843354259478 172460843354259478 endpoint_20_35_p16 endpoint_20_35_w16
private theorem endpoint_20_35_w18 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 18 1 172460843354259478 = some 172460843354259478 := by decide +kernel
private theorem endpoint_20_35_p19 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 19 172460843354259478 = some 172460843354259478 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 18 1 172460843354259478 172460843354259478 172460843354259478 endpoint_20_35_p18 endpoint_20_35_w18
def endpoint_20_35 : CertifiedEndpoint :=
  ⟨⟨20, 35, 2187⟩, 172460843354259478, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_35_flag endpoint_20_35_sources 19 172460843354259478 172460843354259478 rfl endpoint_20_35_base endpoint_20_35_p19) (by decide)⟩
private def endpoint_20_36_flag : Flag := ⟨20, 36, 2145⟩
private def endpoint_20_36_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_36_base : receiptBase endpoint_20_36_flag endpoint_20_36_sources = some 173364915784103199 := by decide +kernel
private theorem endpoint_20_36_w0 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 2 173364915784103199 = some 173364915784103199 := by decide +kernel
private theorem endpoint_20_36_w2 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 2 2 173364915784103199 = some 173364915784103199 := by decide +kernel
private theorem endpoint_20_36_p4 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 4 173364915784103199 = some 173364915784103199 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 2 2 173364915784103199 173364915784103199 173364915784103199 endpoint_20_36_w0 endpoint_20_36_w2
private theorem endpoint_20_36_w4 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 4 2 173364915784103199 = some 173364915784103199 := by decide +kernel
private theorem endpoint_20_36_p6 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 6 173364915784103199 = some 173364915784103199 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 4 2 173364915784103199 173364915784103199 173364915784103199 endpoint_20_36_p4 endpoint_20_36_w4
private theorem endpoint_20_36_w6 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 6 2 173364915784103199 = some 173364915784103199 := by decide +kernel
private theorem endpoint_20_36_p8 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 8 173364915784103199 = some 173364915784103199 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 6 2 173364915784103199 173364915784103199 173364915784103199 endpoint_20_36_p6 endpoint_20_36_w6
private theorem endpoint_20_36_w8 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 8 2 173364915784103199 = some 173364915784103199 := by decide +kernel
private theorem endpoint_20_36_p10 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 10 173364915784103199 = some 173364915784103199 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 8 2 173364915784103199 173364915784103199 173364915784103199 endpoint_20_36_p8 endpoint_20_36_w8
private theorem endpoint_20_36_w10 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 10 2 173364915784103199 = some 173364915784103199 := by decide +kernel
private theorem endpoint_20_36_p12 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 12 173364915784103199 = some 173364915784103199 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 10 2 173364915784103199 173364915784103199 173364915784103199 endpoint_20_36_p10 endpoint_20_36_w10
private theorem endpoint_20_36_w12 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 12 2 173364915784103199 = some 173364915784103199 := by decide +kernel
private theorem endpoint_20_36_p14 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 14 173364915784103199 = some 173364915784103199 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 12 2 173364915784103199 173364915784103199 173364915784103199 endpoint_20_36_p12 endpoint_20_36_w12
private theorem endpoint_20_36_w14 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 14 2 173364915784103199 = some 173364915784103199 := by decide +kernel
private theorem endpoint_20_36_p16 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 16 173364915784103199 = some 173364915784103199 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 14 2 173364915784103199 173364915784103199 173364915784103199 endpoint_20_36_p14 endpoint_20_36_w14
private theorem endpoint_20_36_w16 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 16 2 173364915784103199 = some 173364915784103199 := by decide +kernel
private theorem endpoint_20_36_p18 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 18 173364915784103199 = some 173364915784103199 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 16 2 173364915784103199 173364915784103199 173364915784103199 endpoint_20_36_p16 endpoint_20_36_w16
private theorem endpoint_20_36_w18 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 18 1 173364915784103199 = some 173364915784103199 := by decide +kernel
private theorem endpoint_20_36_p19 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 19 173364915784103199 = some 173364915784103199 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 18 1 173364915784103199 173364915784103199 173364915784103199 endpoint_20_36_p18 endpoint_20_36_w18
def endpoint_20_36 : CertifiedEndpoint :=
  ⟨⟨20, 36, 2145⟩, 173364915784103199, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_36_flag endpoint_20_36_sources 19 173364915784103199 173364915784103199 rfl endpoint_20_36_base endpoint_20_36_p19) (by decide)⟩
private def endpoint_20_37_flag : Flag := ⟨20, 37, 2102⟩
private def endpoint_20_37_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_37_base : receiptBase endpoint_20_37_flag endpoint_20_37_sources = some 174029978057129223 := by decide +kernel
private theorem endpoint_20_37_w0 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 2 174029978057129223 = some 174029978057129223 := by decide +kernel
private theorem endpoint_20_37_w2 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 2 2 174029978057129223 = some 174029978057129223 := by decide +kernel
private theorem endpoint_20_37_p4 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 4 174029978057129223 = some 174029978057129223 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 2 2 174029978057129223 174029978057129223 174029978057129223 endpoint_20_37_w0 endpoint_20_37_w2
private theorem endpoint_20_37_w4 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 4 2 174029978057129223 = some 174029978057129223 := by decide +kernel
private theorem endpoint_20_37_p6 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 6 174029978057129223 = some 174029978057129223 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 4 2 174029978057129223 174029978057129223 174029978057129223 endpoint_20_37_p4 endpoint_20_37_w4
private theorem endpoint_20_37_w6 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 6 2 174029978057129223 = some 174029978057129223 := by decide +kernel
private theorem endpoint_20_37_p8 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 8 174029978057129223 = some 174029978057129223 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 6 2 174029978057129223 174029978057129223 174029978057129223 endpoint_20_37_p6 endpoint_20_37_w6
private theorem endpoint_20_37_w8 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 8 2 174029978057129223 = some 174029978057129223 := by decide +kernel
private theorem endpoint_20_37_p10 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 10 174029978057129223 = some 174029978057129223 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 8 2 174029978057129223 174029978057129223 174029978057129223 endpoint_20_37_p8 endpoint_20_37_w8
private theorem endpoint_20_37_w10 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 10 2 174029978057129223 = some 174029978057129223 := by decide +kernel
private theorem endpoint_20_37_p12 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 12 174029978057129223 = some 174029978057129223 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 10 2 174029978057129223 174029978057129223 174029978057129223 endpoint_20_37_p10 endpoint_20_37_w10
private theorem endpoint_20_37_w12 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 12 2 174029978057129223 = some 174029978057129223 := by decide +kernel
private theorem endpoint_20_37_p14 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 14 174029978057129223 = some 174029978057129223 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 12 2 174029978057129223 174029978057129223 174029978057129223 endpoint_20_37_p12 endpoint_20_37_w12
private theorem endpoint_20_37_w14 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 14 2 174029978057129223 = some 174029978057129223 := by decide +kernel
private theorem endpoint_20_37_p16 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 16 174029978057129223 = some 174029978057129223 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 14 2 174029978057129223 174029978057129223 174029978057129223 endpoint_20_37_p14 endpoint_20_37_w14
private theorem endpoint_20_37_w16 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 16 2 174029978057129223 = some 174029978057129223 := by decide +kernel
private theorem endpoint_20_37_p18 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 18 174029978057129223 = some 174029978057129223 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 16 2 174029978057129223 174029978057129223 174029978057129223 endpoint_20_37_p16 endpoint_20_37_w16
private theorem endpoint_20_37_w18 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 18 1 174029978057129223 = some 174029978057129223 := by decide +kernel
private theorem endpoint_20_37_p19 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 19 174029978057129223 = some 174029978057129223 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 18 1 174029978057129223 174029978057129223 174029978057129223 endpoint_20_37_p18 endpoint_20_37_w18
def endpoint_20_37 : CertifiedEndpoint :=
  ⟨⟨20, 37, 2102⟩, 174029978057129223, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_37_flag endpoint_20_37_sources 19 174029978057129223 174029978057129223 rfl endpoint_20_37_base endpoint_20_37_p19) (by decide)⟩
private def endpoint_20_38_flag : Flag := ⟨20, 38, 2058⟩
private def endpoint_20_38_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_38_base : receiptBase endpoint_20_38_flag endpoint_20_38_sources = some 174450444206451277 := by decide +kernel
private theorem endpoint_20_38_w0 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 2 174450444206451277 = some 174450444206451277 := by decide +kernel
private theorem endpoint_20_38_w2 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 2 2 174450444206451277 = some 174450444206451277 := by decide +kernel
private theorem endpoint_20_38_p4 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 4 174450444206451277 = some 174450444206451277 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 2 2 174450444206451277 174450444206451277 174450444206451277 endpoint_20_38_w0 endpoint_20_38_w2
private theorem endpoint_20_38_w4 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 4 2 174450444206451277 = some 174450444206451277 := by decide +kernel
private theorem endpoint_20_38_p6 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 6 174450444206451277 = some 174450444206451277 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 4 2 174450444206451277 174450444206451277 174450444206451277 endpoint_20_38_p4 endpoint_20_38_w4
private theorem endpoint_20_38_w6 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 6 2 174450444206451277 = some 174450444206451277 := by decide +kernel
private theorem endpoint_20_38_p8 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 8 174450444206451277 = some 174450444206451277 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 6 2 174450444206451277 174450444206451277 174450444206451277 endpoint_20_38_p6 endpoint_20_38_w6
private theorem endpoint_20_38_w8 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 8 2 174450444206451277 = some 174450444206451277 := by decide +kernel
private theorem endpoint_20_38_p10 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 10 174450444206451277 = some 174450444206451277 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 8 2 174450444206451277 174450444206451277 174450444206451277 endpoint_20_38_p8 endpoint_20_38_w8
private theorem endpoint_20_38_w10 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 10 2 174450444206451277 = some 174450444206451277 := by decide +kernel
private theorem endpoint_20_38_p12 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 12 174450444206451277 = some 174450444206451277 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 10 2 174450444206451277 174450444206451277 174450444206451277 endpoint_20_38_p10 endpoint_20_38_w10
private theorem endpoint_20_38_w12 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 12 2 174450444206451277 = some 174450444206451277 := by decide +kernel
private theorem endpoint_20_38_p14 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 14 174450444206451277 = some 174450444206451277 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 12 2 174450444206451277 174450444206451277 174450444206451277 endpoint_20_38_p12 endpoint_20_38_w12
private theorem endpoint_20_38_w14 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 14 2 174450444206451277 = some 174450444206451277 := by decide +kernel
private theorem endpoint_20_38_p16 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 16 174450444206451277 = some 174450444206451277 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 14 2 174450444206451277 174450444206451277 174450444206451277 endpoint_20_38_p14 endpoint_20_38_w14
private theorem endpoint_20_38_w16 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 16 2 174450444206451277 = some 174450444206451277 := by decide +kernel
private theorem endpoint_20_38_p18 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 18 174450444206451277 = some 174450444206451277 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 16 2 174450444206451277 174450444206451277 174450444206451277 endpoint_20_38_p16 endpoint_20_38_w16
private theorem endpoint_20_38_w18 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 18 1 174450444206451277 = some 174450444206451277 := by decide +kernel
private theorem endpoint_20_38_p19 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 19 174450444206451277 = some 174450444206451277 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 18 1 174450444206451277 174450444206451277 174450444206451277 endpoint_20_38_p18 endpoint_20_38_w18
def endpoint_20_38 : CertifiedEndpoint :=
  ⟨⟨20, 38, 2058⟩, 174450444206451277, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_38_flag endpoint_20_38_sources 19 174450444206451277 174450444206451277 rfl endpoint_20_38_base endpoint_20_38_p19) (by decide)⟩
private def endpoint_20_39_flag : Flag := ⟨20, 39, 2014⟩
private def endpoint_20_39_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_39_base : receiptBase endpoint_20_39_flag endpoint_20_39_sources = some 174705201212455944 := by decide +kernel
private theorem endpoint_20_39_w0 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 2 174705201212455944 = some 174705201212455944 := by decide +kernel
private theorem endpoint_20_39_w2 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 2 2 174705201212455944 = some 174705201212455944 := by decide +kernel
private theorem endpoint_20_39_p4 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 4 174705201212455944 = some 174705201212455944 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 2 2 174705201212455944 174705201212455944 174705201212455944 endpoint_20_39_w0 endpoint_20_39_w2
private theorem endpoint_20_39_w4 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 4 2 174705201212455944 = some 174705201212455944 := by decide +kernel
private theorem endpoint_20_39_p6 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 6 174705201212455944 = some 174705201212455944 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 4 2 174705201212455944 174705201212455944 174705201212455944 endpoint_20_39_p4 endpoint_20_39_w4
private theorem endpoint_20_39_w6 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 6 2 174705201212455944 = some 174705201212455944 := by decide +kernel
private theorem endpoint_20_39_p8 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 8 174705201212455944 = some 174705201212455944 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 6 2 174705201212455944 174705201212455944 174705201212455944 endpoint_20_39_p6 endpoint_20_39_w6
private theorem endpoint_20_39_w8 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 8 2 174705201212455944 = some 174705201212455944 := by decide +kernel
private theorem endpoint_20_39_p10 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 10 174705201212455944 = some 174705201212455944 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 8 2 174705201212455944 174705201212455944 174705201212455944 endpoint_20_39_p8 endpoint_20_39_w8
private theorem endpoint_20_39_w10 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 10 2 174705201212455944 = some 174705201212455944 := by decide +kernel
private theorem endpoint_20_39_p12 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 12 174705201212455944 = some 174705201212455944 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 10 2 174705201212455944 174705201212455944 174705201212455944 endpoint_20_39_p10 endpoint_20_39_w10
private theorem endpoint_20_39_w12 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 12 2 174705201212455944 = some 174705201212455944 := by decide +kernel
private theorem endpoint_20_39_p14 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 14 174705201212455944 = some 174705201212455944 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 12 2 174705201212455944 174705201212455944 174705201212455944 endpoint_20_39_p12 endpoint_20_39_w12
private theorem endpoint_20_39_w14 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 14 2 174705201212455944 = some 174705201212455944 := by decide +kernel
private theorem endpoint_20_39_p16 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 16 174705201212455944 = some 174705201212455944 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 14 2 174705201212455944 174705201212455944 174705201212455944 endpoint_20_39_p14 endpoint_20_39_w14
private theorem endpoint_20_39_w16 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 16 2 174705201212455944 = some 174705201212455944 := by decide +kernel
private theorem endpoint_20_39_p18 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 18 174705201212455944 = some 174705201212455944 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 16 2 174705201212455944 174705201212455944 174705201212455944 endpoint_20_39_p16 endpoint_20_39_w16
private theorem endpoint_20_39_w18 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 18 1 174705201212455944 = some 174705201212455944 := by decide +kernel
private theorem endpoint_20_39_p19 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 19 174705201212455944 = some 174705201212455944 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 18 1 174705201212455944 174705201212455944 174705201212455944 endpoint_20_39_p18 endpoint_20_39_w18
def endpoint_20_39 : CertifiedEndpoint :=
  ⟨⟨20, 39, 2014⟩, 174705201212455944, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_39_flag endpoint_20_39_sources 19 174705201212455944 174705201212455944 rfl endpoint_20_39_base endpoint_20_39_p19) (by decide)⟩
private def endpoint_20_40_flag : Flag := ⟨20, 40, 1969⟩
private def endpoint_20_40_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_40_base : receiptBase endpoint_20_40_flag endpoint_20_40_sources = some 174707914138908274 := by decide +kernel
private theorem endpoint_20_40_w0 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 2 174707914138908274 = some 174707914138908274 := by decide +kernel
private theorem endpoint_20_40_w2 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 2 2 174707914138908274 = some 174707914138908274 := by decide +kernel
private theorem endpoint_20_40_p4 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 4 174707914138908274 = some 174707914138908274 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 2 2 174707914138908274 174707914138908274 174707914138908274 endpoint_20_40_w0 endpoint_20_40_w2
private theorem endpoint_20_40_w4 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 4 2 174707914138908274 = some 174707914138908274 := by decide +kernel
private theorem endpoint_20_40_p6 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 6 174707914138908274 = some 174707914138908274 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 4 2 174707914138908274 174707914138908274 174707914138908274 endpoint_20_40_p4 endpoint_20_40_w4
private theorem endpoint_20_40_w6 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 6 2 174707914138908274 = some 174707914138908274 := by decide +kernel
private theorem endpoint_20_40_p8 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 8 174707914138908274 = some 174707914138908274 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 6 2 174707914138908274 174707914138908274 174707914138908274 endpoint_20_40_p6 endpoint_20_40_w6
private theorem endpoint_20_40_w8 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 8 2 174707914138908274 = some 174707914138908274 := by decide +kernel
private theorem endpoint_20_40_p10 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 10 174707914138908274 = some 174707914138908274 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 8 2 174707914138908274 174707914138908274 174707914138908274 endpoint_20_40_p8 endpoint_20_40_w8
private theorem endpoint_20_40_w10 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 10 2 174707914138908274 = some 174707914138908274 := by decide +kernel
private theorem endpoint_20_40_p12 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 12 174707914138908274 = some 174707914138908274 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 10 2 174707914138908274 174707914138908274 174707914138908274 endpoint_20_40_p10 endpoint_20_40_w10
private theorem endpoint_20_40_w12 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 12 2 174707914138908274 = some 174707914138908274 := by decide +kernel
private theorem endpoint_20_40_p14 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 14 174707914138908274 = some 174707914138908274 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 12 2 174707914138908274 174707914138908274 174707914138908274 endpoint_20_40_p12 endpoint_20_40_w12
private theorem endpoint_20_40_w14 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 14 2 174707914138908274 = some 174707914138908274 := by decide +kernel
private theorem endpoint_20_40_p16 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 16 174707914138908274 = some 174707914138908274 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 14 2 174707914138908274 174707914138908274 174707914138908274 endpoint_20_40_p14 endpoint_20_40_w14
private theorem endpoint_20_40_w16 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 16 2 174707914138908274 = some 174707914138908274 := by decide +kernel
private theorem endpoint_20_40_p18 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 18 174707914138908274 = some 174707914138908274 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 16 2 174707914138908274 174707914138908274 174707914138908274 endpoint_20_40_p16 endpoint_20_40_w16
private theorem endpoint_20_40_w18 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 18 1 174707914138908274 = some 174707914138908274 := by decide +kernel
private theorem endpoint_20_40_p19 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 19 174707914138908274 = some 174707914138908274 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 18 1 174707914138908274 174707914138908274 174707914138908274 endpoint_20_40_p18 endpoint_20_40_w18
def endpoint_20_40 : CertifiedEndpoint :=
  ⟨⟨20, 40, 1969⟩, 174707914138908274, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_40_flag endpoint_20_40_sources 19 174707914138908274 174707914138908274 rfl endpoint_20_40_base endpoint_20_40_p19) (by decide)⟩
private def endpoint_20_41_flag : Flag := ⟨20, 41, 1923⟩
private def endpoint_20_41_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_41_base : receiptBase endpoint_20_41_flag endpoint_20_41_sources = some 174452997018921990 := by decide +kernel
private theorem endpoint_20_41_w0 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 2 174452997018921990 = some 174452997018921990 := by decide +kernel
private theorem endpoint_20_41_w2 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 2 2 174452997018921990 = some 174452997018921990 := by decide +kernel
private theorem endpoint_20_41_p4 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 4 174452997018921990 = some 174452997018921990 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 2 2 174452997018921990 174452997018921990 174452997018921990 endpoint_20_41_w0 endpoint_20_41_w2
private theorem endpoint_20_41_w4 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 4 2 174452997018921990 = some 174452997018921990 := by decide +kernel
private theorem endpoint_20_41_p6 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 6 174452997018921990 = some 174452997018921990 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 4 2 174452997018921990 174452997018921990 174452997018921990 endpoint_20_41_p4 endpoint_20_41_w4
private theorem endpoint_20_41_w6 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 6 2 174452997018921990 = some 174452997018921990 := by decide +kernel
private theorem endpoint_20_41_p8 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 8 174452997018921990 = some 174452997018921990 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 6 2 174452997018921990 174452997018921990 174452997018921990 endpoint_20_41_p6 endpoint_20_41_w6
private theorem endpoint_20_41_w8 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 8 2 174452997018921990 = some 174452997018921990 := by decide +kernel
private theorem endpoint_20_41_p10 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 10 174452997018921990 = some 174452997018921990 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 8 2 174452997018921990 174452997018921990 174452997018921990 endpoint_20_41_p8 endpoint_20_41_w8
private theorem endpoint_20_41_w10 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 10 2 174452997018921990 = some 174452997018921990 := by decide +kernel
private theorem endpoint_20_41_p12 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 12 174452997018921990 = some 174452997018921990 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 10 2 174452997018921990 174452997018921990 174452997018921990 endpoint_20_41_p10 endpoint_20_41_w10
private theorem endpoint_20_41_w12 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 12 2 174452997018921990 = some 174452997018921990 := by decide +kernel
private theorem endpoint_20_41_p14 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 14 174452997018921990 = some 174452997018921990 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 12 2 174452997018921990 174452997018921990 174452997018921990 endpoint_20_41_p12 endpoint_20_41_w12
private theorem endpoint_20_41_w14 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 14 2 174452997018921990 = some 174452997018921990 := by decide +kernel
private theorem endpoint_20_41_p16 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 16 174452997018921990 = some 174452997018921990 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 14 2 174452997018921990 174452997018921990 174452997018921990 endpoint_20_41_p14 endpoint_20_41_w14
private theorem endpoint_20_41_w16 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 16 2 174452997018921990 = some 174452997018921990 := by decide +kernel
private theorem endpoint_20_41_p18 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 18 174452997018921990 = some 174452997018921990 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 16 2 174452997018921990 174452997018921990 174452997018921990 endpoint_20_41_p16 endpoint_20_41_w16
private theorem endpoint_20_41_w18 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 18 1 174452997018921990 = some 174452997018921990 := by decide +kernel
private theorem endpoint_20_41_p19 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 19 174452997018921990 = some 174452997018921990 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 18 1 174452997018921990 174452997018921990 174452997018921990 endpoint_20_41_p18 endpoint_20_41_w18
def endpoint_20_41 : CertifiedEndpoint :=
  ⟨⟨20, 41, 1923⟩, 174452997018921990, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_41_flag endpoint_20_41_sources 19 174452997018921990 174452997018921990 rfl endpoint_20_41_base endpoint_20_41_p19) (by decide)⟩
private def endpoint_20_42_flag : Flag := ⟨20, 42, 1877⟩
private def endpoint_20_42_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_42_base : receiptBase endpoint_20_42_flag endpoint_20_42_sources = some 174024922799769953 := by decide +kernel
private theorem endpoint_20_42_w0 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 2 174024922799769953 = some 174024922799769953 := by decide +kernel
private theorem endpoint_20_42_w2 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 2 2 174024922799769953 = some 174024922799769953 := by decide +kernel
private theorem endpoint_20_42_p4 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 4 174024922799769953 = some 174024922799769953 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 2 2 174024922799769953 174024922799769953 174024922799769953 endpoint_20_42_w0 endpoint_20_42_w2
private theorem endpoint_20_42_w4 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 4 2 174024922799769953 = some 174024922799769953 := by decide +kernel
private theorem endpoint_20_42_p6 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 6 174024922799769953 = some 174024922799769953 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 4 2 174024922799769953 174024922799769953 174024922799769953 endpoint_20_42_p4 endpoint_20_42_w4
private theorem endpoint_20_42_w6 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 6 2 174024922799769953 = some 174024922799769953 := by decide +kernel
private theorem endpoint_20_42_p8 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 8 174024922799769953 = some 174024922799769953 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 6 2 174024922799769953 174024922799769953 174024922799769953 endpoint_20_42_p6 endpoint_20_42_w6
private theorem endpoint_20_42_w8 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 8 2 174024922799769953 = some 174024922799769953 := by decide +kernel
private theorem endpoint_20_42_p10 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 10 174024922799769953 = some 174024922799769953 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 8 2 174024922799769953 174024922799769953 174024922799769953 endpoint_20_42_p8 endpoint_20_42_w8
private theorem endpoint_20_42_w10 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 10 2 174024922799769953 = some 174024922799769953 := by decide +kernel
private theorem endpoint_20_42_p12 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 12 174024922799769953 = some 174024922799769953 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 10 2 174024922799769953 174024922799769953 174024922799769953 endpoint_20_42_p10 endpoint_20_42_w10
private theorem endpoint_20_42_w12 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 12 2 174024922799769953 = some 174024922799769953 := by decide +kernel
private theorem endpoint_20_42_p14 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 14 174024922799769953 = some 174024922799769953 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 12 2 174024922799769953 174024922799769953 174024922799769953 endpoint_20_42_p12 endpoint_20_42_w12
private theorem endpoint_20_42_w14 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 14 2 174024922799769953 = some 174024922799769953 := by decide +kernel
private theorem endpoint_20_42_p16 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 16 174024922799769953 = some 174024922799769953 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 14 2 174024922799769953 174024922799769953 174024922799769953 endpoint_20_42_p14 endpoint_20_42_w14
private theorem endpoint_20_42_w16 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 16 2 174024922799769953 = some 174024922799769953 := by decide +kernel
private theorem endpoint_20_42_p18 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 18 174024922799769953 = some 174024922799769953 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 16 2 174024922799769953 174024922799769953 174024922799769953 endpoint_20_42_p16 endpoint_20_42_w16
private theorem endpoint_20_42_w18 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 18 1 174024922799769953 = some 174024922799769953 := by decide +kernel
private theorem endpoint_20_42_p19 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 19 174024922799769953 = some 174024922799769953 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 18 1 174024922799769953 174024922799769953 174024922799769953 endpoint_20_42_p18 endpoint_20_42_w18
def endpoint_20_42 : CertifiedEndpoint :=
  ⟨⟨20, 42, 1877⟩, 174024922799769953, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_42_flag endpoint_20_42_sources 19 174024922799769953 174024922799769953 rfl endpoint_20_42_base endpoint_20_42_p19) (by decide)⟩
private def endpoint_20_43_flag : Flag := ⟨20, 43, 1830⟩
private def endpoint_20_43_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_20_43_base : receiptBase endpoint_20_43_flag endpoint_20_43_sources = some 175071176104335663 := by decide +kernel
private theorem endpoint_20_43_w0 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 2 175071176104335663 = some 175071176104335663 := by decide +kernel
private theorem endpoint_20_43_w2 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 2 2 175071176104335663 = some 175071176104335663 := by decide +kernel
private theorem endpoint_20_43_p4 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 4 175071176104335663 = some 175071176104335663 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 2 2 175071176104335663 175071176104335663 175071176104335663 endpoint_20_43_w0 endpoint_20_43_w2
private theorem endpoint_20_43_w4 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 4 2 175071176104335663 = some 175071176104335663 := by decide +kernel
private theorem endpoint_20_43_p6 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 6 175071176104335663 = some 175071176104335663 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 4 2 175071176104335663 175071176104335663 175071176104335663 endpoint_20_43_p4 endpoint_20_43_w4
private theorem endpoint_20_43_w6 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 6 2 175071176104335663 = some 175071176104335663 := by decide +kernel
private theorem endpoint_20_43_p8 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 8 175071176104335663 = some 175071176104335663 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 6 2 175071176104335663 175071176104335663 175071176104335663 endpoint_20_43_p6 endpoint_20_43_w6
private theorem endpoint_20_43_w8 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 8 2 175071176104335663 = some 175071176104335663 := by decide +kernel
private theorem endpoint_20_43_p10 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 10 175071176104335663 = some 175071176104335663 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 8 2 175071176104335663 175071176104335663 175071176104335663 endpoint_20_43_p8 endpoint_20_43_w8
private theorem endpoint_20_43_w10 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 10 2 175071176104335663 = some 175071176104335663 := by decide +kernel
private theorem endpoint_20_43_p12 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 12 175071176104335663 = some 175071176104335663 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 10 2 175071176104335663 175071176104335663 175071176104335663 endpoint_20_43_p10 endpoint_20_43_w10
private theorem endpoint_20_43_w12 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 12 2 175071176104335663 = some 175071176104335663 := by decide +kernel
private theorem endpoint_20_43_p14 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 14 175071176104335663 = some 175071176104335663 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 12 2 175071176104335663 175071176104335663 175071176104335663 endpoint_20_43_p12 endpoint_20_43_w12
private theorem endpoint_20_43_w14 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 14 2 175071176104335663 = some 175071176104335663 := by decide +kernel
private theorem endpoint_20_43_p16 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 16 175071176104335663 = some 175071176104335663 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 14 2 175071176104335663 175071176104335663 175071176104335663 endpoint_20_43_p14 endpoint_20_43_w14
private theorem endpoint_20_43_w16 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 16 2 175071176104335663 = some 175071176104335663 := by decide +kernel
private theorem endpoint_20_43_p18 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 18 175071176104335663 = some 175071176104335663 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 16 2 175071176104335663 175071176104335663 175071176104335663 endpoint_20_43_p16 endpoint_20_43_w16
private theorem endpoint_20_43_w18 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 18 1 175071176104335663 = some 175071176104335663 := by decide +kernel
private theorem endpoint_20_43_p19 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 19 175071176104335663 = some 175071176104335663 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 18 1 175071176104335663 175071176104335663 175071176104335663 endpoint_20_43_p18 endpoint_20_43_w18
def endpoint_20_43 : CertifiedEndpoint :=
  ⟨⟨20, 43, 1830⟩, 175071176104335663, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_20_43_flag endpoint_20_43_sources 19 175071176104335663 175071176104335663 rfl endpoint_20_43_base endpoint_20_43_p19) (by decide)⟩
private def endpoint_20_44_flag : Flag := ⟨20, 44, 1782⟩
private def endpoint_20_44_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_20_44_base : receiptBase endpoint_20_44_flag endpoint_20_44_sources = some 174044324329708881 := by decide +kernel
private theorem endpoint_20_44_w0 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 2 174044324329708881 = some 174044324329708881 := by decide +kernel
private theorem endpoint_20_44_w2 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 2 2 174044324329708881 = some 174044324329708881 := by decide +kernel
private theorem endpoint_20_44_p4 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 4 174044324329708881 = some 174044324329708881 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 2 2 174044324329708881 174044324329708881 174044324329708881 endpoint_20_44_w0 endpoint_20_44_w2
private theorem endpoint_20_44_w4 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 4 2 174044324329708881 = some 174044324329708881 := by decide +kernel
private theorem endpoint_20_44_p6 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 6 174044324329708881 = some 174044324329708881 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 4 2 174044324329708881 174044324329708881 174044324329708881 endpoint_20_44_p4 endpoint_20_44_w4
private theorem endpoint_20_44_w6 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 6 2 174044324329708881 = some 174044324329708881 := by decide +kernel
private theorem endpoint_20_44_p8 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 8 174044324329708881 = some 174044324329708881 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 6 2 174044324329708881 174044324329708881 174044324329708881 endpoint_20_44_p6 endpoint_20_44_w6
private theorem endpoint_20_44_w8 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 8 2 174044324329708881 = some 174044324329708881 := by decide +kernel
private theorem endpoint_20_44_p10 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 10 174044324329708881 = some 174044324329708881 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 8 2 174044324329708881 174044324329708881 174044324329708881 endpoint_20_44_p8 endpoint_20_44_w8
private theorem endpoint_20_44_w10 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 10 2 174044324329708881 = some 174044324329708881 := by decide +kernel
private theorem endpoint_20_44_p12 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 12 174044324329708881 = some 174044324329708881 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 10 2 174044324329708881 174044324329708881 174044324329708881 endpoint_20_44_p10 endpoint_20_44_w10
private theorem endpoint_20_44_w12 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 12 2 174044324329708881 = some 174044324329708881 := by decide +kernel
private theorem endpoint_20_44_p14 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 14 174044324329708881 = some 174044324329708881 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 12 2 174044324329708881 174044324329708881 174044324329708881 endpoint_20_44_p12 endpoint_20_44_w12
private theorem endpoint_20_44_w14 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 14 2 174044324329708881 = some 174044324329708881 := by decide +kernel
private theorem endpoint_20_44_p16 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 16 174044324329708881 = some 174044324329708881 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 14 2 174044324329708881 174044324329708881 174044324329708881 endpoint_20_44_p14 endpoint_20_44_w14
private theorem endpoint_20_44_w16 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 16 2 174044324329708881 = some 174044324329708881 := by decide +kernel
private theorem endpoint_20_44_p18 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 18 174044324329708881 = some 174044324329708881 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 16 2 174044324329708881 174044324329708881 174044324329708881 endpoint_20_44_p16 endpoint_20_44_w16
private theorem endpoint_20_44_w18 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 18 1 174044324329708881 = some 174044324329708881 := by decide +kernel
private theorem endpoint_20_44_p19 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 19 174044324329708881 = some 174044324329708881 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 18 1 174044324329708881 174044324329708881 174044324329708881 endpoint_20_44_p18 endpoint_20_44_w18
def endpoint_20_44 : CertifiedEndpoint :=
  ⟨⟨20, 44, 1782⟩, 174044324329708881, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_20_44_flag endpoint_20_44_sources 19 174044324329708881 174044324329708881 rfl endpoint_20_44_base endpoint_20_44_p19) (by decide)⟩
private def endpoint_20_45_flag : Flag := ⟨20, 45, 1733⟩
private def endpoint_20_45_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_20_45_base : receiptBase endpoint_20_45_flag endpoint_20_45_sources = some 172736463046505600 := by decide +kernel
private theorem endpoint_20_45_w0 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 2 172736463046505600 = some 172736463046505600 := by decide +kernel
private theorem endpoint_20_45_w2 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 2 2 172736463046505600 = some 172736463046505600 := by decide +kernel
private theorem endpoint_20_45_p4 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 4 172736463046505600 = some 172736463046505600 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 2 2 172736463046505600 172736463046505600 172736463046505600 endpoint_20_45_w0 endpoint_20_45_w2
private theorem endpoint_20_45_w4 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 4 2 172736463046505600 = some 172736463046505600 := by decide +kernel
private theorem endpoint_20_45_p6 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 6 172736463046505600 = some 172736463046505600 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 4 2 172736463046505600 172736463046505600 172736463046505600 endpoint_20_45_p4 endpoint_20_45_w4
private theorem endpoint_20_45_w6 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 6 2 172736463046505600 = some 172736463046505600 := by decide +kernel
private theorem endpoint_20_45_p8 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 8 172736463046505600 = some 172736463046505600 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 6 2 172736463046505600 172736463046505600 172736463046505600 endpoint_20_45_p6 endpoint_20_45_w6
private theorem endpoint_20_45_w8 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 8 2 172736463046505600 = some 172736463046505600 := by decide +kernel
private theorem endpoint_20_45_p10 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 10 172736463046505600 = some 172736463046505600 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 8 2 172736463046505600 172736463046505600 172736463046505600 endpoint_20_45_p8 endpoint_20_45_w8
private theorem endpoint_20_45_w10 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 10 2 172736463046505600 = some 172736463046505600 := by decide +kernel
private theorem endpoint_20_45_p12 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 12 172736463046505600 = some 172736463046505600 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 10 2 172736463046505600 172736463046505600 172736463046505600 endpoint_20_45_p10 endpoint_20_45_w10
private theorem endpoint_20_45_w12 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 12 2 172736463046505600 = some 172736463046505600 := by decide +kernel
private theorem endpoint_20_45_p14 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 14 172736463046505600 = some 172736463046505600 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 12 2 172736463046505600 172736463046505600 172736463046505600 endpoint_20_45_p12 endpoint_20_45_w12
private theorem endpoint_20_45_w14 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 14 2 172736463046505600 = some 172736463046505600 := by decide +kernel
private theorem endpoint_20_45_p16 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 16 172736463046505600 = some 172736463046505600 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 14 2 172736463046505600 172736463046505600 172736463046505600 endpoint_20_45_p14 endpoint_20_45_w14
private theorem endpoint_20_45_w16 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 16 2 172736463046505600 = some 172736463046505600 := by decide +kernel
private theorem endpoint_20_45_p18 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 18 172736463046505600 = some 172736463046505600 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 16 2 172736463046505600 172736463046505600 172736463046505600 endpoint_20_45_p16 endpoint_20_45_w16
private theorem endpoint_20_45_w18 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 18 1 172736463046505600 = some 172736463046505600 := by decide +kernel
private theorem endpoint_20_45_p19 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 19 172736463046505600 = some 172736463046505600 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 18 1 172736463046505600 172736463046505600 172736463046505600 endpoint_20_45_p18 endpoint_20_45_w18
def endpoint_20_45 : CertifiedEndpoint :=
  ⟨⟨20, 45, 1733⟩, 172736463046505600, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_20_45_flag endpoint_20_45_sources 19 172736463046505600 172736463046505600 rfl endpoint_20_45_base endpoint_20_45_p19) (by decide)⟩
private def endpoint_20_46_flag : Flag := ⟨20, 46, 1684⟩
private def endpoint_20_46_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_20_46_base : receiptBase endpoint_20_46_flag endpoint_20_46_sources = some 171241154128136113 := by decide +kernel
private theorem endpoint_20_46_w0 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 2 171241154128136113 = some 171300087948401260 := by decide +kernel
private theorem endpoint_20_46_w2 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 2 2 171300087948401260 = some 171300087948401260 := by decide +kernel
private theorem endpoint_20_46_p4 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 4 171241154128136113 = some 171300087948401260 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 2 2 171241154128136113 171300087948401260 171300087948401260 endpoint_20_46_w0 endpoint_20_46_w2
private theorem endpoint_20_46_w4 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 4 2 171300087948401260 = some 171300087948401260 := by decide +kernel
private theorem endpoint_20_46_p6 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 6 171241154128136113 = some 171300087948401260 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 4 2 171241154128136113 171300087948401260 171300087948401260 endpoint_20_46_p4 endpoint_20_46_w4
private theorem endpoint_20_46_w6 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 6 2 171300087948401260 = some 171300087948401260 := by decide +kernel
private theorem endpoint_20_46_p8 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 8 171241154128136113 = some 171300087948401260 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 6 2 171241154128136113 171300087948401260 171300087948401260 endpoint_20_46_p6 endpoint_20_46_w6
private theorem endpoint_20_46_w8 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 8 2 171300087948401260 = some 171300087948401260 := by decide +kernel
private theorem endpoint_20_46_p10 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 10 171241154128136113 = some 171300087948401260 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 8 2 171241154128136113 171300087948401260 171300087948401260 endpoint_20_46_p8 endpoint_20_46_w8
private theorem endpoint_20_46_w10 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 10 2 171300087948401260 = some 171300087948401260 := by decide +kernel
private theorem endpoint_20_46_p12 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 12 171241154128136113 = some 171300087948401260 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 10 2 171241154128136113 171300087948401260 171300087948401260 endpoint_20_46_p10 endpoint_20_46_w10
private theorem endpoint_20_46_w12 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 12 2 171300087948401260 = some 171300087948401260 := by decide +kernel
private theorem endpoint_20_46_p14 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 14 171241154128136113 = some 171300087948401260 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 12 2 171241154128136113 171300087948401260 171300087948401260 endpoint_20_46_p12 endpoint_20_46_w12
private theorem endpoint_20_46_w14 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 14 2 171300087948401260 = some 171300087948401260 := by decide +kernel
private theorem endpoint_20_46_p16 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 16 171241154128136113 = some 171300087948401260 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 14 2 171241154128136113 171300087948401260 171300087948401260 endpoint_20_46_p14 endpoint_20_46_w14
private theorem endpoint_20_46_w16 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 16 2 171300087948401260 = some 171300087948401260 := by decide +kernel
private theorem endpoint_20_46_p18 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 18 171241154128136113 = some 171300087948401260 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 16 2 171241154128136113 171300087948401260 171300087948401260 endpoint_20_46_p16 endpoint_20_46_w16
private theorem endpoint_20_46_w18 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 18 1 171300087948401260 = some 171300087948401260 := by decide +kernel
private theorem endpoint_20_46_p19 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 19 171241154128136113 = some 171300087948401260 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 18 1 171241154128136113 171300087948401260 171300087948401260 endpoint_20_46_p18 endpoint_20_46_w18
def endpoint_20_46 : CertifiedEndpoint :=
  ⟨⟨20, 46, 1684⟩, 171300087948401260, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_20_46_flag endpoint_20_46_sources 19 171241154128136113 171300087948401260 rfl endpoint_20_46_base endpoint_20_46_p19) (by decide)⟩
private def endpoint_20_47_flag : Flag := ⟨20, 47, 1634⟩
private def endpoint_20_47_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_20_47_base : receiptBase endpoint_20_47_flag endpoint_20_47_sources = some 171350196507576960 := by decide +kernel
private theorem endpoint_20_47_w0 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 2 171350196507576960 = some 171350196507576960 := by decide +kernel
private theorem endpoint_20_47_w2 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 2 2 171350196507576960 = some 171350196507576960 := by decide +kernel
private theorem endpoint_20_47_p4 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 4 171350196507576960 = some 171350196507576960 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 2 2 171350196507576960 171350196507576960 171350196507576960 endpoint_20_47_w0 endpoint_20_47_w2
private theorem endpoint_20_47_w4 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 4 2 171350196507576960 = some 171350196507576960 := by decide +kernel
private theorem endpoint_20_47_p6 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 6 171350196507576960 = some 171350196507576960 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 4 2 171350196507576960 171350196507576960 171350196507576960 endpoint_20_47_p4 endpoint_20_47_w4
private theorem endpoint_20_47_w6 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 6 2 171350196507576960 = some 171350196507576960 := by decide +kernel
private theorem endpoint_20_47_p8 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 8 171350196507576960 = some 171350196507576960 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 6 2 171350196507576960 171350196507576960 171350196507576960 endpoint_20_47_p6 endpoint_20_47_w6
private theorem endpoint_20_47_w8 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 8 2 171350196507576960 = some 171350196507576960 := by decide +kernel
private theorem endpoint_20_47_p10 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 10 171350196507576960 = some 171350196507576960 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 8 2 171350196507576960 171350196507576960 171350196507576960 endpoint_20_47_p8 endpoint_20_47_w8
private theorem endpoint_20_47_w10 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 10 2 171350196507576960 = some 171350196507576960 := by decide +kernel
private theorem endpoint_20_47_p12 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 12 171350196507576960 = some 171350196507576960 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 10 2 171350196507576960 171350196507576960 171350196507576960 endpoint_20_47_p10 endpoint_20_47_w10
private theorem endpoint_20_47_w12 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 12 2 171350196507576960 = some 171350196507576960 := by decide +kernel
private theorem endpoint_20_47_p14 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 14 171350196507576960 = some 171350196507576960 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 12 2 171350196507576960 171350196507576960 171350196507576960 endpoint_20_47_p12 endpoint_20_47_w12
private theorem endpoint_20_47_w14 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 14 2 171350196507576960 = some 171350196507576960 := by decide +kernel
private theorem endpoint_20_47_p16 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 16 171350196507576960 = some 171350196507576960 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 14 2 171350196507576960 171350196507576960 171350196507576960 endpoint_20_47_p14 endpoint_20_47_w14
private theorem endpoint_20_47_w16 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 16 2 171350196507576960 = some 171350196507576960 := by decide +kernel
private theorem endpoint_20_47_p18 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 18 171350196507576960 = some 171350196507576960 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 16 2 171350196507576960 171350196507576960 171350196507576960 endpoint_20_47_p16 endpoint_20_47_w16
private theorem endpoint_20_47_w18 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 18 1 171350196507576960 = some 171350196507576960 := by decide +kernel
private theorem endpoint_20_47_p19 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 19 171350196507576960 = some 171350196507576960 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 18 1 171350196507576960 171350196507576960 171350196507576960 endpoint_20_47_p18 endpoint_20_47_w18
def endpoint_20_47 : CertifiedEndpoint :=
  ⟨⟨20, 47, 1634⟩, 171350196507576960, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_20_47_flag endpoint_20_47_sources 19 171350196507576960 171350196507576960 rfl endpoint_20_47_base endpoint_20_47_p19) (by decide)⟩
private def endpoint_20_48_flag : Flag := ⟨20, 48, 1583⟩
private def endpoint_20_48_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_20_48_base : receiptBase endpoint_20_48_flag endpoint_20_48_sources = some 169131835934391955 := by decide +kernel
private theorem endpoint_20_48_w0 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 2 169131835934391955 = some 169131835934391955 := by decide +kernel
private theorem endpoint_20_48_w2 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 2 2 169131835934391955 = some 169131835934391955 := by decide +kernel
private theorem endpoint_20_48_p4 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 4 169131835934391955 = some 169131835934391955 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 2 2 169131835934391955 169131835934391955 169131835934391955 endpoint_20_48_w0 endpoint_20_48_w2
private theorem endpoint_20_48_w4 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 4 2 169131835934391955 = some 169131835934391955 := by decide +kernel
private theorem endpoint_20_48_p6 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 6 169131835934391955 = some 169131835934391955 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 4 2 169131835934391955 169131835934391955 169131835934391955 endpoint_20_48_p4 endpoint_20_48_w4
private theorem endpoint_20_48_w6 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 6 2 169131835934391955 = some 169131835934391955 := by decide +kernel
private theorem endpoint_20_48_p8 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 8 169131835934391955 = some 169131835934391955 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 6 2 169131835934391955 169131835934391955 169131835934391955 endpoint_20_48_p6 endpoint_20_48_w6
private theorem endpoint_20_48_w8 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 8 2 169131835934391955 = some 169131835934391955 := by decide +kernel
private theorem endpoint_20_48_p10 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 10 169131835934391955 = some 169131835934391955 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 8 2 169131835934391955 169131835934391955 169131835934391955 endpoint_20_48_p8 endpoint_20_48_w8
private theorem endpoint_20_48_w10 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 10 2 169131835934391955 = some 169131835934391955 := by decide +kernel
private theorem endpoint_20_48_p12 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 12 169131835934391955 = some 169131835934391955 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 10 2 169131835934391955 169131835934391955 169131835934391955 endpoint_20_48_p10 endpoint_20_48_w10
private theorem endpoint_20_48_w12 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 12 2 169131835934391955 = some 169131835934391955 := by decide +kernel
private theorem endpoint_20_48_p14 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 14 169131835934391955 = some 169131835934391955 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 12 2 169131835934391955 169131835934391955 169131835934391955 endpoint_20_48_p12 endpoint_20_48_w12
private theorem endpoint_20_48_w14 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 14 2 169131835934391955 = some 169131835934391955 := by decide +kernel
private theorem endpoint_20_48_p16 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 16 169131835934391955 = some 169131835934391955 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 14 2 169131835934391955 169131835934391955 169131835934391955 endpoint_20_48_p14 endpoint_20_48_w14
private theorem endpoint_20_48_w16 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 16 2 169131835934391955 = some 169131835934391955 := by decide +kernel
private theorem endpoint_20_48_p18 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 18 169131835934391955 = some 169131835934391955 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 16 2 169131835934391955 169131835934391955 169131835934391955 endpoint_20_48_p16 endpoint_20_48_w16
private theorem endpoint_20_48_w18 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 18 1 169131835934391955 = some 169131835934391955 := by decide +kernel
private theorem endpoint_20_48_p19 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 19 169131835934391955 = some 169131835934391955 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 18 1 169131835934391955 169131835934391955 169131835934391955 endpoint_20_48_p18 endpoint_20_48_w18
def endpoint_20_48 : CertifiedEndpoint :=
  ⟨⟨20, 48, 1583⟩, 169131835934391955, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_20_48_flag endpoint_20_48_sources 19 169131835934391955 169131835934391955 rfl endpoint_20_48_base endpoint_20_48_p19) (by decide)⟩
private def endpoint_20_49_flag : Flag := ⟨20, 49, 1531⟩
private def endpoint_20_49_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_20_49_base : receiptBase endpoint_20_49_flag endpoint_20_49_sources = some 166610449626183745 := by decide +kernel
private theorem endpoint_20_49_w0 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 2 166610449626183745 = some 166610449626183745 := by decide +kernel
private theorem endpoint_20_49_w2 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 2 2 166610449626183745 = some 166610449626183745 := by decide +kernel
private theorem endpoint_20_49_p4 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 4 166610449626183745 = some 166610449626183745 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 2 2 166610449626183745 166610449626183745 166610449626183745 endpoint_20_49_w0 endpoint_20_49_w2
private theorem endpoint_20_49_w4 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 4 2 166610449626183745 = some 166610449626183745 := by decide +kernel
private theorem endpoint_20_49_p6 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 6 166610449626183745 = some 166610449626183745 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 4 2 166610449626183745 166610449626183745 166610449626183745 endpoint_20_49_p4 endpoint_20_49_w4
private theorem endpoint_20_49_w6 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 6 2 166610449626183745 = some 166610449626183745 := by decide +kernel
private theorem endpoint_20_49_p8 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 8 166610449626183745 = some 166610449626183745 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 6 2 166610449626183745 166610449626183745 166610449626183745 endpoint_20_49_p6 endpoint_20_49_w6
private theorem endpoint_20_49_w8 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 8 2 166610449626183745 = some 166610449626183745 := by decide +kernel
private theorem endpoint_20_49_p10 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 10 166610449626183745 = some 166610449626183745 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 8 2 166610449626183745 166610449626183745 166610449626183745 endpoint_20_49_p8 endpoint_20_49_w8
private theorem endpoint_20_49_w10 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 10 2 166610449626183745 = some 166610449626183745 := by decide +kernel
private theorem endpoint_20_49_p12 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 12 166610449626183745 = some 166610449626183745 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 10 2 166610449626183745 166610449626183745 166610449626183745 endpoint_20_49_p10 endpoint_20_49_w10
private theorem endpoint_20_49_w12 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 12 2 166610449626183745 = some 166610449626183745 := by decide +kernel
private theorem endpoint_20_49_p14 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 14 166610449626183745 = some 166610449626183745 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 12 2 166610449626183745 166610449626183745 166610449626183745 endpoint_20_49_p12 endpoint_20_49_w12
private theorem endpoint_20_49_w14 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 14 2 166610449626183745 = some 166610449626183745 := by decide +kernel
private theorem endpoint_20_49_p16 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 16 166610449626183745 = some 166610449626183745 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 14 2 166610449626183745 166610449626183745 166610449626183745 endpoint_20_49_p14 endpoint_20_49_w14
private theorem endpoint_20_49_w16 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 16 2 166610449626183745 = some 166610449626183745 := by decide +kernel
private theorem endpoint_20_49_p18 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 18 166610449626183745 = some 166610449626183745 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 16 2 166610449626183745 166610449626183745 166610449626183745 endpoint_20_49_p16 endpoint_20_49_w16
private theorem endpoint_20_49_w18 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 18 1 166610449626183745 = some 166610449626183745 := by decide +kernel
private theorem endpoint_20_49_p19 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 19 166610449626183745 = some 166610449626183745 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 18 1 166610449626183745 166610449626183745 166610449626183745 endpoint_20_49_p18 endpoint_20_49_w18
def endpoint_20_49 : CertifiedEndpoint :=
  ⟨⟨20, 49, 1531⟩, 166610449626183745, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_20_49_flag endpoint_20_49_sources 19 166610449626183745 166610449626183745 rfl endpoint_20_49_base endpoint_20_49_p19) (by decide)⟩
private def endpoint_20_50_flag : Flag := ⟨20, 50, 1478⟩
private def endpoint_20_50_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_20_50_base : receiptBase endpoint_20_50_flag endpoint_20_50_sources = some 163780333455864512 := by decide +kernel
private theorem endpoint_20_50_w0 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 2 163780333455864512 = some 164507076765825582 := by decide +kernel
private theorem endpoint_20_50_w2 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 2 2 164507076765825582 = some 164507076765825582 := by decide +kernel
private theorem endpoint_20_50_p4 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 4 163780333455864512 = some 164507076765825582 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 2 2 163780333455864512 164507076765825582 164507076765825582 endpoint_20_50_w0 endpoint_20_50_w2
private theorem endpoint_20_50_w4 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 4 2 164507076765825582 = some 164507076765825582 := by decide +kernel
private theorem endpoint_20_50_p6 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 6 163780333455864512 = some 164507076765825582 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 4 2 163780333455864512 164507076765825582 164507076765825582 endpoint_20_50_p4 endpoint_20_50_w4
private theorem endpoint_20_50_w6 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 6 2 164507076765825582 = some 164507076765825582 := by decide +kernel
private theorem endpoint_20_50_p8 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 8 163780333455864512 = some 164507076765825582 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 6 2 163780333455864512 164507076765825582 164507076765825582 endpoint_20_50_p6 endpoint_20_50_w6
private theorem endpoint_20_50_w8 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 8 2 164507076765825582 = some 164507076765825582 := by decide +kernel
private theorem endpoint_20_50_p10 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 10 163780333455864512 = some 164507076765825582 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 8 2 163780333455864512 164507076765825582 164507076765825582 endpoint_20_50_p8 endpoint_20_50_w8
private theorem endpoint_20_50_w10 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 10 2 164507076765825582 = some 164507076765825582 := by decide +kernel
private theorem endpoint_20_50_p12 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 12 163780333455864512 = some 164507076765825582 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 10 2 163780333455864512 164507076765825582 164507076765825582 endpoint_20_50_p10 endpoint_20_50_w10
private theorem endpoint_20_50_w12 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 12 2 164507076765825582 = some 164507076765825582 := by decide +kernel
private theorem endpoint_20_50_p14 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 14 163780333455864512 = some 164507076765825582 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 12 2 163780333455864512 164507076765825582 164507076765825582 endpoint_20_50_p12 endpoint_20_50_w12
private theorem endpoint_20_50_w14 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 14 2 164507076765825582 = some 164507076765825582 := by decide +kernel
private theorem endpoint_20_50_p16 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 16 163780333455864512 = some 164507076765825582 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 14 2 163780333455864512 164507076765825582 164507076765825582 endpoint_20_50_p14 endpoint_20_50_w14
private theorem endpoint_20_50_w16 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 16 2 164507076765825582 = some 164507076765825582 := by decide +kernel
private theorem endpoint_20_50_p18 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 18 163780333455864512 = some 164507076765825582 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 16 2 163780333455864512 164507076765825582 164507076765825582 endpoint_20_50_p16 endpoint_20_50_w16
private theorem endpoint_20_50_w18 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 18 1 164507076765825582 = some 164507076765825582 := by decide +kernel
private theorem endpoint_20_50_p19 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 19 163780333455864512 = some 164507076765825582 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 18 1 163780333455864512 164507076765825582 164507076765825582 endpoint_20_50_p18 endpoint_20_50_w18
def endpoint_20_50 : CertifiedEndpoint :=
  ⟨⟨20, 50, 1478⟩, 164507076765825582, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_20_50_flag endpoint_20_50_sources 19 163780333455864512 164507076765825582 rfl endpoint_20_50_base endpoint_20_50_p19) (by decide)⟩
private def endpoint_20_51_flag : Flag := ⟨20, 51, 1424⟩
private def endpoint_20_51_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_20_51_base : receiptBase endpoint_20_51_flag endpoint_20_51_sources = some 160635783296346443 := by decide +kernel
private theorem endpoint_20_51_w0 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 0 2 160635783296346443 = some 165254752811588468 := by decide +kernel
private theorem endpoint_20_51_w2 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 2 2 165254752811588468 = some 165254752811588468 := by decide +kernel
private theorem endpoint_20_51_p4 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 0 4 160635783296346443 = some 165254752811588468 :=
  join_receipt_window endpoint_20_51_flag endpoint_20_51_sources 0 2 2 160635783296346443 165254752811588468 165254752811588468 endpoint_20_51_w0 endpoint_20_51_w2
private theorem endpoint_20_51_w4 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 4 2 165254752811588468 = some 165254752811588468 := by decide +kernel
private theorem endpoint_20_51_p6 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 0 6 160635783296346443 = some 165254752811588468 :=
  join_receipt_window endpoint_20_51_flag endpoint_20_51_sources 0 4 2 160635783296346443 165254752811588468 165254752811588468 endpoint_20_51_p4 endpoint_20_51_w4
private theorem endpoint_20_51_w6 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 6 2 165254752811588468 = some 165254752811588468 := by decide +kernel
private theorem endpoint_20_51_p8 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 0 8 160635783296346443 = some 165254752811588468 :=
  join_receipt_window endpoint_20_51_flag endpoint_20_51_sources 0 6 2 160635783296346443 165254752811588468 165254752811588468 endpoint_20_51_p6 endpoint_20_51_w6
private theorem endpoint_20_51_w8 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 8 2 165254752811588468 = some 165254752811588468 := by decide +kernel
private theorem endpoint_20_51_p10 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 0 10 160635783296346443 = some 165254752811588468 :=
  join_receipt_window endpoint_20_51_flag endpoint_20_51_sources 0 8 2 160635783296346443 165254752811588468 165254752811588468 endpoint_20_51_p8 endpoint_20_51_w8
private theorem endpoint_20_51_w10 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 10 2 165254752811588468 = some 165254752811588468 := by decide +kernel
private theorem endpoint_20_51_p12 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 0 12 160635783296346443 = some 165254752811588468 :=
  join_receipt_window endpoint_20_51_flag endpoint_20_51_sources 0 10 2 160635783296346443 165254752811588468 165254752811588468 endpoint_20_51_p10 endpoint_20_51_w10
private theorem endpoint_20_51_w12 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 12 2 165254752811588468 = some 165254752811588468 := by decide +kernel
private theorem endpoint_20_51_p14 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 0 14 160635783296346443 = some 165254752811588468 :=
  join_receipt_window endpoint_20_51_flag endpoint_20_51_sources 0 12 2 160635783296346443 165254752811588468 165254752811588468 endpoint_20_51_p12 endpoint_20_51_w12
private theorem endpoint_20_51_w14 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 14 2 165254752811588468 = some 165254752811588468 := by decide +kernel
private theorem endpoint_20_51_p16 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 0 16 160635783296346443 = some 165254752811588468 :=
  join_receipt_window endpoint_20_51_flag endpoint_20_51_sources 0 14 2 160635783296346443 165254752811588468 165254752811588468 endpoint_20_51_p14 endpoint_20_51_w14
private theorem endpoint_20_51_w16 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 16 2 165254752811588468 = some 165254752811588468 := by decide +kernel
private theorem endpoint_20_51_p18 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 0 18 160635783296346443 = some 165254752811588468 :=
  join_receipt_window endpoint_20_51_flag endpoint_20_51_sources 0 16 2 160635783296346443 165254752811588468 165254752811588468 endpoint_20_51_p16 endpoint_20_51_w16
private theorem endpoint_20_51_w18 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 18 1 165254752811588468 = some 165254752811588468 := by decide +kernel
private theorem endpoint_20_51_p19 : receiptWindow endpoint_20_51_flag endpoint_20_51_sources 0 19 160635783296346443 = some 165254752811588468 :=
  join_receipt_window endpoint_20_51_flag endpoint_20_51_sources 0 18 1 160635783296346443 165254752811588468 165254752811588468 endpoint_20_51_p18 endpoint_20_51_w18
def endpoint_20_51 : CertifiedEndpoint :=
  ⟨⟨20, 51, 1424⟩, 165254752811588468, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_20_51_flag endpoint_20_51_sources 19 160635783296346443 165254752811588468 rfl endpoint_20_51_base endpoint_20_51_p19) (by decide)⟩
private def endpoint_20_52_flag : Flag := ⟨20, 52, 1370⟩
private def endpoint_20_52_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_20_52_base : receiptBase endpoint_20_52_flag endpoint_20_52_sources = some 157283983185971080 := by decide +kernel
private theorem endpoint_20_52_w0 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 0 2 157283983185971080 = some 165827877028403348 := by decide +kernel
private theorem endpoint_20_52_w2 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 2 2 165827877028403348 = some 165827877028403348 := by decide +kernel
private theorem endpoint_20_52_p4 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 0 4 157283983185971080 = some 165827877028403348 :=
  join_receipt_window endpoint_20_52_flag endpoint_20_52_sources 0 2 2 157283983185971080 165827877028403348 165827877028403348 endpoint_20_52_w0 endpoint_20_52_w2
private theorem endpoint_20_52_w4 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 4 2 165827877028403348 = some 165827877028403348 := by decide +kernel
private theorem endpoint_20_52_p6 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 0 6 157283983185971080 = some 165827877028403348 :=
  join_receipt_window endpoint_20_52_flag endpoint_20_52_sources 0 4 2 157283983185971080 165827877028403348 165827877028403348 endpoint_20_52_p4 endpoint_20_52_w4
private theorem endpoint_20_52_w6 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 6 2 165827877028403348 = some 165827877028403348 := by decide +kernel
private theorem endpoint_20_52_p8 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 0 8 157283983185971080 = some 165827877028403348 :=
  join_receipt_window endpoint_20_52_flag endpoint_20_52_sources 0 6 2 157283983185971080 165827877028403348 165827877028403348 endpoint_20_52_p6 endpoint_20_52_w6
private theorem endpoint_20_52_w8 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 8 2 165827877028403348 = some 165827877028403348 := by decide +kernel
private theorem endpoint_20_52_p10 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 0 10 157283983185971080 = some 165827877028403348 :=
  join_receipt_window endpoint_20_52_flag endpoint_20_52_sources 0 8 2 157283983185971080 165827877028403348 165827877028403348 endpoint_20_52_p8 endpoint_20_52_w8
private theorem endpoint_20_52_w10 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 10 2 165827877028403348 = some 165827877028403348 := by decide +kernel
private theorem endpoint_20_52_p12 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 0 12 157283983185971080 = some 165827877028403348 :=
  join_receipt_window endpoint_20_52_flag endpoint_20_52_sources 0 10 2 157283983185971080 165827877028403348 165827877028403348 endpoint_20_52_p10 endpoint_20_52_w10
private theorem endpoint_20_52_w12 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 12 2 165827877028403348 = some 165827877028403348 := by decide +kernel
private theorem endpoint_20_52_p14 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 0 14 157283983185971080 = some 165827877028403348 :=
  join_receipt_window endpoint_20_52_flag endpoint_20_52_sources 0 12 2 157283983185971080 165827877028403348 165827877028403348 endpoint_20_52_p12 endpoint_20_52_w12
private theorem endpoint_20_52_w14 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 14 2 165827877028403348 = some 165827877028403348 := by decide +kernel
private theorem endpoint_20_52_p16 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 0 16 157283983185971080 = some 165827877028403348 :=
  join_receipt_window endpoint_20_52_flag endpoint_20_52_sources 0 14 2 157283983185971080 165827877028403348 165827877028403348 endpoint_20_52_p14 endpoint_20_52_w14
private theorem endpoint_20_52_w16 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 16 2 165827877028403348 = some 165827877028403348 := by decide +kernel
private theorem endpoint_20_52_p18 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 0 18 157283983185971080 = some 165827877028403348 :=
  join_receipt_window endpoint_20_52_flag endpoint_20_52_sources 0 16 2 157283983185971080 165827877028403348 165827877028403348 endpoint_20_52_p16 endpoint_20_52_w16
private theorem endpoint_20_52_w18 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 18 1 165827877028403348 = some 165827877028403348 := by decide +kernel
private theorem endpoint_20_52_p19 : receiptWindow endpoint_20_52_flag endpoint_20_52_sources 0 19 157283983185971080 = some 165827877028403348 :=
  join_receipt_window endpoint_20_52_flag endpoint_20_52_sources 0 18 1 157283983185971080 165827877028403348 165827877028403348 endpoint_20_52_p18 endpoint_20_52_w18
def endpoint_20_52 : CertifiedEndpoint :=
  ⟨⟨20, 52, 1370⟩, 165827877028403348, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_20_52_flag endpoint_20_52_sources 19 157283983185971080 165827877028403348 rfl endpoint_20_52_base endpoint_20_52_p19) (by decide)⟩
private def endpoint_20_53_flag : Flag := ⟨20, 53, 1314⟩
private def endpoint_20_53_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_20_53_base : receiptBase endpoint_20_53_flag endpoint_20_53_sources = some 153495354042487828 := by decide +kernel
private theorem endpoint_20_53_w0 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 0 2 153495354042487828 = some 166095140344882272 := by decide +kernel
private theorem endpoint_20_53_w2 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 2 2 166095140344882272 = some 166095140344882272 := by decide +kernel
private theorem endpoint_20_53_p4 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 0 4 153495354042487828 = some 166095140344882272 :=
  join_receipt_window endpoint_20_53_flag endpoint_20_53_sources 0 2 2 153495354042487828 166095140344882272 166095140344882272 endpoint_20_53_w0 endpoint_20_53_w2
private theorem endpoint_20_53_w4 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 4 2 166095140344882272 = some 166095140344882272 := by decide +kernel
private theorem endpoint_20_53_p6 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 0 6 153495354042487828 = some 166095140344882272 :=
  join_receipt_window endpoint_20_53_flag endpoint_20_53_sources 0 4 2 153495354042487828 166095140344882272 166095140344882272 endpoint_20_53_p4 endpoint_20_53_w4
private theorem endpoint_20_53_w6 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 6 2 166095140344882272 = some 166095140344882272 := by decide +kernel
private theorem endpoint_20_53_p8 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 0 8 153495354042487828 = some 166095140344882272 :=
  join_receipt_window endpoint_20_53_flag endpoint_20_53_sources 0 6 2 153495354042487828 166095140344882272 166095140344882272 endpoint_20_53_p6 endpoint_20_53_w6
private theorem endpoint_20_53_w8 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 8 2 166095140344882272 = some 166095140344882272 := by decide +kernel
private theorem endpoint_20_53_p10 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 0 10 153495354042487828 = some 166095140344882272 :=
  join_receipt_window endpoint_20_53_flag endpoint_20_53_sources 0 8 2 153495354042487828 166095140344882272 166095140344882272 endpoint_20_53_p8 endpoint_20_53_w8
private theorem endpoint_20_53_w10 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 10 2 166095140344882272 = some 166095140344882272 := by decide +kernel
private theorem endpoint_20_53_p12 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 0 12 153495354042487828 = some 166095140344882272 :=
  join_receipt_window endpoint_20_53_flag endpoint_20_53_sources 0 10 2 153495354042487828 166095140344882272 166095140344882272 endpoint_20_53_p10 endpoint_20_53_w10
private theorem endpoint_20_53_w12 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 12 2 166095140344882272 = some 166095140344882272 := by decide +kernel
private theorem endpoint_20_53_p14 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 0 14 153495354042487828 = some 166095140344882272 :=
  join_receipt_window endpoint_20_53_flag endpoint_20_53_sources 0 12 2 153495354042487828 166095140344882272 166095140344882272 endpoint_20_53_p12 endpoint_20_53_w12
private theorem endpoint_20_53_w14 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 14 2 166095140344882272 = some 166095140344882272 := by decide +kernel
private theorem endpoint_20_53_p16 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 0 16 153495354042487828 = some 166095140344882272 :=
  join_receipt_window endpoint_20_53_flag endpoint_20_53_sources 0 14 2 153495354042487828 166095140344882272 166095140344882272 endpoint_20_53_p14 endpoint_20_53_w14
private theorem endpoint_20_53_w16 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 16 2 166095140344882272 = some 166095140344882272 := by decide +kernel
private theorem endpoint_20_53_p18 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 0 18 153495354042487828 = some 166095140344882272 :=
  join_receipt_window endpoint_20_53_flag endpoint_20_53_sources 0 16 2 153495354042487828 166095140344882272 166095140344882272 endpoint_20_53_p16 endpoint_20_53_w16
private theorem endpoint_20_53_w18 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 18 1 166095140344882272 = some 166095140344882272 := by decide +kernel
private theorem endpoint_20_53_p19 : receiptWindow endpoint_20_53_flag endpoint_20_53_sources 0 19 153495354042487828 = some 166095140344882272 :=
  join_receipt_window endpoint_20_53_flag endpoint_20_53_sources 0 18 1 153495354042487828 166095140344882272 166095140344882272 endpoint_20_53_p18 endpoint_20_53_w18
def endpoint_20_53 : CertifiedEndpoint :=
  ⟨⟨20, 53, 1314⟩, 166095140344882272, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_20_53_flag endpoint_20_53_sources 19 153495354042487828 166095140344882272 rfl endpoint_20_53_base endpoint_20_53_p19) (by decide)⟩
private def endpoint_20_54_flag : Flag := ⟨20, 54, 1257⟩
private def endpoint_20_54_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_20_54_base : receiptBase endpoint_20_54_flag endpoint_20_54_sources = some 149375178528542294 := by decide +kernel
private theorem endpoint_20_54_w0 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 0 2 149375178528542294 = some 166114337310286060 := by decide +kernel
private theorem endpoint_20_54_w2 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 2 2 166114337310286060 = some 166114337310286060 := by decide +kernel
private theorem endpoint_20_54_p4 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 0 4 149375178528542294 = some 166114337310286060 :=
  join_receipt_window endpoint_20_54_flag endpoint_20_54_sources 0 2 2 149375178528542294 166114337310286060 166114337310286060 endpoint_20_54_w0 endpoint_20_54_w2
private theorem endpoint_20_54_w4 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 4 2 166114337310286060 = some 166114337310286060 := by decide +kernel
private theorem endpoint_20_54_p6 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 0 6 149375178528542294 = some 166114337310286060 :=
  join_receipt_window endpoint_20_54_flag endpoint_20_54_sources 0 4 2 149375178528542294 166114337310286060 166114337310286060 endpoint_20_54_p4 endpoint_20_54_w4
private theorem endpoint_20_54_w6 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 6 2 166114337310286060 = some 166114337310286060 := by decide +kernel
private theorem endpoint_20_54_p8 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 0 8 149375178528542294 = some 166114337310286060 :=
  join_receipt_window endpoint_20_54_flag endpoint_20_54_sources 0 6 2 149375178528542294 166114337310286060 166114337310286060 endpoint_20_54_p6 endpoint_20_54_w6
private theorem endpoint_20_54_w8 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 8 2 166114337310286060 = some 166114337310286060 := by decide +kernel
private theorem endpoint_20_54_p10 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 0 10 149375178528542294 = some 166114337310286060 :=
  join_receipt_window endpoint_20_54_flag endpoint_20_54_sources 0 8 2 149375178528542294 166114337310286060 166114337310286060 endpoint_20_54_p8 endpoint_20_54_w8
private theorem endpoint_20_54_w10 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 10 2 166114337310286060 = some 166114337310286060 := by decide +kernel
private theorem endpoint_20_54_p12 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 0 12 149375178528542294 = some 166114337310286060 :=
  join_receipt_window endpoint_20_54_flag endpoint_20_54_sources 0 10 2 149375178528542294 166114337310286060 166114337310286060 endpoint_20_54_p10 endpoint_20_54_w10
private theorem endpoint_20_54_w12 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 12 2 166114337310286060 = some 166114337310286060 := by decide +kernel
private theorem endpoint_20_54_p14 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 0 14 149375178528542294 = some 166114337310286060 :=
  join_receipt_window endpoint_20_54_flag endpoint_20_54_sources 0 12 2 149375178528542294 166114337310286060 166114337310286060 endpoint_20_54_p12 endpoint_20_54_w12
private theorem endpoint_20_54_w14 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 14 2 166114337310286060 = some 166114337310286060 := by decide +kernel
private theorem endpoint_20_54_p16 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 0 16 149375178528542294 = some 166114337310286060 :=
  join_receipt_window endpoint_20_54_flag endpoint_20_54_sources 0 14 2 149375178528542294 166114337310286060 166114337310286060 endpoint_20_54_p14 endpoint_20_54_w14
private theorem endpoint_20_54_w16 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 16 2 166114337310286060 = some 166114337310286060 := by decide +kernel
private theorem endpoint_20_54_p18 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 0 18 149375178528542294 = some 166114337310286060 :=
  join_receipt_window endpoint_20_54_flag endpoint_20_54_sources 0 16 2 149375178528542294 166114337310286060 166114337310286060 endpoint_20_54_p16 endpoint_20_54_w16
private theorem endpoint_20_54_w18 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 18 1 166114337310286060 = some 166114337310286060 := by decide +kernel
private theorem endpoint_20_54_p19 : receiptWindow endpoint_20_54_flag endpoint_20_54_sources 0 19 149375178528542294 = some 166114337310286060 :=
  join_receipt_window endpoint_20_54_flag endpoint_20_54_sources 0 18 1 149375178528542294 166114337310286060 166114337310286060 endpoint_20_54_p18 endpoint_20_54_w18
def endpoint_20_54 : CertifiedEndpoint :=
  ⟨⟨20, 54, 1257⟩, 166114337310286060, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_20_54_flag endpoint_20_54_sources 19 149375178528542294 166114337310286060 rfl endpoint_20_54_base endpoint_20_54_p19) (by decide)⟩
def endpoint_20_55 : CertifiedEndpoint :=
  ⟨⟨20, 55, 1200⟩, 261560388089914485, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_56 : CertifiedEndpoint :=
  ⟨⟨20, 56, 1141⟩, 253807785439404631, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_57 : CertifiedEndpoint :=
  ⟨⟨20, 57, 1082⟩, 245456157456682687, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_58 : CertifiedEndpoint :=
  ⟨⟨20, 58, 1021⟩, 236027273349175391, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_59 : CertifiedEndpoint :=
  ⟨⟨20, 59, 959⟩, 225735079381563824, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_60 : CertifiedEndpoint :=
  ⟨⟨20, 60, 896⟩, 214564474074884656, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_61 : CertifiedEndpoint :=
  ⟨⟨20, 61, 832⟩, 202500355950174557, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_62 : CertifiedEndpoint :=
  ⟨⟨20, 62, 766⟩, 189268372826899126, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_63 : CertifiedEndpoint :=
  ⟨⟨20, 63, 700⟩, 175366890802916065, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_64 : CertifiedEndpoint :=
  ⟨⟨20, 64, 632⟩, 160257273169798792, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_65 : CertifiedEndpoint :=
  ⟨⟨20, 65, 563⟩, 144183669150155048, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_66 : CertifiedEndpoint :=
  ⟨⟨20, 66, 492⟩, 126851591258165992, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_67 : CertifiedEndpoint :=
  ⟨⟨20, 67, 420⟩, 108515256369081585, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_68 : CertifiedEndpoint :=
  ⟨⟨20, 68, 347⟩, 89159563003938497, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_69 : CertifiedEndpoint :=
  ⟨⟨20, 69, 272⟩, 68474922197954557, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_70 : CertifiedEndpoint :=
  ⟨⟨20, 70, 196⟩, 46730652305343056, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_71 : CertifiedEndpoint :=
  ⟨⟨20, 71, 118⟩, 23607096708679603, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_21 : CertifiedEndpoint :=
  ⟨⟨21, 21, 2400⟩, 143140123312932609, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_22 : CertifiedEndpoint :=
  ⟨⟨21, 22, 2363⟩, 144999897313785444, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_23 : CertifiedEndpoint :=
  ⟨⟨21, 23, 2325⟩, 146667123085194830, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_24 : CertifiedEndpoint :=
  ⟨⟨21, 24, 2287⟩, 156231236079348943, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_25 : CertifiedEndpoint :=
  ⟨⟨21, 25, 2248⟩, 165313811135468135, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_26 : CertifiedEndpoint :=
  ⟨⟨21, 26, 2209⟩, 173978355270208729, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_27 : CertifiedEndpoint :=
  ⟨⟨21, 27, 2169⟩, 182140195344312954, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_28 : CertifiedEndpoint :=
  ⟨⟨21, 28, 2129⟩, 189873421435737857, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_29 : CertifiedEndpoint :=
  ⟨⟨21, 29, 2088⟩, 197082777343924943, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_30 : CertifiedEndpoint :=
  ⟨⟨21, 30, 2047⟩, 203852936208131983, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_31 : CertifiedEndpoint :=
  ⟨⟨21, 31, 2005⟩, 210078058766499758, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_32 : CertifiedEndpoint :=
  ⟨⟨21, 32, 1963⟩, 215853401219586763, .intrinsic (by decide +kernel) (by decide)⟩

def endpointBlock12 : List CertifiedEndpoint := [
  endpoint_18_73, endpoint_18_74, endpoint_18_75, endpoint_18_76, endpoint_18_77, endpoint_18_78, endpoint_18_79,
  endpoint_18_80, endpoint_19_19, endpoint_19_20, endpoint_19_21, endpoint_19_22, endpoint_19_23, endpoint_19_24,
  endpoint_19_25, endpoint_19_26, endpoint_19_27, endpoint_19_28, endpoint_19_29, endpoint_19_30, endpoint_19_31,
  endpoint_19_32, endpoint_19_33, endpoint_19_34, endpoint_19_35, endpoint_19_36, endpoint_19_37, endpoint_19_38,
  endpoint_19_39, endpoint_19_40, endpoint_19_41, endpoint_19_42, endpoint_19_43, endpoint_19_44, endpoint_19_45,
  endpoint_19_46, endpoint_19_47, endpoint_19_48, endpoint_19_49, endpoint_19_50, endpoint_19_51, endpoint_19_52,
  endpoint_19_53, endpoint_19_54, endpoint_19_55, endpoint_19_56, endpoint_19_57, endpoint_19_58, endpoint_19_59,
  endpoint_19_60, endpoint_19_61, endpoint_19_62, endpoint_19_63, endpoint_19_64, endpoint_19_65, endpoint_19_66,
  endpoint_19_67, endpoint_19_68, endpoint_19_69, endpoint_19_70, endpoint_19_71, endpoint_19_72, endpoint_19_73,
  endpoint_19_74, endpoint_19_75, endpoint_19_76, endpoint_20_20, endpoint_20_21, endpoint_20_22, endpoint_20_23,
  endpoint_20_24, endpoint_20_25, endpoint_20_26, endpoint_20_27, endpoint_20_28, endpoint_20_29, endpoint_20_30,
  endpoint_20_31, endpoint_20_32, endpoint_20_33, endpoint_20_34, endpoint_20_35, endpoint_20_36, endpoint_20_37,
  endpoint_20_38, endpoint_20_39, endpoint_20_40, endpoint_20_41, endpoint_20_42, endpoint_20_43, endpoint_20_44,
  endpoint_20_45, endpoint_20_46, endpoint_20_47, endpoint_20_48, endpoint_20_49, endpoint_20_50, endpoint_20_51,
  endpoint_20_52, endpoint_20_53, endpoint_20_54, endpoint_20_55, endpoint_20_56, endpoint_20_57, endpoint_20_58,
  endpoint_20_59, endpoint_20_60, endpoint_20_61, endpoint_20_62, endpoint_20_63, endpoint_20_64, endpoint_20_65,
  endpoint_20_66, endpoint_20_67, endpoint_20_68, endpoint_20_69, endpoint_20_70, endpoint_20_71, endpoint_21_21,
  endpoint_21_22, endpoint_21_23, endpoint_21_24, endpoint_21_25, endpoint_21_26, endpoint_21_27, endpoint_21_28,
  endpoint_21_29, endpoint_21_30, endpoint_21_31, endpoint_21_32
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
