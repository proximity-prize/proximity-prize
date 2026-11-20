import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_13_47_flag : Flag := ⟨13, 47, 3289⟩
private def endpoint_13_47_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_47_base : receiptBase endpoint_13_47_flag endpoint_13_47_sources = some 235839448964805739 := by decide +kernel
private theorem endpoint_13_47_w0 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 2 235839448964805739 = some 244661542133395700 := by decide +kernel
private theorem endpoint_13_47_w2 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 2 2 244661542133395700 = some 244661542133395700 := by decide +kernel
private theorem endpoint_13_47_p4 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 4 235839448964805739 = some 244661542133395700 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 2 2 235839448964805739 244661542133395700 244661542133395700 endpoint_13_47_w0 endpoint_13_47_w2
private theorem endpoint_13_47_w4 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 4 2 244661542133395700 = some 244661542133395700 := by decide +kernel
private theorem endpoint_13_47_p6 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 6 235839448964805739 = some 244661542133395700 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 4 2 235839448964805739 244661542133395700 244661542133395700 endpoint_13_47_p4 endpoint_13_47_w4
private theorem endpoint_13_47_w6 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 6 2 244661542133395700 = some 244661542133395700 := by decide +kernel
private theorem endpoint_13_47_p8 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 8 235839448964805739 = some 244661542133395700 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 6 2 235839448964805739 244661542133395700 244661542133395700 endpoint_13_47_p6 endpoint_13_47_w6
private theorem endpoint_13_47_w8 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 8 2 244661542133395700 = some 244661542133395700 := by decide +kernel
private theorem endpoint_13_47_p10 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 10 235839448964805739 = some 244661542133395700 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 8 2 235839448964805739 244661542133395700 244661542133395700 endpoint_13_47_p8 endpoint_13_47_w8
private theorem endpoint_13_47_w10 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 10 2 244661542133395700 = some 244661542133395700 := by decide +kernel
private theorem endpoint_13_47_p12 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 12 235839448964805739 = some 244661542133395700 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 10 2 235839448964805739 244661542133395700 244661542133395700 endpoint_13_47_p10 endpoint_13_47_w10
def endpoint_13_47 : CertifiedEndpoint :=
  ⟨⟨13, 47, 3289⟩, 244661542133395700, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_47_flag endpoint_13_47_sources 12 235839448964805739 244661542133395700 rfl endpoint_13_47_base endpoint_13_47_p12) (by decide)⟩
private def endpoint_13_48_flag : Flag := ⟨13, 48, 3257⟩
private def endpoint_13_48_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_48_base : receiptBase endpoint_13_48_flag endpoint_13_48_sources = some 238631408264759623 := by decide +kernel
private theorem endpoint_13_48_w0 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 2 238631408264759623 = some 245540708864974442 := by decide +kernel
private theorem endpoint_13_48_w2 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 2 2 245540708864974442 = some 245540708864974442 := by decide +kernel
private theorem endpoint_13_48_p4 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 4 238631408264759623 = some 245540708864974442 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 2 2 238631408264759623 245540708864974442 245540708864974442 endpoint_13_48_w0 endpoint_13_48_w2
private theorem endpoint_13_48_w4 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 4 2 245540708864974442 = some 245540708864974442 := by decide +kernel
private theorem endpoint_13_48_p6 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 6 238631408264759623 = some 245540708864974442 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 4 2 238631408264759623 245540708864974442 245540708864974442 endpoint_13_48_p4 endpoint_13_48_w4
private theorem endpoint_13_48_w6 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 6 2 245540708864974442 = some 245540708864974442 := by decide +kernel
private theorem endpoint_13_48_p8 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 8 238631408264759623 = some 245540708864974442 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 6 2 238631408264759623 245540708864974442 245540708864974442 endpoint_13_48_p6 endpoint_13_48_w6
private theorem endpoint_13_48_w8 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 8 2 245540708864974442 = some 245540708864974442 := by decide +kernel
private theorem endpoint_13_48_p10 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 10 238631408264759623 = some 245540708864974442 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 8 2 238631408264759623 245540708864974442 245540708864974442 endpoint_13_48_p8 endpoint_13_48_w8
private theorem endpoint_13_48_w10 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 10 2 245540708864974442 = some 245540708864974442 := by decide +kernel
private theorem endpoint_13_48_p12 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 12 238631408264759623 = some 245540708864974442 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 10 2 238631408264759623 245540708864974442 245540708864974442 endpoint_13_48_p10 endpoint_13_48_w10
def endpoint_13_48 : CertifiedEndpoint :=
  ⟨⟨13, 48, 3257⟩, 245540708864974442, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_48_flag endpoint_13_48_sources 12 238631408264759623 245540708864974442 rfl endpoint_13_48_base endpoint_13_48_p12) (by decide)⟩
private def endpoint_13_49_flag : Flag := ⟨13, 49, 3224⟩
private def endpoint_13_49_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_49_base : receiptBase endpoint_13_49_flag endpoint_13_49_sources = some 240508651167483899 := by decide +kernel
private theorem endpoint_13_49_w0 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 2 240508651167483899 = some 250216197911991706 := by decide +kernel
private theorem endpoint_13_49_w2 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 2 2 250216197911991706 = some 250216197911991706 := by decide +kernel
private theorem endpoint_13_49_p4 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 4 240508651167483899 = some 250216197911991706 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 2 2 240508651167483899 250216197911991706 250216197911991706 endpoint_13_49_w0 endpoint_13_49_w2
private theorem endpoint_13_49_w4 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 4 2 250216197911991706 = some 250216197911991706 := by decide +kernel
private theorem endpoint_13_49_p6 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 6 240508651167483899 = some 250216197911991706 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 4 2 240508651167483899 250216197911991706 250216197911991706 endpoint_13_49_p4 endpoint_13_49_w4
private theorem endpoint_13_49_w6 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 6 2 250216197911991706 = some 250216197911991706 := by decide +kernel
private theorem endpoint_13_49_p8 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 8 240508651167483899 = some 250216197911991706 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 6 2 240508651167483899 250216197911991706 250216197911991706 endpoint_13_49_p6 endpoint_13_49_w6
private theorem endpoint_13_49_w8 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 8 2 250216197911991706 = some 250216197911991706 := by decide +kernel
private theorem endpoint_13_49_p10 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 10 240508651167483899 = some 250216197911991706 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 8 2 240508651167483899 250216197911991706 250216197911991706 endpoint_13_49_p8 endpoint_13_49_w8
private theorem endpoint_13_49_w10 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 10 2 250216197911991706 = some 250216197911991706 := by decide +kernel
private theorem endpoint_13_49_p12 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 12 240508651167483899 = some 250216197911991706 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 10 2 240508651167483899 250216197911991706 250216197911991706 endpoint_13_49_p10 endpoint_13_49_w10
def endpoint_13_49 : CertifiedEndpoint :=
  ⟨⟨13, 49, 3224⟩, 250216197911991706, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_49_flag endpoint_13_49_sources 12 240508651167483899 250216197911991706 rfl endpoint_13_49_base endpoint_13_49_p12) (by decide)⟩
private def endpoint_13_50_flag : Flag := ⟨13, 50, 3190⟩
private def endpoint_13_50_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_50_base : receiptBase endpoint_13_50_flag endpoint_13_50_sources = some 242224162134459096 := by decide +kernel
private theorem endpoint_13_50_w0 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 2 242224162134459096 = some 254783614240427096 := by decide +kernel
private theorem endpoint_13_50_w2 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 2 2 254783614240427096 = some 254783614240427096 := by decide +kernel
private theorem endpoint_13_50_p4 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 4 242224162134459096 = some 254783614240427096 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 2 2 242224162134459096 254783614240427096 254783614240427096 endpoint_13_50_w0 endpoint_13_50_w2
private theorem endpoint_13_50_w4 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 4 2 254783614240427096 = some 254783614240427096 := by decide +kernel
private theorem endpoint_13_50_p6 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 6 242224162134459096 = some 254783614240427096 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 4 2 242224162134459096 254783614240427096 254783614240427096 endpoint_13_50_p4 endpoint_13_50_w4
private theorem endpoint_13_50_w6 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 6 2 254783614240427096 = some 254783614240427096 := by decide +kernel
private theorem endpoint_13_50_p8 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 8 242224162134459096 = some 254783614240427096 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 6 2 242224162134459096 254783614240427096 254783614240427096 endpoint_13_50_p6 endpoint_13_50_w6
private theorem endpoint_13_50_w8 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 8 2 254783614240427096 = some 254783614240427096 := by decide +kernel
private theorem endpoint_13_50_p10 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 10 242224162134459096 = some 254783614240427096 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 8 2 242224162134459096 254783614240427096 254783614240427096 endpoint_13_50_p8 endpoint_13_50_w8
private theorem endpoint_13_50_w10 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 10 2 254783614240427096 = some 254783614240427096 := by decide +kernel
private theorem endpoint_13_50_p12 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 12 242224162134459096 = some 254783614240427096 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 10 2 242224162134459096 254783614240427096 254783614240427096 endpoint_13_50_p10 endpoint_13_50_w10
def endpoint_13_50 : CertifiedEndpoint :=
  ⟨⟨13, 50, 3190⟩, 254783614240427096, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_50_flag endpoint_13_50_sources 12 242224162134459096 254783614240427096 rfl endpoint_13_50_base endpoint_13_50_p12) (by decide)⟩
private def endpoint_13_51_flag : Flag := ⟨13, 51, 3156⟩
private def endpoint_13_51_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_51_base : receiptBase endpoint_13_51_flag endpoint_13_51_sources = some 245846678093787030 := by decide +kernel
private theorem endpoint_13_51_w0 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 2 245846678093787030 = some 252008917731164247 := by decide +kernel
private theorem endpoint_13_51_w2 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 2 2 252008917731164247 = some 252008917731164247 := by decide +kernel
private theorem endpoint_13_51_p4 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 4 245846678093787030 = some 252008917731164247 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 2 2 245846678093787030 252008917731164247 252008917731164247 endpoint_13_51_w0 endpoint_13_51_w2
private theorem endpoint_13_51_w4 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 4 2 252008917731164247 = some 252008917731164247 := by decide +kernel
private theorem endpoint_13_51_p6 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 6 245846678093787030 = some 252008917731164247 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 4 2 245846678093787030 252008917731164247 252008917731164247 endpoint_13_51_p4 endpoint_13_51_w4
private theorem endpoint_13_51_w6 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 6 2 252008917731164247 = some 252008917731164247 := by decide +kernel
private theorem endpoint_13_51_p8 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 8 245846678093787030 = some 252008917731164247 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 6 2 245846678093787030 252008917731164247 252008917731164247 endpoint_13_51_p6 endpoint_13_51_w6
private theorem endpoint_13_51_w8 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 8 2 252008917731164247 = some 252008917731164247 := by decide +kernel
private theorem endpoint_13_51_p10 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 10 245846678093787030 = some 252008917731164247 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 8 2 245846678093787030 252008917731164247 252008917731164247 endpoint_13_51_p8 endpoint_13_51_w8
private theorem endpoint_13_51_w10 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 10 2 252008917731164247 = some 252008917731164247 := by decide +kernel
private theorem endpoint_13_51_p12 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 12 245846678093787030 = some 252008917731164247 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 10 2 245846678093787030 252008917731164247 252008917731164247 endpoint_13_51_p10 endpoint_13_51_w10
def endpoint_13_51 : CertifiedEndpoint :=
  ⟨⟨13, 51, 3156⟩, 252008917731164247, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_51_flag endpoint_13_51_sources 12 245846678093787030 252008917731164247 rfl endpoint_13_51_base endpoint_13_51_p12) (by decide)⟩
private def endpoint_13_52_flag : Flag := ⟨13, 52, 3120⟩
private def endpoint_13_52_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_52_base : receiptBase endpoint_13_52_flag endpoint_13_52_sources = some 247175263672427942 := by decide +kernel
private theorem endpoint_13_52_w0 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 2 247175263672427942 = some 256186298251285312 := by decide +kernel
private theorem endpoint_13_52_w2 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 2 2 256186298251285312 = some 256186298251285312 := by decide +kernel
private theorem endpoint_13_52_p4 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 4 247175263672427942 = some 256186298251285312 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 2 2 247175263672427942 256186298251285312 256186298251285312 endpoint_13_52_w0 endpoint_13_52_w2
private theorem endpoint_13_52_w4 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 4 2 256186298251285312 = some 256186298251285312 := by decide +kernel
private theorem endpoint_13_52_p6 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 6 247175263672427942 = some 256186298251285312 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 4 2 247175263672427942 256186298251285312 256186298251285312 endpoint_13_52_p4 endpoint_13_52_w4
private theorem endpoint_13_52_w6 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 6 2 256186298251285312 = some 256186298251285312 := by decide +kernel
private theorem endpoint_13_52_p8 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 8 247175263672427942 = some 256186298251285312 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 6 2 247175263672427942 256186298251285312 256186298251285312 endpoint_13_52_p6 endpoint_13_52_w6
private theorem endpoint_13_52_w8 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 8 2 256186298251285312 = some 256186298251285312 := by decide +kernel
private theorem endpoint_13_52_p10 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 10 247175263672427942 = some 256186298251285312 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 8 2 247175263672427942 256186298251285312 256186298251285312 endpoint_13_52_p8 endpoint_13_52_w8
private theorem endpoint_13_52_w10 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 10 2 256186298251285312 = some 256186298251285312 := by decide +kernel
private theorem endpoint_13_52_p12 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 12 247175263672427942 = some 256186298251285312 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 10 2 247175263672427942 256186298251285312 256186298251285312 endpoint_13_52_p10 endpoint_13_52_w10
def endpoint_13_52 : CertifiedEndpoint :=
  ⟨⟨13, 52, 3120⟩, 256186298251285312, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_52_flag endpoint_13_52_sources 12 247175263672427942 256186298251285312 rfl endpoint_13_52_base endpoint_13_52_p12) (by decide)⟩
private def endpoint_13_53_flag : Flag := ⟨13, 53, 3084⟩
private def endpoint_13_53_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_53_base : receiptBase endpoint_13_53_flag endpoint_13_53_sources = some 248409359434188326 := by decide +kernel
private theorem endpoint_13_53_w0 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 2 248409359434188326 = some 260290817102396187 := by decide +kernel
private theorem endpoint_13_53_w2 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 2 2 260290817102396187 = some 260290817102396187 := by decide +kernel
private theorem endpoint_13_53_p4 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 4 248409359434188326 = some 260290817102396187 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 2 2 248409359434188326 260290817102396187 260290817102396187 endpoint_13_53_w0 endpoint_13_53_w2
private theorem endpoint_13_53_w4 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 4 2 260290817102396187 = some 260290817102396187 := by decide +kernel
private theorem endpoint_13_53_p6 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 6 248409359434188326 = some 260290817102396187 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 4 2 248409359434188326 260290817102396187 260290817102396187 endpoint_13_53_p4 endpoint_13_53_w4
private theorem endpoint_13_53_w6 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 6 2 260290817102396187 = some 260290817102396187 := by decide +kernel
private theorem endpoint_13_53_p8 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 8 248409359434188326 = some 260290817102396187 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 6 2 248409359434188326 260290817102396187 260290817102396187 endpoint_13_53_p6 endpoint_13_53_w6
private theorem endpoint_13_53_w8 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 8 2 260290817102396187 = some 260290817102396187 := by decide +kernel
private theorem endpoint_13_53_p10 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 10 248409359434188326 = some 260290817102396187 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 8 2 248409359434188326 260290817102396187 260290817102396187 endpoint_13_53_p8 endpoint_13_53_w8
private theorem endpoint_13_53_w10 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 10 2 260290817102396187 = some 260290817102396187 := by decide +kernel
private theorem endpoint_13_53_p12 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 12 248409359434188326 = some 260290817102396187 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 10 2 248409359434188326 260290817102396187 260290817102396187 endpoint_13_53_p10 endpoint_13_53_w10
def endpoint_13_53 : CertifiedEndpoint :=
  ⟨⟨13, 53, 3084⟩, 260290817102396187, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_53_flag endpoint_13_53_sources 12 248409359434188326 260290817102396187 rfl endpoint_13_53_base endpoint_13_53_p12) (by decide)⟩
private def endpoint_13_54_flag : Flag := ⟨13, 54, 3046⟩
private def endpoint_13_54_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_54_base : receiptBase endpoint_13_54_flag endpoint_13_54_sources = some 254247972352422479 := by decide +kernel
private theorem endpoint_13_54_w0 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 2 254247972352422479 = some 254247972352422479 := by decide +kernel
private theorem endpoint_13_54_w2 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 2 2 254247972352422479 = some 254247972352422479 := by decide +kernel
private theorem endpoint_13_54_p4 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 4 254247972352422479 = some 254247972352422479 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 2 2 254247972352422479 254247972352422479 254247972352422479 endpoint_13_54_w0 endpoint_13_54_w2
private theorem endpoint_13_54_w4 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 4 2 254247972352422479 = some 254247972352422479 := by decide +kernel
private theorem endpoint_13_54_p6 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 6 254247972352422479 = some 254247972352422479 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 4 2 254247972352422479 254247972352422479 254247972352422479 endpoint_13_54_p4 endpoint_13_54_w4
private theorem endpoint_13_54_w6 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 6 2 254247972352422479 = some 254247972352422479 := by decide +kernel
private theorem endpoint_13_54_p8 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 8 254247972352422479 = some 254247972352422479 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 6 2 254247972352422479 254247972352422479 254247972352422479 endpoint_13_54_p6 endpoint_13_54_w6
private theorem endpoint_13_54_w8 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 8 2 254247972352422479 = some 254247972352422479 := by decide +kernel
private theorem endpoint_13_54_p10 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 10 254247972352422479 = some 254247972352422479 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 8 2 254247972352422479 254247972352422479 254247972352422479 endpoint_13_54_p8 endpoint_13_54_w8
private theorem endpoint_13_54_w10 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 10 2 254247972352422479 = some 254247972352422479 := by decide +kernel
private theorem endpoint_13_54_p12 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 12 254247972352422479 = some 254247972352422479 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 10 2 254247972352422479 254247972352422479 254247972352422479 endpoint_13_54_p10 endpoint_13_54_w10
def endpoint_13_54 : CertifiedEndpoint :=
  ⟨⟨13, 54, 3046⟩, 254247972352422479, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_54_flag endpoint_13_54_sources 12 254247972352422479 254247972352422479 rfl endpoint_13_54_base endpoint_13_54_p12) (by decide)⟩
private def endpoint_13_55_flag : Flag := ⟨13, 55, 3008⟩
private def endpoint_13_55_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_13_55_base : receiptBase endpoint_13_55_flag endpoint_13_55_sources = some 251180168191570866 := by decide +kernel
private theorem endpoint_13_55_w0 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 2 251180168191570866 = some 260160081951049586 := by decide +kernel
private theorem endpoint_13_55_w2 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 2 2 260160081951049586 = some 260160081951049586 := by decide +kernel
private theorem endpoint_13_55_p4 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 4 251180168191570866 = some 260160081951049586 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 2 2 251180168191570866 260160081951049586 260160081951049586 endpoint_13_55_w0 endpoint_13_55_w2
private theorem endpoint_13_55_w4 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 4 2 260160081951049586 = some 260160081951049586 := by decide +kernel
private theorem endpoint_13_55_p6 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 6 251180168191570866 = some 260160081951049586 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 4 2 251180168191570866 260160081951049586 260160081951049586 endpoint_13_55_p4 endpoint_13_55_w4
private theorem endpoint_13_55_w6 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 6 2 260160081951049586 = some 260160081951049586 := by decide +kernel
private theorem endpoint_13_55_p8 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 8 251180168191570866 = some 260160081951049586 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 6 2 251180168191570866 260160081951049586 260160081951049586 endpoint_13_55_p6 endpoint_13_55_w6
private theorem endpoint_13_55_w8 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 8 2 260160081951049586 = some 260160081951049586 := by decide +kernel
private theorem endpoint_13_55_p10 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 10 251180168191570866 = some 260160081951049586 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 8 2 251180168191570866 260160081951049586 260160081951049586 endpoint_13_55_p8 endpoint_13_55_w8
private theorem endpoint_13_55_w10 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 10 2 260160081951049586 = some 260160081951049586 := by decide +kernel
private theorem endpoint_13_55_p12 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 12 251180168191570866 = some 260160081951049586 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 10 2 251180168191570866 260160081951049586 260160081951049586 endpoint_13_55_p10 endpoint_13_55_w10
def endpoint_13_55 : CertifiedEndpoint :=
  ⟨⟨13, 55, 3008⟩, 260160081951049586, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_13_55_flag endpoint_13_55_sources 12 251180168191570866 260160081951049586 rfl endpoint_13_55_base endpoint_13_55_p12) (by decide)⟩
private def endpoint_13_56_flag : Flag := ⟨13, 56, 2968⟩
private def endpoint_13_56_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_56_base : receiptBase endpoint_13_56_flag endpoint_13_56_sources = some 255826251520491147 := by decide +kernel
private theorem endpoint_13_56_w0 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 2 255826251520491147 = some 255826251520491147 := by decide +kernel
private theorem endpoint_13_56_w2 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 2 2 255826251520491147 = some 255826251520491147 := by decide +kernel
private theorem endpoint_13_56_p4 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 4 255826251520491147 = some 255826251520491147 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 2 2 255826251520491147 255826251520491147 255826251520491147 endpoint_13_56_w0 endpoint_13_56_w2
private theorem endpoint_13_56_w4 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 4 2 255826251520491147 = some 255826251520491147 := by decide +kernel
private theorem endpoint_13_56_p6 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 6 255826251520491147 = some 255826251520491147 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 4 2 255826251520491147 255826251520491147 255826251520491147 endpoint_13_56_p4 endpoint_13_56_w4
private theorem endpoint_13_56_w6 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 6 2 255826251520491147 = some 255826251520491147 := by decide +kernel
private theorem endpoint_13_56_p8 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 8 255826251520491147 = some 255826251520491147 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 6 2 255826251520491147 255826251520491147 255826251520491147 endpoint_13_56_p6 endpoint_13_56_w6
private theorem endpoint_13_56_w8 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 8 2 255826251520491147 = some 255826251520491147 := by decide +kernel
private theorem endpoint_13_56_p10 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 10 255826251520491147 = some 255826251520491147 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 8 2 255826251520491147 255826251520491147 255826251520491147 endpoint_13_56_p8 endpoint_13_56_w8
private theorem endpoint_13_56_w10 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 10 2 255826251520491147 = some 255826251520491147 := by decide +kernel
private theorem endpoint_13_56_p12 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 12 255826251520491147 = some 255826251520491147 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 10 2 255826251520491147 255826251520491147 255826251520491147 endpoint_13_56_p10 endpoint_13_56_w10
def endpoint_13_56 : CertifiedEndpoint :=
  ⟨⟨13, 56, 2968⟩, 255826251520491147, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_56_flag endpoint_13_56_sources 12 255826251520491147 255826251520491147 rfl endpoint_13_56_base endpoint_13_56_p12) (by decide)⟩
private def endpoint_13_57_flag : Flag := ⟨13, 57, 2927⟩
private def endpoint_13_57_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_57_base : receiptBase endpoint_13_57_flag endpoint_13_57_sources = some 256283610849004362 := by decide +kernel
private theorem endpoint_13_57_w0 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 2 256283610849004362 = some 256283610849004362 := by decide +kernel
private theorem endpoint_13_57_w2 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 2 2 256283610849004362 = some 256283610849004362 := by decide +kernel
private theorem endpoint_13_57_p4 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 4 256283610849004362 = some 256283610849004362 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 2 2 256283610849004362 256283610849004362 256283610849004362 endpoint_13_57_w0 endpoint_13_57_w2
private theorem endpoint_13_57_w4 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 4 2 256283610849004362 = some 256283610849004362 := by decide +kernel
private theorem endpoint_13_57_p6 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 6 256283610849004362 = some 256283610849004362 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 4 2 256283610849004362 256283610849004362 256283610849004362 endpoint_13_57_p4 endpoint_13_57_w4
private theorem endpoint_13_57_w6 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 6 2 256283610849004362 = some 256283610849004362 := by decide +kernel
private theorem endpoint_13_57_p8 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 8 256283610849004362 = some 256283610849004362 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 6 2 256283610849004362 256283610849004362 256283610849004362 endpoint_13_57_p6 endpoint_13_57_w6
private theorem endpoint_13_57_w8 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 8 2 256283610849004362 = some 256283610849004362 := by decide +kernel
private theorem endpoint_13_57_p10 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 10 256283610849004362 = some 256283610849004362 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 8 2 256283610849004362 256283610849004362 256283610849004362 endpoint_13_57_p8 endpoint_13_57_w8
private theorem endpoint_13_57_w10 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 10 2 256283610849004362 = some 256283610849004362 := by decide +kernel
private theorem endpoint_13_57_p12 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 12 256283610849004362 = some 256283610849004362 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 10 2 256283610849004362 256283610849004362 256283610849004362 endpoint_13_57_p10 endpoint_13_57_w10
def endpoint_13_57 : CertifiedEndpoint :=
  ⟨⟨13, 57, 2927⟩, 256283610849004362, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_57_flag endpoint_13_57_sources 12 256283610849004362 256283610849004362 rfl endpoint_13_57_base endpoint_13_57_p12) (by decide)⟩
private def endpoint_13_58_flag : Flag := ⟨13, 58, 2885⟩
private def endpoint_13_58_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_58_base : receiptBase endpoint_13_58_flag endpoint_13_58_sources = some 256541930353664321 := by decide +kernel
private theorem endpoint_13_58_w0 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 2 256541930353664321 = some 256541930353664321 := by decide +kernel
private theorem endpoint_13_58_w2 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 2 2 256541930353664321 = some 256541930353664321 := by decide +kernel
private theorem endpoint_13_58_p4 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 4 256541930353664321 = some 256541930353664321 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 2 2 256541930353664321 256541930353664321 256541930353664321 endpoint_13_58_w0 endpoint_13_58_w2
private theorem endpoint_13_58_w4 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 4 2 256541930353664321 = some 256541930353664321 := by decide +kernel
private theorem endpoint_13_58_p6 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 6 256541930353664321 = some 256541930353664321 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 4 2 256541930353664321 256541930353664321 256541930353664321 endpoint_13_58_p4 endpoint_13_58_w4
private theorem endpoint_13_58_w6 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 6 2 256541930353664321 = some 256541930353664321 := by decide +kernel
private theorem endpoint_13_58_p8 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 8 256541930353664321 = some 256541930353664321 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 6 2 256541930353664321 256541930353664321 256541930353664321 endpoint_13_58_p6 endpoint_13_58_w6
private theorem endpoint_13_58_w8 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 8 2 256541930353664321 = some 256541930353664321 := by decide +kernel
private theorem endpoint_13_58_p10 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 10 256541930353664321 = some 256541930353664321 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 8 2 256541930353664321 256541930353664321 256541930353664321 endpoint_13_58_p8 endpoint_13_58_w8
private theorem endpoint_13_58_w10 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 10 2 256541930353664321 = some 256541930353664321 := by decide +kernel
private theorem endpoint_13_58_p12 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 12 256541930353664321 = some 256541930353664321 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 10 2 256541930353664321 256541930353664321 256541930353664321 endpoint_13_58_p10 endpoint_13_58_w10
def endpoint_13_58 : CertifiedEndpoint :=
  ⟨⟨13, 58, 2885⟩, 256541930353664321, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_58_flag endpoint_13_58_sources 12 256541930353664321 256541930353664321 rfl endpoint_13_58_base endpoint_13_58_p12) (by decide)⟩
private def endpoint_13_59_flag : Flag := ⟨13, 59, 2841⟩
private def endpoint_13_59_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_59_base : receiptBase endpoint_13_59_flag endpoint_13_59_sources = some 256507981361782333 := by decide +kernel
private theorem endpoint_13_59_w0 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 2 256507981361782333 = some 256507981361782333 := by decide +kernel
private theorem endpoint_13_59_w2 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 2 2 256507981361782333 = some 256507981361782333 := by decide +kernel
private theorem endpoint_13_59_p4 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 4 256507981361782333 = some 256507981361782333 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 2 2 256507981361782333 256507981361782333 256507981361782333 endpoint_13_59_w0 endpoint_13_59_w2
private theorem endpoint_13_59_w4 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 4 2 256507981361782333 = some 256507981361782333 := by decide +kernel
private theorem endpoint_13_59_p6 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 6 256507981361782333 = some 256507981361782333 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 4 2 256507981361782333 256507981361782333 256507981361782333 endpoint_13_59_p4 endpoint_13_59_w4
private theorem endpoint_13_59_w6 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 6 2 256507981361782333 = some 256507981361782333 := by decide +kernel
private theorem endpoint_13_59_p8 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 8 256507981361782333 = some 256507981361782333 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 6 2 256507981361782333 256507981361782333 256507981361782333 endpoint_13_59_p6 endpoint_13_59_w6
private theorem endpoint_13_59_w8 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 8 2 256507981361782333 = some 256507981361782333 := by decide +kernel
private theorem endpoint_13_59_p10 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 10 256507981361782333 = some 256507981361782333 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 8 2 256507981361782333 256507981361782333 256507981361782333 endpoint_13_59_p8 endpoint_13_59_w8
private theorem endpoint_13_59_w10 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 10 2 256507981361782333 = some 256507981361782333 := by decide +kernel
private theorem endpoint_13_59_p12 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 12 256507981361782333 = some 256507981361782333 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 10 2 256507981361782333 256507981361782333 256507981361782333 endpoint_13_59_p10 endpoint_13_59_w10
def endpoint_13_59 : CertifiedEndpoint :=
  ⟨⟨13, 59, 2841⟩, 256507981361782333, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_59_flag endpoint_13_59_sources 12 256507981361782333 256507981361782333 rfl endpoint_13_59_base endpoint_13_59_p12) (by decide)⟩
private def endpoint_13_60_flag : Flag := ⟨13, 60, 2795⟩
private def endpoint_13_60_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_60_base : receiptBase endpoint_13_60_flag endpoint_13_60_sources = some 256173727583396532 := by decide +kernel
private theorem endpoint_13_60_w0 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 2 256173727583396532 = some 256173727583396532 := by decide +kernel
private theorem endpoint_13_60_w2 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 2 2 256173727583396532 = some 256173727583396532 := by decide +kernel
private theorem endpoint_13_60_p4 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 4 256173727583396532 = some 256173727583396532 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 2 2 256173727583396532 256173727583396532 256173727583396532 endpoint_13_60_w0 endpoint_13_60_w2
private theorem endpoint_13_60_w4 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 4 2 256173727583396532 = some 256173727583396532 := by decide +kernel
private theorem endpoint_13_60_p6 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 6 256173727583396532 = some 256173727583396532 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 4 2 256173727583396532 256173727583396532 256173727583396532 endpoint_13_60_p4 endpoint_13_60_w4
private theorem endpoint_13_60_w6 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 6 2 256173727583396532 = some 256173727583396532 := by decide +kernel
private theorem endpoint_13_60_p8 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 8 256173727583396532 = some 256173727583396532 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 6 2 256173727583396532 256173727583396532 256173727583396532 endpoint_13_60_p6 endpoint_13_60_w6
private theorem endpoint_13_60_w8 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 8 2 256173727583396532 = some 256173727583396532 := by decide +kernel
private theorem endpoint_13_60_p10 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 10 256173727583396532 = some 256173727583396532 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 8 2 256173727583396532 256173727583396532 256173727583396532 endpoint_13_60_p8 endpoint_13_60_w8
private theorem endpoint_13_60_w10 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 10 2 256173727583396532 = some 256173727583396532 := by decide +kernel
private theorem endpoint_13_60_p12 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 12 256173727583396532 = some 256173727583396532 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 10 2 256173727583396532 256173727583396532 256173727583396532 endpoint_13_60_p10 endpoint_13_60_w10
def endpoint_13_60 : CertifiedEndpoint :=
  ⟨⟨13, 60, 2795⟩, 256173727583396532, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_60_flag endpoint_13_60_sources 12 256173727583396532 256173727583396532 rfl endpoint_13_60_base endpoint_13_60_p12) (by decide)⟩
private def endpoint_13_61_flag : Flag := ⟨13, 61, 2747⟩
private def endpoint_13_61_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_61_base : receiptBase endpoint_13_61_flag endpoint_13_61_sources = some 255531132728545051 := by decide +kernel
private theorem endpoint_13_61_w0 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 2 255531132728545051 = some 258260510568666240 := by decide +kernel
private theorem endpoint_13_61_w2 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 2 2 258260510568666240 = some 258260510568666240 := by decide +kernel
private theorem endpoint_13_61_p4 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 4 255531132728545051 = some 258260510568666240 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 2 2 255531132728545051 258260510568666240 258260510568666240 endpoint_13_61_w0 endpoint_13_61_w2
private theorem endpoint_13_61_w4 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 4 2 258260510568666240 = some 258260510568666240 := by decide +kernel
private theorem endpoint_13_61_p6 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 6 255531132728545051 = some 258260510568666240 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 4 2 255531132728545051 258260510568666240 258260510568666240 endpoint_13_61_p4 endpoint_13_61_w4
private theorem endpoint_13_61_w6 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 6 2 258260510568666240 = some 258260510568666240 := by decide +kernel
private theorem endpoint_13_61_p8 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 8 255531132728545051 = some 258260510568666240 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 6 2 255531132728545051 258260510568666240 258260510568666240 endpoint_13_61_p6 endpoint_13_61_w6
private theorem endpoint_13_61_w8 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 8 2 258260510568666240 = some 258260510568666240 := by decide +kernel
private theorem endpoint_13_61_p10 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 10 255531132728545051 = some 258260510568666240 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 8 2 255531132728545051 258260510568666240 258260510568666240 endpoint_13_61_p8 endpoint_13_61_w8
private theorem endpoint_13_61_w10 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 10 2 258260510568666240 = some 258260510568666240 := by decide +kernel
private theorem endpoint_13_61_p12 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 12 255531132728545051 = some 258260510568666240 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 10 2 255531132728545051 258260510568666240 258260510568666240 endpoint_13_61_p10 endpoint_13_61_w10
def endpoint_13_61 : CertifiedEndpoint :=
  ⟨⟨13, 61, 2747⟩, 258260510568666240, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_61_flag endpoint_13_61_sources 12 255531132728545051 258260510568666240 rfl endpoint_13_61_base endpoint_13_61_p12) (by decide)⟩
private def endpoint_13_62_flag : Flag := ⟨13, 62, 2698⟩
private def endpoint_13_62_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_62_base : receiptBase endpoint_13_62_flag endpoint_13_62_sources = some 254665389179954720 := by decide +kernel
private theorem endpoint_13_62_w0 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 2 254665389179954720 = some 260424411038320268 := by decide +kernel
private theorem endpoint_13_62_w2 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 2 2 260424411038320268 = some 260424411038320268 := by decide +kernel
private theorem endpoint_13_62_p4 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 4 254665389179954720 = some 260424411038320268 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 2 2 254665389179954720 260424411038320268 260424411038320268 endpoint_13_62_w0 endpoint_13_62_w2
private theorem endpoint_13_62_w4 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 4 2 260424411038320268 = some 260424411038320268 := by decide +kernel
private theorem endpoint_13_62_p6 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 6 254665389179954720 = some 260424411038320268 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 4 2 254665389179954720 260424411038320268 260424411038320268 endpoint_13_62_p4 endpoint_13_62_w4
private theorem endpoint_13_62_w6 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 6 2 260424411038320268 = some 260424411038320268 := by decide +kernel
private theorem endpoint_13_62_p8 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 8 254665389179954720 = some 260424411038320268 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 6 2 254665389179954720 260424411038320268 260424411038320268 endpoint_13_62_p6 endpoint_13_62_w6
private theorem endpoint_13_62_w8 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 8 2 260424411038320268 = some 260424411038320268 := by decide +kernel
private theorem endpoint_13_62_p10 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 10 254665389179954720 = some 260424411038320268 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 8 2 254665389179954720 260424411038320268 260424411038320268 endpoint_13_62_p8 endpoint_13_62_w8
private theorem endpoint_13_62_w10 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 10 2 260424411038320268 = some 260424411038320268 := by decide +kernel
private theorem endpoint_13_62_p12 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 12 254665389179954720 = some 260424411038320268 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 10 2 254665389179954720 260424411038320268 260424411038320268 endpoint_13_62_p10 endpoint_13_62_w10
def endpoint_13_62 : CertifiedEndpoint :=
  ⟨⟨13, 62, 2698⟩, 260424411038320268, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_62_flag endpoint_13_62_sources 12 254665389179954720 260424411038320268 rfl endpoint_13_62_base endpoint_13_62_p12) (by decide)⟩
private def endpoint_13_63_flag : Flag := ⟨13, 63, 2647⟩
private def endpoint_13_63_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_63_base : receiptBase endpoint_13_63_flag endpoint_13_63_sources = some 259342693142285452 := by decide +kernel
private theorem endpoint_13_63_w0 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 2 259342693142285452 = some 259342693142285452 := by decide +kernel
private theorem endpoint_13_63_w2 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 2 2 259342693142285452 = some 259342693142285452 := by decide +kernel
private theorem endpoint_13_63_p4 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 4 259342693142285452 = some 259342693142285452 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 2 2 259342693142285452 259342693142285452 259342693142285452 endpoint_13_63_w0 endpoint_13_63_w2
private theorem endpoint_13_63_w4 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 4 2 259342693142285452 = some 259342693142285452 := by decide +kernel
private theorem endpoint_13_63_p6 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 6 259342693142285452 = some 259342693142285452 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 4 2 259342693142285452 259342693142285452 259342693142285452 endpoint_13_63_p4 endpoint_13_63_w4
private theorem endpoint_13_63_w6 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 6 2 259342693142285452 = some 259342693142285452 := by decide +kernel
private theorem endpoint_13_63_p8 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 8 259342693142285452 = some 259342693142285452 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 6 2 259342693142285452 259342693142285452 259342693142285452 endpoint_13_63_p6 endpoint_13_63_w6
private theorem endpoint_13_63_w8 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 8 2 259342693142285452 = some 259342693142285452 := by decide +kernel
private theorem endpoint_13_63_p10 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 10 259342693142285452 = some 259342693142285452 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 8 2 259342693142285452 259342693142285452 259342693142285452 endpoint_13_63_p8 endpoint_13_63_w8
private theorem endpoint_13_63_w10 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 10 2 259342693142285452 = some 259342693142285452 := by decide +kernel
private theorem endpoint_13_63_p12 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 12 259342693142285452 = some 259342693142285452 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 10 2 259342693142285452 259342693142285452 259342693142285452 endpoint_13_63_p10 endpoint_13_63_w10
def endpoint_13_63 : CertifiedEndpoint :=
  ⟨⟨13, 63, 2647⟩, 259342693142285452, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_63_flag endpoint_13_63_sources 12 259342693142285452 259342693142285452 rfl endpoint_13_63_base endpoint_13_63_p12) (by decide)⟩
private def endpoint_13_64_flag : Flag := ⟨13, 64, 2593⟩
private def endpoint_13_64_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_64_base : receiptBase endpoint_13_64_flag endpoint_13_64_sources = some 257711189443320843 := by decide +kernel
private theorem endpoint_13_64_w0 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 2 257711189443320843 = some 257711189443320843 := by decide +kernel
private theorem endpoint_13_64_w2 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 2 2 257711189443320843 = some 257711189443320843 := by decide +kernel
private theorem endpoint_13_64_p4 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 4 257711189443320843 = some 257711189443320843 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 2 2 257711189443320843 257711189443320843 257711189443320843 endpoint_13_64_w0 endpoint_13_64_w2
private theorem endpoint_13_64_w4 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 4 2 257711189443320843 = some 257711189443320843 := by decide +kernel
private theorem endpoint_13_64_p6 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 6 257711189443320843 = some 257711189443320843 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 4 2 257711189443320843 257711189443320843 257711189443320843 endpoint_13_64_p4 endpoint_13_64_w4
private theorem endpoint_13_64_w6 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 6 2 257711189443320843 = some 257711189443320843 := by decide +kernel
private theorem endpoint_13_64_p8 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 8 257711189443320843 = some 257711189443320843 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 6 2 257711189443320843 257711189443320843 257711189443320843 endpoint_13_64_p6 endpoint_13_64_w6
private theorem endpoint_13_64_w8 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 8 2 257711189443320843 = some 257711189443320843 := by decide +kernel
private theorem endpoint_13_64_p10 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 10 257711189443320843 = some 257711189443320843 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 8 2 257711189443320843 257711189443320843 257711189443320843 endpoint_13_64_p8 endpoint_13_64_w8
private theorem endpoint_13_64_w10 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 10 2 257711189443320843 = some 257711189443320843 := by decide +kernel
private theorem endpoint_13_64_p12 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 12 257711189443320843 = some 257711189443320843 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 10 2 257711189443320843 257711189443320843 257711189443320843 endpoint_13_64_p10 endpoint_13_64_w10
def endpoint_13_64 : CertifiedEndpoint :=
  ⟨⟨13, 64, 2593⟩, 257711189443320843, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_64_flag endpoint_13_64_sources 12 257711189443320843 257711189443320843 rfl endpoint_13_64_base endpoint_13_64_p12) (by decide)⟩
private def endpoint_13_65_flag : Flag := ⟨13, 65, 2537⟩
private def endpoint_13_65_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_65_base : receiptBase endpoint_13_65_flag endpoint_13_65_sources = some 255736340236268311 := by decide +kernel
private theorem endpoint_13_65_w0 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 2 255736340236268311 = some 255736340236268311 := by decide +kernel
private theorem endpoint_13_65_w2 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 2 2 255736340236268311 = some 255736340236268311 := by decide +kernel
private theorem endpoint_13_65_p4 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 4 255736340236268311 = some 255736340236268311 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 2 2 255736340236268311 255736340236268311 255736340236268311 endpoint_13_65_w0 endpoint_13_65_w2
private theorem endpoint_13_65_w4 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 4 2 255736340236268311 = some 255736340236268311 := by decide +kernel
private theorem endpoint_13_65_p6 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 6 255736340236268311 = some 255736340236268311 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 4 2 255736340236268311 255736340236268311 255736340236268311 endpoint_13_65_p4 endpoint_13_65_w4
private theorem endpoint_13_65_w6 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 6 2 255736340236268311 = some 255736340236268311 := by decide +kernel
private theorem endpoint_13_65_p8 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 8 255736340236268311 = some 255736340236268311 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 6 2 255736340236268311 255736340236268311 255736340236268311 endpoint_13_65_p6 endpoint_13_65_w6
private theorem endpoint_13_65_w8 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 8 2 255736340236268311 = some 255736340236268311 := by decide +kernel
private theorem endpoint_13_65_p10 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 10 255736340236268311 = some 255736340236268311 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 8 2 255736340236268311 255736340236268311 255736340236268311 endpoint_13_65_p8 endpoint_13_65_w8
private theorem endpoint_13_65_w10 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 10 2 255736340236268311 = some 255736340236268311 := by decide +kernel
private theorem endpoint_13_65_p12 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 12 255736340236268311 = some 255736340236268311 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 10 2 255736340236268311 255736340236268311 255736340236268311 endpoint_13_65_p10 endpoint_13_65_w10
def endpoint_13_65 : CertifiedEndpoint :=
  ⟨⟨13, 65, 2537⟩, 255736340236268311, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_65_flag endpoint_13_65_sources 12 255736340236268311 255736340236268311 rfl endpoint_13_65_base endpoint_13_65_p12) (by decide)⟩
private def endpoint_13_66_flag : Flag := ⟨13, 66, 2480⟩
private def endpoint_13_66_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_66_base : receiptBase endpoint_13_66_flag endpoint_13_66_sources = some 253509994818342084 := by decide +kernel
private theorem endpoint_13_66_w0 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 2 253509994818342084 = some 253912986298621720 := by decide +kernel
private theorem endpoint_13_66_w2 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 2 2 253912986298621720 = some 253912986298621720 := by decide +kernel
private theorem endpoint_13_66_p4 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 4 253509994818342084 = some 253912986298621720 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 2 2 253509994818342084 253912986298621720 253912986298621720 endpoint_13_66_w0 endpoint_13_66_w2
private theorem endpoint_13_66_w4 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 4 2 253912986298621720 = some 253912986298621720 := by decide +kernel
private theorem endpoint_13_66_p6 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 6 253509994818342084 = some 253912986298621720 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 4 2 253509994818342084 253912986298621720 253912986298621720 endpoint_13_66_p4 endpoint_13_66_w4
private theorem endpoint_13_66_w6 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 6 2 253912986298621720 = some 253912986298621720 := by decide +kernel
private theorem endpoint_13_66_p8 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 8 253509994818342084 = some 253912986298621720 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 6 2 253509994818342084 253912986298621720 253912986298621720 endpoint_13_66_p6 endpoint_13_66_w6
private theorem endpoint_13_66_w8 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 8 2 253912986298621720 = some 253912986298621720 := by decide +kernel
private theorem endpoint_13_66_p10 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 10 253509994818342084 = some 253912986298621720 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 8 2 253509994818342084 253912986298621720 253912986298621720 endpoint_13_66_p8 endpoint_13_66_w8
private theorem endpoint_13_66_w10 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 10 2 253912986298621720 = some 253912986298621720 := by decide +kernel
private theorem endpoint_13_66_p12 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 12 253509994818342084 = some 253912986298621720 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 10 2 253509994818342084 253912986298621720 253912986298621720 endpoint_13_66_p10 endpoint_13_66_w10
def endpoint_13_66 : CertifiedEndpoint :=
  ⟨⟨13, 66, 2480⟩, 253912986298621720, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_66_flag endpoint_13_66_sources 12 253509994818342084 253912986298621720 rfl endpoint_13_66_base endpoint_13_66_p12) (by decide)⟩
private def endpoint_13_67_flag : Flag := ⟨13, 67, 2419⟩
private def endpoint_13_67_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_67_base : receiptBase endpoint_13_67_flag endpoint_13_67_sources = some 250724407601026983 := by decide +kernel
private theorem endpoint_13_67_w0 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 2 250724407601026983 = some 254654426217940576 := by decide +kernel
private theorem endpoint_13_67_w2 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 2 2 254654426217940576 = some 254654426217940576 := by decide +kernel
private theorem endpoint_13_67_p4 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 4 250724407601026983 = some 254654426217940576 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 2 2 250724407601026983 254654426217940576 254654426217940576 endpoint_13_67_w0 endpoint_13_67_w2
private theorem endpoint_13_67_w4 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 4 2 254654426217940576 = some 254654426217940576 := by decide +kernel
private theorem endpoint_13_67_p6 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 6 250724407601026983 = some 254654426217940576 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 4 2 250724407601026983 254654426217940576 254654426217940576 endpoint_13_67_p4 endpoint_13_67_w4
private theorem endpoint_13_67_w6 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 6 2 254654426217940576 = some 254654426217940576 := by decide +kernel
private theorem endpoint_13_67_p8 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 8 250724407601026983 = some 254654426217940576 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 6 2 250724407601026983 254654426217940576 254654426217940576 endpoint_13_67_p6 endpoint_13_67_w6
private theorem endpoint_13_67_w8 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 8 2 254654426217940576 = some 254654426217940576 := by decide +kernel
private theorem endpoint_13_67_p10 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 10 250724407601026983 = some 254654426217940576 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 8 2 250724407601026983 254654426217940576 254654426217940576 endpoint_13_67_p8 endpoint_13_67_w8
private theorem endpoint_13_67_w10 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 10 2 254654426217940576 = some 254654426217940576 := by decide +kernel
private theorem endpoint_13_67_p12 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 12 250724407601026983 = some 254654426217940576 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 10 2 250724407601026983 254654426217940576 254654426217940576 endpoint_13_67_p10 endpoint_13_67_w10
def endpoint_13_67 : CertifiedEndpoint :=
  ⟨⟨13, 67, 2419⟩, 254654426217940576, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_67_flag endpoint_13_67_sources 12 250724407601026983 254654426217940576 rfl endpoint_13_67_base endpoint_13_67_p12) (by decide)⟩
private def endpoint_13_68_flag : Flag := ⟨13, 68, 2357⟩
private def endpoint_13_68_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_68_base : receiptBase endpoint_13_68_flag endpoint_13_68_sources = some 247671225324401938 := by decide +kernel
private theorem endpoint_13_68_w0 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 2 247671225324401938 = some 255215962566984376 := by decide +kernel
private theorem endpoint_13_68_w2 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 2 2 255215962566984376 = some 255215962566984376 := by decide +kernel
private theorem endpoint_13_68_p4 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 4 247671225324401938 = some 255215962566984376 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 2 2 247671225324401938 255215962566984376 255215962566984376 endpoint_13_68_w0 endpoint_13_68_w2
private theorem endpoint_13_68_w4 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 4 2 255215962566984376 = some 255215962566984376 := by decide +kernel
private theorem endpoint_13_68_p6 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 6 247671225324401938 = some 255215962566984376 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 4 2 247671225324401938 255215962566984376 255215962566984376 endpoint_13_68_p4 endpoint_13_68_w4
private theorem endpoint_13_68_w6 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 6 2 255215962566984376 = some 255215962566984376 := by decide +kernel
private theorem endpoint_13_68_p8 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 8 247671225324401938 = some 255215962566984376 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 6 2 247671225324401938 255215962566984376 255215962566984376 endpoint_13_68_p6 endpoint_13_68_w6
private theorem endpoint_13_68_w8 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 8 2 255215962566984376 = some 255215962566984376 := by decide +kernel
private theorem endpoint_13_68_p10 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 10 247671225324401938 = some 255215962566984376 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 8 2 247671225324401938 255215962566984376 255215962566984376 endpoint_13_68_p8 endpoint_13_68_w8
private theorem endpoint_13_68_w10 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 10 2 255215962566984376 = some 255215962566984376 := by decide +kernel
private theorem endpoint_13_68_p12 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 12 247671225324401938 = some 255215962566984376 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 10 2 247671225324401938 255215962566984376 255215962566984376 endpoint_13_68_p10 endpoint_13_68_w10
def endpoint_13_68 : CertifiedEndpoint :=
  ⟨⟨13, 68, 2357⟩, 255215962566984376, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_68_flag endpoint_13_68_sources 12 247671225324401938 255215962566984376 rfl endpoint_13_68_base endpoint_13_68_p12) (by decide)⟩
private def endpoint_13_69_flag : Flag := ⟨13, 69, 2292⟩
private def endpoint_13_69_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_13_69_base : receiptBase endpoint_13_69_flag endpoint_13_69_sources = some 245528023713462454 := by decide +kernel
private theorem endpoint_13_69_w0 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 2 245528023713462454 = some 245528023713462454 := by decide +kernel
private theorem endpoint_13_69_w2 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 2 2 245528023713462454 = some 245528023713462454 := by decide +kernel
private theorem endpoint_13_69_p4 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 4 245528023713462454 = some 245528023713462454 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 2 2 245528023713462454 245528023713462454 245528023713462454 endpoint_13_69_w0 endpoint_13_69_w2
private theorem endpoint_13_69_w4 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 4 2 245528023713462454 = some 245528023713462454 := by decide +kernel
private theorem endpoint_13_69_p6 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 6 245528023713462454 = some 245528023713462454 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 4 2 245528023713462454 245528023713462454 245528023713462454 endpoint_13_69_p4 endpoint_13_69_w4
private theorem endpoint_13_69_w6 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 6 2 245528023713462454 = some 245528023713462454 := by decide +kernel
private theorem endpoint_13_69_p8 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 8 245528023713462454 = some 245528023713462454 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 6 2 245528023713462454 245528023713462454 245528023713462454 endpoint_13_69_p6 endpoint_13_69_w6
private theorem endpoint_13_69_w8 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 8 2 245528023713462454 = some 245528023713462454 := by decide +kernel
private theorem endpoint_13_69_p10 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 10 245528023713462454 = some 245528023713462454 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 8 2 245528023713462454 245528023713462454 245528023713462454 endpoint_13_69_p8 endpoint_13_69_w8
private theorem endpoint_13_69_w10 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 10 2 245528023713462454 = some 245528023713462454 := by decide +kernel
private theorem endpoint_13_69_p12 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 12 245528023713462454 = some 245528023713462454 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 10 2 245528023713462454 245528023713462454 245528023713462454 endpoint_13_69_p10 endpoint_13_69_w10
def endpoint_13_69 : CertifiedEndpoint :=
  ⟨⟨13, 69, 2292⟩, 245528023713462454, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_13_69_flag endpoint_13_69_sources 12 245528023713462454 245528023713462454 rfl endpoint_13_69_base endpoint_13_69_p12) (by decide)⟩
private def endpoint_13_70_flag : Flag := ⟨13, 70, 2225⟩
private def endpoint_13_70_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_13_70_base : receiptBase endpoint_13_70_flag endpoint_13_70_sources = some 241699298391534920 := by decide +kernel
private theorem endpoint_13_70_w0 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 2 241699298391534920 = some 242542791108428514 := by decide +kernel
private theorem endpoint_13_70_w2 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 2 2 242542791108428514 = some 242542791108428514 := by decide +kernel
private theorem endpoint_13_70_p4 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 4 241699298391534920 = some 242542791108428514 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 2 2 241699298391534920 242542791108428514 242542791108428514 endpoint_13_70_w0 endpoint_13_70_w2
private theorem endpoint_13_70_w4 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 4 2 242542791108428514 = some 242542791108428514 := by decide +kernel
private theorem endpoint_13_70_p6 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 6 241699298391534920 = some 242542791108428514 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 4 2 241699298391534920 242542791108428514 242542791108428514 endpoint_13_70_p4 endpoint_13_70_w4
private theorem endpoint_13_70_w6 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 6 2 242542791108428514 = some 242542791108428514 := by decide +kernel
private theorem endpoint_13_70_p8 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 8 241699298391534920 = some 242542791108428514 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 6 2 241699298391534920 242542791108428514 242542791108428514 endpoint_13_70_p6 endpoint_13_70_w6
private theorem endpoint_13_70_w8 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 8 2 242542791108428514 = some 242542791108428514 := by decide +kernel
private theorem endpoint_13_70_p10 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 10 241699298391534920 = some 242542791108428514 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 8 2 241699298391534920 242542791108428514 242542791108428514 endpoint_13_70_p8 endpoint_13_70_w8
private theorem endpoint_13_70_w10 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 10 2 242542791108428514 = some 242542791108428514 := by decide +kernel
private theorem endpoint_13_70_p12 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 12 241699298391534920 = some 242542791108428514 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 10 2 241699298391534920 242542791108428514 242542791108428514 endpoint_13_70_p10 endpoint_13_70_w10
def endpoint_13_70 : CertifiedEndpoint :=
  ⟨⟨13, 70, 2225⟩, 242542791108428514, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_13_70_flag endpoint_13_70_sources 12 241699298391534920 242542791108428514 rfl endpoint_13_70_base endpoint_13_70_p12) (by decide)⟩
private def endpoint_13_71_flag : Flag := ⟨13, 71, 2155⟩
private def endpoint_13_71_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_13_71_base : receiptBase endpoint_13_71_flag endpoint_13_71_sources = some 238779251725233353 := by decide +kernel
private theorem endpoint_13_71_w0 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 2 238779251725233353 = some 238779251725233353 := by decide +kernel
private theorem endpoint_13_71_w2 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 2 2 238779251725233353 = some 238779251725233353 := by decide +kernel
private theorem endpoint_13_71_p4 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 4 238779251725233353 = some 238779251725233353 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 2 2 238779251725233353 238779251725233353 238779251725233353 endpoint_13_71_w0 endpoint_13_71_w2
private theorem endpoint_13_71_w4 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 4 2 238779251725233353 = some 238779251725233353 := by decide +kernel
private theorem endpoint_13_71_p6 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 6 238779251725233353 = some 238779251725233353 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 4 2 238779251725233353 238779251725233353 238779251725233353 endpoint_13_71_p4 endpoint_13_71_w4
private theorem endpoint_13_71_w6 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 6 2 238779251725233353 = some 238779251725233353 := by decide +kernel
private theorem endpoint_13_71_p8 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 8 238779251725233353 = some 238779251725233353 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 6 2 238779251725233353 238779251725233353 238779251725233353 endpoint_13_71_p6 endpoint_13_71_w6
private theorem endpoint_13_71_w8 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 8 2 238779251725233353 = some 238779251725233353 := by decide +kernel
private theorem endpoint_13_71_p10 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 10 238779251725233353 = some 238779251725233353 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 8 2 238779251725233353 238779251725233353 238779251725233353 endpoint_13_71_p8 endpoint_13_71_w8
private theorem endpoint_13_71_w10 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 10 2 238779251725233353 = some 238779251725233353 := by decide +kernel
private theorem endpoint_13_71_p12 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 12 238779251725233353 = some 238779251725233353 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 10 2 238779251725233353 238779251725233353 238779251725233353 endpoint_13_71_p10 endpoint_13_71_w10
def endpoint_13_71 : CertifiedEndpoint :=
  ⟨⟨13, 71, 2155⟩, 238779251725233353, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_13_71_flag endpoint_13_71_sources 12 238779251725233353 238779251725233353 rfl endpoint_13_71_base endpoint_13_71_p12) (by decide)⟩
private def endpoint_13_72_flag : Flag := ⟨13, 72, 2083⟩
private def endpoint_13_72_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_13_72_base : receiptBase endpoint_13_72_flag endpoint_13_72_sources = some 233790678869093283 := by decide +kernel
private theorem endpoint_13_72_w0 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 2 233790678869093283 = some 234638990416615896 := by decide +kernel
private theorem endpoint_13_72_w2 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 2 2 234638990416615896 = some 234638990416615896 := by decide +kernel
private theorem endpoint_13_72_p4 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 4 233790678869093283 = some 234638990416615896 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 2 2 233790678869093283 234638990416615896 234638990416615896 endpoint_13_72_w0 endpoint_13_72_w2
private theorem endpoint_13_72_w4 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 4 2 234638990416615896 = some 234638990416615896 := by decide +kernel
private theorem endpoint_13_72_p6 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 6 233790678869093283 = some 234638990416615896 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 4 2 233790678869093283 234638990416615896 234638990416615896 endpoint_13_72_p4 endpoint_13_72_w4
private theorem endpoint_13_72_w6 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 6 2 234638990416615896 = some 234638990416615896 := by decide +kernel
private theorem endpoint_13_72_p8 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 8 233790678869093283 = some 234638990416615896 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 6 2 233790678869093283 234638990416615896 234638990416615896 endpoint_13_72_p6 endpoint_13_72_w6
private theorem endpoint_13_72_w8 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 8 2 234638990416615896 = some 234638990416615896 := by decide +kernel
private theorem endpoint_13_72_p10 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 10 233790678869093283 = some 234638990416615896 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 8 2 233790678869093283 234638990416615896 234638990416615896 endpoint_13_72_p8 endpoint_13_72_w8
private theorem endpoint_13_72_w10 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 10 2 234638990416615896 = some 234638990416615896 := by decide +kernel
private theorem endpoint_13_72_p12 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 12 233790678869093283 = some 234638990416615896 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 10 2 233790678869093283 234638990416615896 234638990416615896 endpoint_13_72_p10 endpoint_13_72_w10
def endpoint_13_72 : CertifiedEndpoint :=
  ⟨⟨13, 72, 2083⟩, 234638990416615896, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_13_72_flag endpoint_13_72_sources 12 233790678869093283 234638990416615896 rfl endpoint_13_72_base endpoint_13_72_p12) (by decide)⟩
private def endpoint_13_73_flag : Flag := ⟨13, 73, 2009⟩
private def endpoint_13_73_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_13_73_base : receiptBase endpoint_13_73_flag endpoint_13_73_sources = some 230122284720605504 := by decide +kernel
private theorem endpoint_13_73_w0 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 2 230122284720605504 = some 230122284720605504 := by decide +kernel
private theorem endpoint_13_73_w2 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 2 2 230122284720605504 = some 230122284720605504 := by decide +kernel
private theorem endpoint_13_73_p4 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 4 230122284720605504 = some 230122284720605504 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 2 2 230122284720605504 230122284720605504 230122284720605504 endpoint_13_73_w0 endpoint_13_73_w2
private theorem endpoint_13_73_w4 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 4 2 230122284720605504 = some 230122284720605504 := by decide +kernel
private theorem endpoint_13_73_p6 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 6 230122284720605504 = some 230122284720605504 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 4 2 230122284720605504 230122284720605504 230122284720605504 endpoint_13_73_p4 endpoint_13_73_w4
private theorem endpoint_13_73_w6 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 6 2 230122284720605504 = some 230122284720605504 := by decide +kernel
private theorem endpoint_13_73_p8 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 8 230122284720605504 = some 230122284720605504 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 6 2 230122284720605504 230122284720605504 230122284720605504 endpoint_13_73_p6 endpoint_13_73_w6
private theorem endpoint_13_73_w8 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 8 2 230122284720605504 = some 230122284720605504 := by decide +kernel
private theorem endpoint_13_73_p10 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 10 230122284720605504 = some 230122284720605504 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 8 2 230122284720605504 230122284720605504 230122284720605504 endpoint_13_73_p8 endpoint_13_73_w8
private theorem endpoint_13_73_w10 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 10 2 230122284720605504 = some 230122284720605504 := by decide +kernel
private theorem endpoint_13_73_p12 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 12 230122284720605504 = some 230122284720605504 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 10 2 230122284720605504 230122284720605504 230122284720605504 endpoint_13_73_p10 endpoint_13_73_w10
def endpoint_13_73 : CertifiedEndpoint :=
  ⟨⟨13, 73, 2009⟩, 230122284720605504, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_13_73_flag endpoint_13_73_sources 12 230122284720605504 230122284720605504 rfl endpoint_13_73_base endpoint_13_73_p12) (by decide)⟩
private def endpoint_13_74_flag : Flag := ⟨13, 74, 1932⟩
private def endpoint_13_74_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_13_74_base : receiptBase endpoint_13_74_flag endpoint_13_74_sources = some 224087312464710803 := by decide +kernel
private theorem endpoint_13_74_w0 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 2 224087312464710803 = some 224087312464710803 := by decide +kernel
private theorem endpoint_13_74_w2 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 2 2 224087312464710803 = some 224087312464710803 := by decide +kernel
private theorem endpoint_13_74_p4 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 4 224087312464710803 = some 224087312464710803 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 2 2 224087312464710803 224087312464710803 224087312464710803 endpoint_13_74_w0 endpoint_13_74_w2
private theorem endpoint_13_74_w4 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 4 2 224087312464710803 = some 224087312464710803 := by decide +kernel
private theorem endpoint_13_74_p6 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 6 224087312464710803 = some 224087312464710803 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 4 2 224087312464710803 224087312464710803 224087312464710803 endpoint_13_74_p4 endpoint_13_74_w4
private theorem endpoint_13_74_w6 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 6 2 224087312464710803 = some 224087312464710803 := by decide +kernel
private theorem endpoint_13_74_p8 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 8 224087312464710803 = some 224087312464710803 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 6 2 224087312464710803 224087312464710803 224087312464710803 endpoint_13_74_p6 endpoint_13_74_w6
private theorem endpoint_13_74_w8 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 8 2 224087312464710803 = some 224087312464710803 := by decide +kernel
private theorem endpoint_13_74_p10 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 10 224087312464710803 = some 224087312464710803 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 8 2 224087312464710803 224087312464710803 224087312464710803 endpoint_13_74_p8 endpoint_13_74_w8
private theorem endpoint_13_74_w10 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 10 2 224087312464710803 = some 224087312464710803 := by decide +kernel
private theorem endpoint_13_74_p12 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 12 224087312464710803 = some 224087312464710803 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 10 2 224087312464710803 224087312464710803 224087312464710803 endpoint_13_74_p10 endpoint_13_74_w10
def endpoint_13_74 : CertifiedEndpoint :=
  ⟨⟨13, 74, 1932⟩, 224087312464710803, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_13_74_flag endpoint_13_74_sources 12 224087312464710803 224087312464710803 rfl endpoint_13_74_base endpoint_13_74_p12) (by decide)⟩
private def endpoint_13_75_flag : Flag := ⟨13, 75, 1853⟩
private def endpoint_13_75_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_13_75_base : receiptBase endpoint_13_75_flag endpoint_13_75_sources = some 217605099590368241 := by decide +kernel
private theorem endpoint_13_75_w0 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 2 217605099590368241 = some 217605099590368241 := by decide +kernel
private theorem endpoint_13_75_w2 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 2 2 217605099590368241 = some 217605099590368241 := by decide +kernel
private theorem endpoint_13_75_p4 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 4 217605099590368241 = some 217605099590368241 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 2 2 217605099590368241 217605099590368241 217605099590368241 endpoint_13_75_w0 endpoint_13_75_w2
private theorem endpoint_13_75_w4 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 4 2 217605099590368241 = some 217605099590368241 := by decide +kernel
private theorem endpoint_13_75_p6 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 6 217605099590368241 = some 217605099590368241 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 4 2 217605099590368241 217605099590368241 217605099590368241 endpoint_13_75_p4 endpoint_13_75_w4
private theorem endpoint_13_75_w6 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 6 2 217605099590368241 = some 217605099590368241 := by decide +kernel
private theorem endpoint_13_75_p8 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 8 217605099590368241 = some 217605099590368241 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 6 2 217605099590368241 217605099590368241 217605099590368241 endpoint_13_75_p6 endpoint_13_75_w6
private theorem endpoint_13_75_w8 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 8 2 217605099590368241 = some 217605099590368241 := by decide +kernel
private theorem endpoint_13_75_p10 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 10 217605099590368241 = some 217605099590368241 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 8 2 217605099590368241 217605099590368241 217605099590368241 endpoint_13_75_p8 endpoint_13_75_w8
private theorem endpoint_13_75_w10 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 10 2 217605099590368241 = some 217605099590368241 := by decide +kernel
private theorem endpoint_13_75_p12 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 12 217605099590368241 = some 217605099590368241 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 10 2 217605099590368241 217605099590368241 217605099590368241 endpoint_13_75_p10 endpoint_13_75_w10
def endpoint_13_75 : CertifiedEndpoint :=
  ⟨⟨13, 75, 1853⟩, 217605099590368241, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_13_75_flag endpoint_13_75_sources 12 217605099590368241 217605099590368241 rfl endpoint_13_75_base endpoint_13_75_p12) (by decide)⟩
private def endpoint_13_76_flag : Flag := ⟨13, 76, 1771⟩
private def endpoint_13_76_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_13_76_base : receiptBase endpoint_13_76_flag endpoint_13_76_sources = some 213969411212426625 := by decide +kernel
private theorem endpoint_13_76_w0 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 2 213969411212426625 = some 213969411212426625 := by decide +kernel
private theorem endpoint_13_76_w2 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 2 2 213969411212426625 = some 213969411212426625 := by decide +kernel
private theorem endpoint_13_76_p4 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 4 213969411212426625 = some 213969411212426625 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 2 2 213969411212426625 213969411212426625 213969411212426625 endpoint_13_76_w0 endpoint_13_76_w2
private theorem endpoint_13_76_w4 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 4 2 213969411212426625 = some 213969411212426625 := by decide +kernel
private theorem endpoint_13_76_p6 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 6 213969411212426625 = some 213969411212426625 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 4 2 213969411212426625 213969411212426625 213969411212426625 endpoint_13_76_p4 endpoint_13_76_w4
private theorem endpoint_13_76_w6 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 6 2 213969411212426625 = some 213969411212426625 := by decide +kernel
private theorem endpoint_13_76_p8 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 8 213969411212426625 = some 213969411212426625 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 6 2 213969411212426625 213969411212426625 213969411212426625 endpoint_13_76_p6 endpoint_13_76_w6
private theorem endpoint_13_76_w8 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 8 2 213969411212426625 = some 213969411212426625 := by decide +kernel
private theorem endpoint_13_76_p10 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 10 213969411212426625 = some 213969411212426625 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 8 2 213969411212426625 213969411212426625 213969411212426625 endpoint_13_76_p8 endpoint_13_76_w8
private theorem endpoint_13_76_w10 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 10 2 213969411212426625 = some 213969411212426625 := by decide +kernel
private theorem endpoint_13_76_p12 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 12 213969411212426625 = some 213969411212426625 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 10 2 213969411212426625 213969411212426625 213969411212426625 endpoint_13_76_p10 endpoint_13_76_w10
def endpoint_13_76 : CertifiedEndpoint :=
  ⟨⟨13, 76, 1771⟩, 213969411212426625, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_13_76_flag endpoint_13_76_sources 12 213969411212426625 213969411212426625 rfl endpoint_13_76_base endpoint_13_76_p12) (by decide)⟩
private def endpoint_13_77_flag : Flag := ⟨13, 77, 1686⟩
private def endpoint_13_77_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_13_77_base : receiptBase endpoint_13_77_flag endpoint_13_77_sources = some 206154046385600463 := by decide +kernel
private theorem endpoint_13_77_w0 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 2 206154046385600463 = some 206154046385600463 := by decide +kernel
private theorem endpoint_13_77_w2 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 2 2 206154046385600463 = some 206154046385600463 := by decide +kernel
private theorem endpoint_13_77_p4 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 4 206154046385600463 = some 206154046385600463 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 2 2 206154046385600463 206154046385600463 206154046385600463 endpoint_13_77_w0 endpoint_13_77_w2
private theorem endpoint_13_77_w4 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 4 2 206154046385600463 = some 206154046385600463 := by decide +kernel
private theorem endpoint_13_77_p6 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 6 206154046385600463 = some 206154046385600463 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 4 2 206154046385600463 206154046385600463 206154046385600463 endpoint_13_77_p4 endpoint_13_77_w4
private theorem endpoint_13_77_w6 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 6 2 206154046385600463 = some 206154046385600463 := by decide +kernel
private theorem endpoint_13_77_p8 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 8 206154046385600463 = some 206154046385600463 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 6 2 206154046385600463 206154046385600463 206154046385600463 endpoint_13_77_p6 endpoint_13_77_w6
private theorem endpoint_13_77_w8 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 8 2 206154046385600463 = some 206154046385600463 := by decide +kernel
private theorem endpoint_13_77_p10 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 10 206154046385600463 = some 206154046385600463 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 8 2 206154046385600463 206154046385600463 206154046385600463 endpoint_13_77_p8 endpoint_13_77_w8
private theorem endpoint_13_77_w10 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 10 2 206154046385600463 = some 206154046385600463 := by decide +kernel
private theorem endpoint_13_77_p12 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 12 206154046385600463 = some 206154046385600463 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 10 2 206154046385600463 206154046385600463 206154046385600463 endpoint_13_77_p10 endpoint_13_77_w10
def endpoint_13_77 : CertifiedEndpoint :=
  ⟨⟨13, 77, 1686⟩, 206154046385600463, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_13_77_flag endpoint_13_77_sources 12 206154046385600463 206154046385600463 rfl endpoint_13_77_base endpoint_13_77_p12) (by decide)⟩
private def endpoint_13_78_flag : Flag := ⟨13, 78, 1599⟩
private def endpoint_13_78_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_13_78_base : receiptBase endpoint_13_78_flag endpoint_13_78_sources = some 198171569588310355 := by decide +kernel
private theorem endpoint_13_78_w0 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 2 198171569588310355 = some 198171569588310355 := by decide +kernel
private theorem endpoint_13_78_w2 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 2 2 198171569588310355 = some 198171569588310355 := by decide +kernel
private theorem endpoint_13_78_p4 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 4 198171569588310355 = some 198171569588310355 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 2 2 198171569588310355 198171569588310355 198171569588310355 endpoint_13_78_w0 endpoint_13_78_w2
private theorem endpoint_13_78_w4 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 4 2 198171569588310355 = some 198171569588310355 := by decide +kernel
private theorem endpoint_13_78_p6 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 6 198171569588310355 = some 198171569588310355 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 4 2 198171569588310355 198171569588310355 198171569588310355 endpoint_13_78_p4 endpoint_13_78_w4
private theorem endpoint_13_78_w6 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 6 2 198171569588310355 = some 198171569588310355 := by decide +kernel
private theorem endpoint_13_78_p8 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 8 198171569588310355 = some 198171569588310355 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 6 2 198171569588310355 198171569588310355 198171569588310355 endpoint_13_78_p6 endpoint_13_78_w6
private theorem endpoint_13_78_w8 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 8 2 198171569588310355 = some 198171569588310355 := by decide +kernel
private theorem endpoint_13_78_p10 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 10 198171569588310355 = some 198171569588310355 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 8 2 198171569588310355 198171569588310355 198171569588310355 endpoint_13_78_p8 endpoint_13_78_w8
private theorem endpoint_13_78_w10 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 10 2 198171569588310355 = some 198171569588310355 := by decide +kernel
private theorem endpoint_13_78_p12 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 12 198171569588310355 = some 198171569588310355 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 10 2 198171569588310355 198171569588310355 198171569588310355 endpoint_13_78_p10 endpoint_13_78_w10
def endpoint_13_78 : CertifiedEndpoint :=
  ⟨⟨13, 78, 1599⟩, 198171569588310355, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_13_78_flag endpoint_13_78_sources 12 198171569588310355 198171569588310355 rfl endpoint_13_78_base endpoint_13_78_p12) (by decide)⟩
private def endpoint_13_79_flag : Flag := ⟨13, 79, 1510⟩
private def endpoint_13_79_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_13_79_base : receiptBase endpoint_13_79_flag endpoint_13_79_sources = some 190502764381496209 := by decide +kernel
private theorem endpoint_13_79_w0 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 2 190502764381496209 = some 190502764381496209 := by decide +kernel
private theorem endpoint_13_79_w2 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 2 2 190502764381496209 = some 190502764381496209 := by decide +kernel
private theorem endpoint_13_79_p4 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 4 190502764381496209 = some 190502764381496209 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 2 2 190502764381496209 190502764381496209 190502764381496209 endpoint_13_79_w0 endpoint_13_79_w2
private theorem endpoint_13_79_w4 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 4 2 190502764381496209 = some 190502764381496209 := by decide +kernel
private theorem endpoint_13_79_p6 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 6 190502764381496209 = some 190502764381496209 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 4 2 190502764381496209 190502764381496209 190502764381496209 endpoint_13_79_p4 endpoint_13_79_w4
private theorem endpoint_13_79_w6 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 6 2 190502764381496209 = some 190502764381496209 := by decide +kernel
private theorem endpoint_13_79_p8 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 8 190502764381496209 = some 190502764381496209 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 6 2 190502764381496209 190502764381496209 190502764381496209 endpoint_13_79_p6 endpoint_13_79_w6
private theorem endpoint_13_79_w8 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 8 2 190502764381496209 = some 190502764381496209 := by decide +kernel
private theorem endpoint_13_79_p10 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 10 190502764381496209 = some 190502764381496209 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 8 2 190502764381496209 190502764381496209 190502764381496209 endpoint_13_79_p8 endpoint_13_79_w8
private theorem endpoint_13_79_w10 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 10 2 190502764381496209 = some 190502764381496209 := by decide +kernel
private theorem endpoint_13_79_p12 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 12 190502764381496209 = some 190502764381496209 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 10 2 190502764381496209 190502764381496209 190502764381496209 endpoint_13_79_p10 endpoint_13_79_w10
def endpoint_13_79 : CertifiedEndpoint :=
  ⟨⟨13, 79, 1510⟩, 190502764381496209, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_13_79_flag endpoint_13_79_sources 12 190502764381496209 190502764381496209 rfl endpoint_13_79_base endpoint_13_79_p12) (by decide)⟩
private def endpoint_13_80_flag : Flag := ⟨13, 80, 1418⟩
private def endpoint_13_80_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_13_80_base : receiptBase endpoint_13_80_flag endpoint_13_80_sources = some 181030772008731269 := by decide +kernel
private theorem endpoint_13_80_w0 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 2 181030772008731269 = some 181030772008731269 := by decide +kernel
private theorem endpoint_13_80_w2 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 2 2 181030772008731269 = some 181030772008731269 := by decide +kernel
private theorem endpoint_13_80_p4 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 4 181030772008731269 = some 181030772008731269 :=
  join_receipt_window endpoint_13_80_flag endpoint_13_80_sources 0 2 2 181030772008731269 181030772008731269 181030772008731269 endpoint_13_80_w0 endpoint_13_80_w2
private theorem endpoint_13_80_w4 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 4 2 181030772008731269 = some 181030772008731269 := by decide +kernel
private theorem endpoint_13_80_p6 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 6 181030772008731269 = some 181030772008731269 :=
  join_receipt_window endpoint_13_80_flag endpoint_13_80_sources 0 4 2 181030772008731269 181030772008731269 181030772008731269 endpoint_13_80_p4 endpoint_13_80_w4
private theorem endpoint_13_80_w6 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 6 2 181030772008731269 = some 181030772008731269 := by decide +kernel
private theorem endpoint_13_80_p8 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 8 181030772008731269 = some 181030772008731269 :=
  join_receipt_window endpoint_13_80_flag endpoint_13_80_sources 0 6 2 181030772008731269 181030772008731269 181030772008731269 endpoint_13_80_p6 endpoint_13_80_w6
private theorem endpoint_13_80_w8 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 8 2 181030772008731269 = some 181030772008731269 := by decide +kernel
private theorem endpoint_13_80_p10 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 10 181030772008731269 = some 181030772008731269 :=
  join_receipt_window endpoint_13_80_flag endpoint_13_80_sources 0 8 2 181030772008731269 181030772008731269 181030772008731269 endpoint_13_80_p8 endpoint_13_80_w8
private theorem endpoint_13_80_w10 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 10 2 181030772008731269 = some 181030772008731269 := by decide +kernel
private theorem endpoint_13_80_p12 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 12 181030772008731269 = some 181030772008731269 :=
  join_receipt_window endpoint_13_80_flag endpoint_13_80_sources 0 10 2 181030772008731269 181030772008731269 181030772008731269 endpoint_13_80_p10 endpoint_13_80_w10
def endpoint_13_80 : CertifiedEndpoint :=
  ⟨⟨13, 80, 1418⟩, 181030772008731269, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_13_80_flag endpoint_13_80_sources 12 181030772008731269 181030772008731269 rfl endpoint_13_80_base endpoint_13_80_p12) (by decide)⟩
private def endpoint_13_81_flag : Flag := ⟨13, 81, 1323⟩
private def endpoint_13_81_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_13_81_base : receiptBase endpoint_13_81_flag endpoint_13_81_sources = some 170913515076338091 := by decide +kernel
private theorem endpoint_13_81_w0 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 2 170913515076338091 = some 170913515076338091 := by decide +kernel
private theorem endpoint_13_81_w2 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 2 2 170913515076338091 = some 170913515076338091 := by decide +kernel
private theorem endpoint_13_81_p4 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 4 170913515076338091 = some 170913515076338091 :=
  join_receipt_window endpoint_13_81_flag endpoint_13_81_sources 0 2 2 170913515076338091 170913515076338091 170913515076338091 endpoint_13_81_w0 endpoint_13_81_w2
private theorem endpoint_13_81_w4 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 4 2 170913515076338091 = some 170913515076338091 := by decide +kernel
private theorem endpoint_13_81_p6 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 6 170913515076338091 = some 170913515076338091 :=
  join_receipt_window endpoint_13_81_flag endpoint_13_81_sources 0 4 2 170913515076338091 170913515076338091 170913515076338091 endpoint_13_81_p4 endpoint_13_81_w4
private theorem endpoint_13_81_w6 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 6 2 170913515076338091 = some 170913515076338091 := by decide +kernel
private theorem endpoint_13_81_p8 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 8 170913515076338091 = some 170913515076338091 :=
  join_receipt_window endpoint_13_81_flag endpoint_13_81_sources 0 6 2 170913515076338091 170913515076338091 170913515076338091 endpoint_13_81_p6 endpoint_13_81_w6
private theorem endpoint_13_81_w8 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 8 2 170913515076338091 = some 170913515076338091 := by decide +kernel
private theorem endpoint_13_81_p10 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 10 170913515076338091 = some 170913515076338091 :=
  join_receipt_window endpoint_13_81_flag endpoint_13_81_sources 0 8 2 170913515076338091 170913515076338091 170913515076338091 endpoint_13_81_p8 endpoint_13_81_w8
private theorem endpoint_13_81_w10 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 10 2 170913515076338091 = some 170913515076338091 := by decide +kernel
private theorem endpoint_13_81_p12 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 12 170913515076338091 = some 170913515076338091 :=
  join_receipt_window endpoint_13_81_flag endpoint_13_81_sources 0 10 2 170913515076338091 170913515076338091 170913515076338091 endpoint_13_81_p10 endpoint_13_81_w10
def endpoint_13_81 : CertifiedEndpoint :=
  ⟨⟨13, 81, 1323⟩, 170913515076338091, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_13_81_flag endpoint_13_81_sources 12 170913515076338091 170913515076338091 rfl endpoint_13_81_base endpoint_13_81_p12) (by decide)⟩
private def endpoint_13_82_flag : Flag := ⟨13, 82, 1226⟩
private def endpoint_13_82_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_13_82_base : receiptBase endpoint_13_82_flag endpoint_13_82_sources = some 160267133613814256 := by decide +kernel
private theorem endpoint_13_82_w0 : receiptWindow endpoint_13_82_flag endpoint_13_82_sources 0 2 160267133613814256 = some 163512499321618276 := by decide +kernel
private theorem endpoint_13_82_w2 : receiptWindow endpoint_13_82_flag endpoint_13_82_sources 2 2 163512499321618276 = some 163512499321618276 := by decide +kernel
private theorem endpoint_13_82_p4 : receiptWindow endpoint_13_82_flag endpoint_13_82_sources 0 4 160267133613814256 = some 163512499321618276 :=
  join_receipt_window endpoint_13_82_flag endpoint_13_82_sources 0 2 2 160267133613814256 163512499321618276 163512499321618276 endpoint_13_82_w0 endpoint_13_82_w2
private theorem endpoint_13_82_w4 : receiptWindow endpoint_13_82_flag endpoint_13_82_sources 4 2 163512499321618276 = some 163512499321618276 := by decide +kernel
private theorem endpoint_13_82_p6 : receiptWindow endpoint_13_82_flag endpoint_13_82_sources 0 6 160267133613814256 = some 163512499321618276 :=
  join_receipt_window endpoint_13_82_flag endpoint_13_82_sources 0 4 2 160267133613814256 163512499321618276 163512499321618276 endpoint_13_82_p4 endpoint_13_82_w4
private theorem endpoint_13_82_w6 : receiptWindow endpoint_13_82_flag endpoint_13_82_sources 6 2 163512499321618276 = some 163512499321618276 := by decide +kernel
private theorem endpoint_13_82_p8 : receiptWindow endpoint_13_82_flag endpoint_13_82_sources 0 8 160267133613814256 = some 163512499321618276 :=
  join_receipt_window endpoint_13_82_flag endpoint_13_82_sources 0 6 2 160267133613814256 163512499321618276 163512499321618276 endpoint_13_82_p6 endpoint_13_82_w6
private theorem endpoint_13_82_w8 : receiptWindow endpoint_13_82_flag endpoint_13_82_sources 8 2 163512499321618276 = some 163512499321618276 := by decide +kernel
private theorem endpoint_13_82_p10 : receiptWindow endpoint_13_82_flag endpoint_13_82_sources 0 10 160267133613814256 = some 163512499321618276 :=
  join_receipt_window endpoint_13_82_flag endpoint_13_82_sources 0 8 2 160267133613814256 163512499321618276 163512499321618276 endpoint_13_82_p8 endpoint_13_82_w8
private theorem endpoint_13_82_w10 : receiptWindow endpoint_13_82_flag endpoint_13_82_sources 10 2 163512499321618276 = some 163512499321618276 := by decide +kernel
private theorem endpoint_13_82_p12 : receiptWindow endpoint_13_82_flag endpoint_13_82_sources 0 12 160267133613814256 = some 163512499321618276 :=
  join_receipt_window endpoint_13_82_flag endpoint_13_82_sources 0 10 2 160267133613814256 163512499321618276 163512499321618276 endpoint_13_82_p10 endpoint_13_82_w10
def endpoint_13_82 : CertifiedEndpoint :=
  ⟨⟨13, 82, 1226⟩, 163512499321618276, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_13_82_flag endpoint_13_82_sources 12 160267133613814256 163512499321618276 rfl endpoint_13_82_base endpoint_13_82_p12) (by decide)⟩
private def endpoint_13_83_flag : Flag := ⟨13, 83, 1126⟩
private def endpoint_13_83_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_13_83_base : receiptBase endpoint_13_83_flag endpoint_13_83_sources = some 148952762656072862 := by decide +kernel
private theorem endpoint_13_83_w0 : receiptWindow endpoint_13_83_flag endpoint_13_83_sources 0 2 148952762656072862 = some 158287425574624607 := by decide +kernel
private theorem endpoint_13_83_w2 : receiptWindow endpoint_13_83_flag endpoint_13_83_sources 2 2 158287425574624607 = some 158287425574624607 := by decide +kernel
private theorem endpoint_13_83_p4 : receiptWindow endpoint_13_83_flag endpoint_13_83_sources 0 4 148952762656072862 = some 158287425574624607 :=
  join_receipt_window endpoint_13_83_flag endpoint_13_83_sources 0 2 2 148952762656072862 158287425574624607 158287425574624607 endpoint_13_83_w0 endpoint_13_83_w2
private theorem endpoint_13_83_w4 : receiptWindow endpoint_13_83_flag endpoint_13_83_sources 4 2 158287425574624607 = some 158287425574624607 := by decide +kernel
private theorem endpoint_13_83_p6 : receiptWindow endpoint_13_83_flag endpoint_13_83_sources 0 6 148952762656072862 = some 158287425574624607 :=
  join_receipt_window endpoint_13_83_flag endpoint_13_83_sources 0 4 2 148952762656072862 158287425574624607 158287425574624607 endpoint_13_83_p4 endpoint_13_83_w4
private theorem endpoint_13_83_w6 : receiptWindow endpoint_13_83_flag endpoint_13_83_sources 6 2 158287425574624607 = some 158287425574624607 := by decide +kernel
private theorem endpoint_13_83_p8 : receiptWindow endpoint_13_83_flag endpoint_13_83_sources 0 8 148952762656072862 = some 158287425574624607 :=
  join_receipt_window endpoint_13_83_flag endpoint_13_83_sources 0 6 2 148952762656072862 158287425574624607 158287425574624607 endpoint_13_83_p6 endpoint_13_83_w6
private theorem endpoint_13_83_w8 : receiptWindow endpoint_13_83_flag endpoint_13_83_sources 8 2 158287425574624607 = some 158287425574624607 := by decide +kernel
private theorem endpoint_13_83_p10 : receiptWindow endpoint_13_83_flag endpoint_13_83_sources 0 10 148952762656072862 = some 158287425574624607 :=
  join_receipt_window endpoint_13_83_flag endpoint_13_83_sources 0 8 2 148952762656072862 158287425574624607 158287425574624607 endpoint_13_83_p8 endpoint_13_83_w8
private theorem endpoint_13_83_w10 : receiptWindow endpoint_13_83_flag endpoint_13_83_sources 10 2 158287425574624607 = some 158287425574624607 := by decide +kernel
private theorem endpoint_13_83_p12 : receiptWindow endpoint_13_83_flag endpoint_13_83_sources 0 12 148952762656072862 = some 158287425574624607 :=
  join_receipt_window endpoint_13_83_flag endpoint_13_83_sources 0 10 2 148952762656072862 158287425574624607 158287425574624607 endpoint_13_83_p10 endpoint_13_83_w10
def endpoint_13_83 : CertifiedEndpoint :=
  ⟨⟨13, 83, 1126⟩, 158287425574624607, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_13_83_flag endpoint_13_83_sources 12 148952762656072862 158287425574624607 rfl endpoint_13_83_base endpoint_13_83_p12) (by decide)⟩
def endpoint_13_84 : CertifiedEndpoint :=
  ⟨⟨13, 84, 1024⟩, 243384770797109724, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_85 : CertifiedEndpoint :=
  ⟨⟨13, 85, 919⟩, 219965503968316576, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_86 : CertifiedEndpoint :=
  ⟨⟨13, 86, 812⟩, 195354388256876964, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_87 : CertifiedEndpoint :=
  ⟨⟨13, 87, 701⟩, 169015243671462662, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_88 : CertifiedEndpoint :=
  ⟨⟨13, 88, 589⟩, 141694202070771781, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_89 : CertifiedEndpoint :=
  ⟨⟨13, 89, 473⟩, 112586993467811982, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_90 : CertifiedEndpoint :=
  ⟨⟨13, 90, 355⟩, 82191039101715339, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_91 : CertifiedEndpoint :=
  ⟨⟨13, 91, 235⟩, 50486959596383776, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_92 : CertifiedEndpoint :=
  ⟨⟨13, 92, 111⟩, 16906276000325607, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_14 : CertifiedEndpoint :=
  ⟨⟨14, 14, 3996⟩, 109078272773981556, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_15 : CertifiedEndpoint :=
  ⟨⟨14, 15, 3976⟩, 113055168417564536, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_16 : CertifiedEndpoint :=
  ⟨⟨14, 16, 3955⟩, 116956711226236025, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_17 : CertifiedEndpoint :=
  ⟨⟨14, 17, 3934⟩, 129996667706792119, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_18 : CertifiedEndpoint :=
  ⟨⟨14, 18, 3912⟩, 142850028939733252, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_19 : CertifiedEndpoint :=
  ⟨⟨14, 19, 3891⟩, 155586564190222320, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_20 : CertifiedEndpoint :=
  ⟨⟨14, 20, 3869⟩, 168129528992405231, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_21 : CertifiedEndpoint :=
  ⟨⟨14, 21, 3847⟩, 180515551779036232, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_22 : CertifiedEndpoint :=
  ⟨⟨14, 22, 3825⟩, 192744632550115323, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_23 : CertifiedEndpoint :=
  ⟨⟨14, 23, 3802⟩, 204762704871160267, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_24 : CertifiedEndpoint :=
  ⟨⟨14, 24, 3780⟩, 216674414010789940, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_25 : CertifiedEndpoint :=
  ⟨⟨14, 25, 3756⟩, 228307097864520837, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_26 : CertifiedEndpoint :=
  ⟨⟨14, 26, 3733⟩, 239833418536836463, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_27 : CertifiedEndpoint :=
  ⟨⟨14, 27, 3709⟩, 251127805157044354, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_14_28_flag : Flag := ⟨14, 28, 3685⟩
private def endpoint_14_28_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_28_base : receiptBase endpoint_14_28_flag endpoint_14_28_sources = some 178468697775203609 := by decide +kernel
private theorem endpoint_14_28_w0 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 2 178468697775203609 = some 178468697775203609 := by decide +kernel
private theorem endpoint_14_28_w2 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 2 2 178468697775203609 = some 178468697775203609 := by decide +kernel
private theorem endpoint_14_28_p4 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 4 178468697775203609 = some 178468697775203609 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 2 2 178468697775203609 178468697775203609 178468697775203609 endpoint_14_28_w0 endpoint_14_28_w2
private theorem endpoint_14_28_w4 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 4 2 178468697775203609 = some 178468697775203609 := by decide +kernel
private theorem endpoint_14_28_p6 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 6 178468697775203609 = some 178468697775203609 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 4 2 178468697775203609 178468697775203609 178468697775203609 endpoint_14_28_p4 endpoint_14_28_w4
private theorem endpoint_14_28_w6 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 6 2 178468697775203609 = some 178468697775203609 := by decide +kernel
private theorem endpoint_14_28_p8 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 8 178468697775203609 = some 178468697775203609 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 6 2 178468697775203609 178468697775203609 178468697775203609 endpoint_14_28_p6 endpoint_14_28_w6
private theorem endpoint_14_28_w8 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 8 2 178468697775203609 = some 178468697775203609 := by decide +kernel
private theorem endpoint_14_28_p10 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 10 178468697775203609 = some 178468697775203609 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 8 2 178468697775203609 178468697775203609 178468697775203609 endpoint_14_28_p8 endpoint_14_28_w8
private theorem endpoint_14_28_w10 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 10 2 178468697775203609 = some 178468697775203609 := by decide +kernel
private theorem endpoint_14_28_p12 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 12 178468697775203609 = some 178468697775203609 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 10 2 178468697775203609 178468697775203609 178468697775203609 endpoint_14_28_p10 endpoint_14_28_w10
private theorem endpoint_14_28_w12 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 12 1 178468697775203609 = some 178468697775203609 := by decide +kernel
private theorem endpoint_14_28_p13 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 13 178468697775203609 = some 178468697775203609 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 12 1 178468697775203609 178468697775203609 178468697775203609 endpoint_14_28_p12 endpoint_14_28_w12
def endpoint_14_28 : CertifiedEndpoint :=
  ⟨⟨14, 28, 3685⟩, 178468697775203609, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_28_flag endpoint_14_28_sources 13 178468697775203609 178468697775203609 rfl endpoint_14_28_base endpoint_14_28_p13) (by decide)⟩
private def endpoint_14_29_flag : Flag := ⟨14, 29, 3661⟩
private def endpoint_14_29_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_29_base : receiptBase endpoint_14_29_flag endpoint_14_29_sources = some 182476605844647551 := by decide +kernel
private theorem endpoint_14_29_w0 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 2 182476605844647551 = some 182476605844647551 := by decide +kernel
private theorem endpoint_14_29_w2 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 2 2 182476605844647551 = some 182476605844647551 := by decide +kernel
private theorem endpoint_14_29_p4 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 4 182476605844647551 = some 182476605844647551 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 2 2 182476605844647551 182476605844647551 182476605844647551 endpoint_14_29_w0 endpoint_14_29_w2
private theorem endpoint_14_29_w4 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 4 2 182476605844647551 = some 182476605844647551 := by decide +kernel
private theorem endpoint_14_29_p6 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 6 182476605844647551 = some 182476605844647551 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 4 2 182476605844647551 182476605844647551 182476605844647551 endpoint_14_29_p4 endpoint_14_29_w4
private theorem endpoint_14_29_w6 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 6 2 182476605844647551 = some 182476605844647551 := by decide +kernel
private theorem endpoint_14_29_p8 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 8 182476605844647551 = some 182476605844647551 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 6 2 182476605844647551 182476605844647551 182476605844647551 endpoint_14_29_p6 endpoint_14_29_w6
private theorem endpoint_14_29_w8 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 8 2 182476605844647551 = some 182476605844647551 := by decide +kernel
private theorem endpoint_14_29_p10 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 10 182476605844647551 = some 182476605844647551 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 8 2 182476605844647551 182476605844647551 182476605844647551 endpoint_14_29_p8 endpoint_14_29_w8
private theorem endpoint_14_29_w10 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 10 2 182476605844647551 = some 182476605844647551 := by decide +kernel
private theorem endpoint_14_29_p12 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 12 182476605844647551 = some 182476605844647551 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 10 2 182476605844647551 182476605844647551 182476605844647551 endpoint_14_29_p10 endpoint_14_29_w10
private theorem endpoint_14_29_w12 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 12 1 182476605844647551 = some 182476605844647551 := by decide +kernel
private theorem endpoint_14_29_p13 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 13 182476605844647551 = some 182476605844647551 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 12 1 182476605844647551 182476605844647551 182476605844647551 endpoint_14_29_p12 endpoint_14_29_w12
def endpoint_14_29 : CertifiedEndpoint :=
  ⟨⟨14, 29, 3661⟩, 182476605844647551, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_29_flag endpoint_14_29_sources 13 182476605844647551 182476605844647551 rfl endpoint_14_29_base endpoint_14_29_p13) (by decide)⟩
private def endpoint_14_30_flag : Flag := ⟨14, 30, 3637⟩
private def endpoint_14_30_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_30_base : receiptBase endpoint_14_30_flag endpoint_14_30_sources = some 186417150040324812 := by decide +kernel
private theorem endpoint_14_30_w0 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 2 186417150040324812 = some 186417150040324812 := by decide +kernel
private theorem endpoint_14_30_w2 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 2 2 186417150040324812 = some 186417150040324812 := by decide +kernel
private theorem endpoint_14_30_p4 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 4 186417150040324812 = some 186417150040324812 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 2 2 186417150040324812 186417150040324812 186417150040324812 endpoint_14_30_w0 endpoint_14_30_w2
private theorem endpoint_14_30_w4 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 4 2 186417150040324812 = some 186417150040324812 := by decide +kernel
private theorem endpoint_14_30_p6 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 6 186417150040324812 = some 186417150040324812 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 4 2 186417150040324812 186417150040324812 186417150040324812 endpoint_14_30_p4 endpoint_14_30_w4
private theorem endpoint_14_30_w6 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 6 2 186417150040324812 = some 186417150040324812 := by decide +kernel
private theorem endpoint_14_30_p8 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 8 186417150040324812 = some 186417150040324812 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 6 2 186417150040324812 186417150040324812 186417150040324812 endpoint_14_30_p6 endpoint_14_30_w6
private theorem endpoint_14_30_w8 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 8 2 186417150040324812 = some 186417150040324812 := by decide +kernel
private theorem endpoint_14_30_p10 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 10 186417150040324812 = some 186417150040324812 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 8 2 186417150040324812 186417150040324812 186417150040324812 endpoint_14_30_p8 endpoint_14_30_w8
private theorem endpoint_14_30_w10 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 10 2 186417150040324812 = some 186417150040324812 := by decide +kernel
private theorem endpoint_14_30_p12 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 12 186417150040324812 = some 186417150040324812 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 10 2 186417150040324812 186417150040324812 186417150040324812 endpoint_14_30_p10 endpoint_14_30_w10
private theorem endpoint_14_30_w12 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 12 1 186417150040324812 = some 186417150040324812 := by decide +kernel
private theorem endpoint_14_30_p13 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 13 186417150040324812 = some 186417150040324812 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 12 1 186417150040324812 186417150040324812 186417150040324812 endpoint_14_30_p12 endpoint_14_30_w12
def endpoint_14_30 : CertifiedEndpoint :=
  ⟨⟨14, 30, 3637⟩, 186417150040324812, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_30_flag endpoint_14_30_sources 13 186417150040324812 186417150040324812 rfl endpoint_14_30_base endpoint_14_30_p13) (by decide)⟩
private def endpoint_14_31_flag : Flag := ⟨14, 31, 3612⟩
private def endpoint_14_31_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_31_base : receiptBase endpoint_14_31_flag endpoint_14_31_sources = some 190238491617329564 := by decide +kernel
private theorem endpoint_14_31_w0 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 2 190238491617329564 = some 190238491617329564 := by decide +kernel
private theorem endpoint_14_31_w2 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 2 2 190238491617329564 = some 190238491617329564 := by decide +kernel
private theorem endpoint_14_31_p4 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 4 190238491617329564 = some 190238491617329564 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 2 2 190238491617329564 190238491617329564 190238491617329564 endpoint_14_31_w0 endpoint_14_31_w2
private theorem endpoint_14_31_w4 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 4 2 190238491617329564 = some 190238491617329564 := by decide +kernel
private theorem endpoint_14_31_p6 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 6 190238491617329564 = some 190238491617329564 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 4 2 190238491617329564 190238491617329564 190238491617329564 endpoint_14_31_p4 endpoint_14_31_w4
private theorem endpoint_14_31_w6 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 6 2 190238491617329564 = some 190238491617329564 := by decide +kernel
private theorem endpoint_14_31_p8 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 8 190238491617329564 = some 190238491617329564 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 6 2 190238491617329564 190238491617329564 190238491617329564 endpoint_14_31_p6 endpoint_14_31_w6
private theorem endpoint_14_31_w8 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 8 2 190238491617329564 = some 190238491617329564 := by decide +kernel
private theorem endpoint_14_31_p10 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 10 190238491617329564 = some 190238491617329564 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 8 2 190238491617329564 190238491617329564 190238491617329564 endpoint_14_31_p8 endpoint_14_31_w8
private theorem endpoint_14_31_w10 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 10 2 190238491617329564 = some 190238491617329564 := by decide +kernel
private theorem endpoint_14_31_p12 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 12 190238491617329564 = some 190238491617329564 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 10 2 190238491617329564 190238491617329564 190238491617329564 endpoint_14_31_p10 endpoint_14_31_w10
private theorem endpoint_14_31_w12 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 12 1 190238491617329564 = some 190238491617329564 := by decide +kernel
private theorem endpoint_14_31_p13 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 13 190238491617329564 = some 190238491617329564 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 12 1 190238491617329564 190238491617329564 190238491617329564 endpoint_14_31_p12 endpoint_14_31_w12
def endpoint_14_31 : CertifiedEndpoint :=
  ⟨⟨14, 31, 3612⟩, 190238491617329564, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_31_flag endpoint_14_31_sources 13 190238491617329564 190238491617329564 rfl endpoint_14_31_base endpoint_14_31_p13) (by decide)⟩
private def endpoint_14_32_flag : Flag := ⟨14, 32, 3586⟩
private def endpoint_14_32_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_32_base : receiptBase endpoint_14_32_flag endpoint_14_32_sources = some 193936507496546863 := by decide +kernel
private theorem endpoint_14_32_w0 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 2 193936507496546863 = some 193936507496546863 := by decide +kernel
private theorem endpoint_14_32_w2 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 2 2 193936507496546863 = some 193936507496546863 := by decide +kernel
private theorem endpoint_14_32_p4 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 4 193936507496546863 = some 193936507496546863 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 2 2 193936507496546863 193936507496546863 193936507496546863 endpoint_14_32_w0 endpoint_14_32_w2
private theorem endpoint_14_32_w4 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 4 2 193936507496546863 = some 193936507496546863 := by decide +kernel
private theorem endpoint_14_32_p6 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 6 193936507496546863 = some 193936507496546863 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 4 2 193936507496546863 193936507496546863 193936507496546863 endpoint_14_32_p4 endpoint_14_32_w4
private theorem endpoint_14_32_w6 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 6 2 193936507496546863 = some 193936507496546863 := by decide +kernel
private theorem endpoint_14_32_p8 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 8 193936507496546863 = some 193936507496546863 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 6 2 193936507496546863 193936507496546863 193936507496546863 endpoint_14_32_p6 endpoint_14_32_w6
private theorem endpoint_14_32_w8 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 8 2 193936507496546863 = some 193936507496546863 := by decide +kernel
private theorem endpoint_14_32_p10 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 10 193936507496546863 = some 193936507496546863 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 8 2 193936507496546863 193936507496546863 193936507496546863 endpoint_14_32_p8 endpoint_14_32_w8
private theorem endpoint_14_32_w10 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 10 2 193936507496546863 = some 193936507496546863 := by decide +kernel
private theorem endpoint_14_32_p12 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 12 193936507496546863 = some 193936507496546863 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 10 2 193936507496546863 193936507496546863 193936507496546863 endpoint_14_32_p10 endpoint_14_32_w10
private theorem endpoint_14_32_w12 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 12 1 193936507496546863 = some 193936507496546863 := by decide +kernel
private theorem endpoint_14_32_p13 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 13 193936507496546863 = some 193936507496546863 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 12 1 193936507496546863 193936507496546863 193936507496546863 endpoint_14_32_p12 endpoint_14_32_w12
def endpoint_14_32 : CertifiedEndpoint :=
  ⟨⟨14, 32, 3586⟩, 193936507496546863, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_32_flag endpoint_14_32_sources 13 193936507496546863 193936507496546863 rfl endpoint_14_32_base endpoint_14_32_p13) (by decide)⟩
private def endpoint_14_33_flag : Flag := ⟨14, 33, 3561⟩
private def endpoint_14_33_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_33_base : receiptBase endpoint_14_33_flag endpoint_14_33_sources = some 197616249527493346 := by decide +kernel
private theorem endpoint_14_33_w0 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 2 197616249527493346 = some 197616249527493346 := by decide +kernel
private theorem endpoint_14_33_w2 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 2 2 197616249527493346 = some 197616249527493346 := by decide +kernel
private theorem endpoint_14_33_p4 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 4 197616249527493346 = some 197616249527493346 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 2 2 197616249527493346 197616249527493346 197616249527493346 endpoint_14_33_w0 endpoint_14_33_w2
private theorem endpoint_14_33_w4 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 4 2 197616249527493346 = some 197616249527493346 := by decide +kernel
private theorem endpoint_14_33_p6 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 6 197616249527493346 = some 197616249527493346 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 4 2 197616249527493346 197616249527493346 197616249527493346 endpoint_14_33_p4 endpoint_14_33_w4
private theorem endpoint_14_33_w6 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 6 2 197616249527493346 = some 197616249527493346 := by decide +kernel
private theorem endpoint_14_33_p8 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 8 197616249527493346 = some 197616249527493346 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 6 2 197616249527493346 197616249527493346 197616249527493346 endpoint_14_33_p6 endpoint_14_33_w6
private theorem endpoint_14_33_w8 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 8 2 197616249527493346 = some 197616249527493346 := by decide +kernel
private theorem endpoint_14_33_p10 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 10 197616249527493346 = some 197616249527493346 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 8 2 197616249527493346 197616249527493346 197616249527493346 endpoint_14_33_p8 endpoint_14_33_w8
private theorem endpoint_14_33_w10 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 10 2 197616249527493346 = some 197616249527493346 := by decide +kernel
private theorem endpoint_14_33_p12 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 12 197616249527493346 = some 197616249527493346 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 10 2 197616249527493346 197616249527493346 197616249527493346 endpoint_14_33_p10 endpoint_14_33_w10
private theorem endpoint_14_33_w12 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 12 1 197616249527493346 = some 197616249527493346 := by decide +kernel
private theorem endpoint_14_33_p13 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 13 197616249527493346 = some 197616249527493346 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 12 1 197616249527493346 197616249527493346 197616249527493346 endpoint_14_33_p12 endpoint_14_33_w12
def endpoint_14_33 : CertifiedEndpoint :=
  ⟨⟨14, 33, 3561⟩, 197616249527493346, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_33_flag endpoint_14_33_sources 13 197616249527493346 197616249527493346 rfl endpoint_14_33_base endpoint_14_33_p13) (by decide)⟩
private def endpoint_14_34_flag : Flag := ⟨14, 34, 3534⟩
private def endpoint_14_34_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_34_base : receiptBase endpoint_14_34_flag endpoint_14_34_sources = some 202326823566360997 := by decide +kernel
private theorem endpoint_14_34_w0 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 2 202326823566360997 = some 202326823566360997 := by decide +kernel
private theorem endpoint_14_34_w2 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 2 2 202326823566360997 = some 202326823566360997 := by decide +kernel
private theorem endpoint_14_34_p4 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 4 202326823566360997 = some 202326823566360997 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 2 2 202326823566360997 202326823566360997 202326823566360997 endpoint_14_34_w0 endpoint_14_34_w2
private theorem endpoint_14_34_w4 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 4 2 202326823566360997 = some 202326823566360997 := by decide +kernel
private theorem endpoint_14_34_p6 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 6 202326823566360997 = some 202326823566360997 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 4 2 202326823566360997 202326823566360997 202326823566360997 endpoint_14_34_p4 endpoint_14_34_w4
private theorem endpoint_14_34_w6 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 6 2 202326823566360997 = some 202326823566360997 := by decide +kernel
private theorem endpoint_14_34_p8 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 8 202326823566360997 = some 202326823566360997 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 6 2 202326823566360997 202326823566360997 202326823566360997 endpoint_14_34_p6 endpoint_14_34_w6
private theorem endpoint_14_34_w8 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 8 2 202326823566360997 = some 202326823566360997 := by decide +kernel
private theorem endpoint_14_34_p10 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 10 202326823566360997 = some 202326823566360997 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 8 2 202326823566360997 202326823566360997 202326823566360997 endpoint_14_34_p8 endpoint_14_34_w8
private theorem endpoint_14_34_w10 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 10 2 202326823566360997 = some 202326823566360997 := by decide +kernel
private theorem endpoint_14_34_p12 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 12 202326823566360997 = some 202326823566360997 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 10 2 202326823566360997 202326823566360997 202326823566360997 endpoint_14_34_p10 endpoint_14_34_w10
private theorem endpoint_14_34_w12 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 12 1 202326823566360997 = some 202326823566360997 := by decide +kernel
private theorem endpoint_14_34_p13 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 13 202326823566360997 = some 202326823566360997 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 12 1 202326823566360997 202326823566360997 202326823566360997 endpoint_14_34_p12 endpoint_14_34_w12
def endpoint_14_34 : CertifiedEndpoint :=
  ⟨⟨14, 34, 3534⟩, 202326823566360997, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_34_flag endpoint_14_34_sources 13 202326823566360997 202326823566360997 rfl endpoint_14_34_base endpoint_14_34_p13) (by decide)⟩
private def endpoint_14_35_flag : Flag := ⟨14, 35, 3508⟩
private def endpoint_14_35_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_35_base : receiptBase endpoint_14_35_flag endpoint_14_35_sources = some 205729387202576741 := by decide +kernel
private theorem endpoint_14_35_w0 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 2 205729387202576741 = some 205729387202576741 := by decide +kernel
private theorem endpoint_14_35_w2 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 2 2 205729387202576741 = some 205729387202576741 := by decide +kernel
private theorem endpoint_14_35_p4 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 4 205729387202576741 = some 205729387202576741 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 2 2 205729387202576741 205729387202576741 205729387202576741 endpoint_14_35_w0 endpoint_14_35_w2
private theorem endpoint_14_35_w4 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 4 2 205729387202576741 = some 205729387202576741 := by decide +kernel
private theorem endpoint_14_35_p6 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 6 205729387202576741 = some 205729387202576741 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 4 2 205729387202576741 205729387202576741 205729387202576741 endpoint_14_35_p4 endpoint_14_35_w4
private theorem endpoint_14_35_w6 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 6 2 205729387202576741 = some 205729387202576741 := by decide +kernel
private theorem endpoint_14_35_p8 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 8 205729387202576741 = some 205729387202576741 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 6 2 205729387202576741 205729387202576741 205729387202576741 endpoint_14_35_p6 endpoint_14_35_w6
private theorem endpoint_14_35_w8 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 8 2 205729387202576741 = some 205729387202576741 := by decide +kernel
private theorem endpoint_14_35_p10 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 10 205729387202576741 = some 205729387202576741 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 8 2 205729387202576741 205729387202576741 205729387202576741 endpoint_14_35_p8 endpoint_14_35_w8
private theorem endpoint_14_35_w10 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 10 2 205729387202576741 = some 205729387202576741 := by decide +kernel
private theorem endpoint_14_35_p12 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 12 205729387202576741 = some 205729387202576741 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 10 2 205729387202576741 205729387202576741 205729387202576741 endpoint_14_35_p10 endpoint_14_35_w10
private theorem endpoint_14_35_w12 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 12 1 205729387202576741 = some 205729387202576741 := by decide +kernel
private theorem endpoint_14_35_p13 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 13 205729387202576741 = some 205729387202576741 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 12 1 205729387202576741 205729387202576741 205729387202576741 endpoint_14_35_p12 endpoint_14_35_w12
def endpoint_14_35 : CertifiedEndpoint :=
  ⟨⟨14, 35, 3508⟩, 205729387202576741, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_35_flag endpoint_14_35_sources 13 205729387202576741 205729387202576741 rfl endpoint_14_35_base endpoint_14_35_p13) (by decide)⟩
private def endpoint_14_36_flag : Flag := ⟨14, 36, 3481⟩
private def endpoint_14_36_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_36_base : receiptBase endpoint_14_36_flag endpoint_14_36_sources = some 209000816113715358 := by decide +kernel
private theorem endpoint_14_36_w0 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 2 209000816113715358 = some 209000816113715358 := by decide +kernel
private theorem endpoint_14_36_w2 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 2 2 209000816113715358 = some 209000816113715358 := by decide +kernel
private theorem endpoint_14_36_p4 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 4 209000816113715358 = some 209000816113715358 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 2 2 209000816113715358 209000816113715358 209000816113715358 endpoint_14_36_w0 endpoint_14_36_w2
private theorem endpoint_14_36_w4 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 4 2 209000816113715358 = some 209000816113715358 := by decide +kernel
private theorem endpoint_14_36_p6 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 6 209000816113715358 = some 209000816113715358 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 4 2 209000816113715358 209000816113715358 209000816113715358 endpoint_14_36_p4 endpoint_14_36_w4
private theorem endpoint_14_36_w6 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 6 2 209000816113715358 = some 209000816113715358 := by decide +kernel
private theorem endpoint_14_36_p8 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 8 209000816113715358 = some 209000816113715358 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 6 2 209000816113715358 209000816113715358 209000816113715358 endpoint_14_36_p6 endpoint_14_36_w6
private theorem endpoint_14_36_w8 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 8 2 209000816113715358 = some 209000816113715358 := by decide +kernel
private theorem endpoint_14_36_p10 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 10 209000816113715358 = some 209000816113715358 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 8 2 209000816113715358 209000816113715358 209000816113715358 endpoint_14_36_p8 endpoint_14_36_w8
private theorem endpoint_14_36_w10 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 10 2 209000816113715358 = some 209000816113715358 := by decide +kernel
private theorem endpoint_14_36_p12 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 12 209000816113715358 = some 209000816113715358 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 10 2 209000816113715358 209000816113715358 209000816113715358 endpoint_14_36_p10 endpoint_14_36_w10
private theorem endpoint_14_36_w12 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 12 1 209000816113715358 = some 209000816113715358 := by decide +kernel
private theorem endpoint_14_36_p13 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 13 209000816113715358 = some 209000816113715358 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 12 1 209000816113715358 209000816113715358 209000816113715358 endpoint_14_36_p12 endpoint_14_36_w12
def endpoint_14_36 : CertifiedEndpoint :=
  ⟨⟨14, 36, 3481⟩, 209000816113715358, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_36_flag endpoint_14_36_sources 13 209000816113715358 209000816113715358 rfl endpoint_14_36_base endpoint_14_36_p13) (by decide)⟩
private def endpoint_14_37_flag : Flag := ⟨14, 37, 3454⟩
private def endpoint_14_37_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_37_base : receiptBase endpoint_14_37_flag endpoint_14_37_sources = some 212197517166074868 := by decide +kernel
private theorem endpoint_14_37_w0 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 2 212197517166074868 = some 212197517166074868 := by decide +kernel
private theorem endpoint_14_37_w2 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 2 2 212197517166074868 = some 212197517166074868 := by decide +kernel
private theorem endpoint_14_37_p4 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 4 212197517166074868 = some 212197517166074868 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 2 2 212197517166074868 212197517166074868 212197517166074868 endpoint_14_37_w0 endpoint_14_37_w2
private theorem endpoint_14_37_w4 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 4 2 212197517166074868 = some 212197517166074868 := by decide +kernel
private theorem endpoint_14_37_p6 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 6 212197517166074868 = some 212197517166074868 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 4 2 212197517166074868 212197517166074868 212197517166074868 endpoint_14_37_p4 endpoint_14_37_w4
private theorem endpoint_14_37_w6 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 6 2 212197517166074868 = some 212197517166074868 := by decide +kernel
private theorem endpoint_14_37_p8 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 8 212197517166074868 = some 212197517166074868 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 6 2 212197517166074868 212197517166074868 212197517166074868 endpoint_14_37_p6 endpoint_14_37_w6
private theorem endpoint_14_37_w8 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 8 2 212197517166074868 = some 212197517166074868 := by decide +kernel
private theorem endpoint_14_37_p10 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 10 212197517166074868 = some 212197517166074868 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 8 2 212197517166074868 212197517166074868 212197517166074868 endpoint_14_37_p8 endpoint_14_37_w8
private theorem endpoint_14_37_w10 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 10 2 212197517166074868 = some 212197517166074868 := by decide +kernel
private theorem endpoint_14_37_p12 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 12 212197517166074868 = some 212197517166074868 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 10 2 212197517166074868 212197517166074868 212197517166074868 endpoint_14_37_p10 endpoint_14_37_w10
private theorem endpoint_14_37_w12 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 12 1 212197517166074868 = some 212197517166074868 := by decide +kernel
private theorem endpoint_14_37_p13 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 13 212197517166074868 = some 212197517166074868 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 12 1 212197517166074868 212197517166074868 212197517166074868 endpoint_14_37_p12 endpoint_14_37_w12
def endpoint_14_37 : CertifiedEndpoint :=
  ⟨⟨14, 37, 3454⟩, 212197517166074868, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_37_flag endpoint_14_37_sources 13 212197517166074868 212197517166074868 rfl endpoint_14_37_base endpoint_14_37_p13) (by decide)⟩
private def endpoint_14_38_flag : Flag := ⟨14, 38, 3426⟩
private def endpoint_14_38_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_38_base : receiptBase endpoint_14_38_flag endpoint_14_38_sources = some 215257649067235500 := by decide +kernel
private theorem endpoint_14_38_w0 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 2 215257649067235500 = some 215257649067235500 := by decide +kernel
private theorem endpoint_14_38_w2 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 2 2 215257649067235500 = some 215257649067235500 := by decide +kernel
private theorem endpoint_14_38_p4 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 4 215257649067235500 = some 215257649067235500 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 2 2 215257649067235500 215257649067235500 215257649067235500 endpoint_14_38_w0 endpoint_14_38_w2
private theorem endpoint_14_38_w4 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 4 2 215257649067235500 = some 215257649067235500 := by decide +kernel
private theorem endpoint_14_38_p6 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 6 215257649067235500 = some 215257649067235500 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 4 2 215257649067235500 215257649067235500 215257649067235500 endpoint_14_38_p4 endpoint_14_38_w4
private theorem endpoint_14_38_w6 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 6 2 215257649067235500 = some 215257649067235500 := by decide +kernel
private theorem endpoint_14_38_p8 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 8 215257649067235500 = some 215257649067235500 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 6 2 215257649067235500 215257649067235500 215257649067235500 endpoint_14_38_p6 endpoint_14_38_w6
private theorem endpoint_14_38_w8 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 8 2 215257649067235500 = some 215257649067235500 := by decide +kernel
private theorem endpoint_14_38_p10 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 10 215257649067235500 = some 215257649067235500 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 8 2 215257649067235500 215257649067235500 215257649067235500 endpoint_14_38_p8 endpoint_14_38_w8
private theorem endpoint_14_38_w10 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 10 2 215257649067235500 = some 215257649067235500 := by decide +kernel
private theorem endpoint_14_38_p12 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 12 215257649067235500 = some 215257649067235500 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 10 2 215257649067235500 215257649067235500 215257649067235500 endpoint_14_38_p10 endpoint_14_38_w10
private theorem endpoint_14_38_w12 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 12 1 215257649067235500 = some 215257649067235500 := by decide +kernel
private theorem endpoint_14_38_p13 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 13 215257649067235500 = some 215257649067235500 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 12 1 215257649067235500 215257649067235500 215257649067235500 endpoint_14_38_p12 endpoint_14_38_w12
def endpoint_14_38 : CertifiedEndpoint :=
  ⟨⟨14, 38, 3426⟩, 215257649067235500, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_38_flag endpoint_14_38_sources 13 215257649067235500 215257649067235500 rfl endpoint_14_38_base endpoint_14_38_p13) (by decide)⟩
private def endpoint_14_39_flag : Flag := ⟨14, 39, 3397⟩
private def endpoint_14_39_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_39_base : receiptBase endpoint_14_39_flag endpoint_14_39_sources = some 218177135997605939 := by decide +kernel
private theorem endpoint_14_39_w0 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 2 218177135997605939 = some 218177135997605939 := by decide +kernel
private theorem endpoint_14_39_w2 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 2 2 218177135997605939 = some 218177135997605939 := by decide +kernel
private theorem endpoint_14_39_p4 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 4 218177135997605939 = some 218177135997605939 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 2 2 218177135997605939 218177135997605939 218177135997605939 endpoint_14_39_w0 endpoint_14_39_w2
private theorem endpoint_14_39_w4 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 4 2 218177135997605939 = some 218177135997605939 := by decide +kernel
private theorem endpoint_14_39_p6 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 6 218177135997605939 = some 218177135997605939 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 4 2 218177135997605939 218177135997605939 218177135997605939 endpoint_14_39_p4 endpoint_14_39_w4
private theorem endpoint_14_39_w6 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 6 2 218177135997605939 = some 218177135997605939 := by decide +kernel
private theorem endpoint_14_39_p8 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 8 218177135997605939 = some 218177135997605939 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 6 2 218177135997605939 218177135997605939 218177135997605939 endpoint_14_39_p6 endpoint_14_39_w6
private theorem endpoint_14_39_w8 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 8 2 218177135997605939 = some 218177135997605939 := by decide +kernel
private theorem endpoint_14_39_p10 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 10 218177135997605939 = some 218177135997605939 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 8 2 218177135997605939 218177135997605939 218177135997605939 endpoint_14_39_p8 endpoint_14_39_w8
private theorem endpoint_14_39_w10 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 10 2 218177135997605939 = some 218177135997605939 := by decide +kernel
private theorem endpoint_14_39_p12 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 12 218177135997605939 = some 218177135997605939 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 10 2 218177135997605939 218177135997605939 218177135997605939 endpoint_14_39_p10 endpoint_14_39_w10
private theorem endpoint_14_39_w12 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 12 1 218177135997605939 = some 218177135997605939 := by decide +kernel
private theorem endpoint_14_39_p13 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 13 218177135997605939 = some 218177135997605939 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 12 1 218177135997605939 218177135997605939 218177135997605939 endpoint_14_39_p12 endpoint_14_39_w12
def endpoint_14_39 : CertifiedEndpoint :=
  ⟨⟨14, 39, 3397⟩, 218177135997605939, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_39_flag endpoint_14_39_sources 13 218177135997605939 218177135997605939 rfl endpoint_14_39_base endpoint_14_39_p13) (by decide)⟩
private def endpoint_14_40_flag : Flag := ⟨14, 40, 3369⟩
private def endpoint_14_40_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_40_base : receiptBase endpoint_14_40_flag endpoint_14_40_sources = some 221664207531327764 := by decide +kernel
private theorem endpoint_14_40_w0 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 2 221664207531327764 = some 221664207531327764 := by decide +kernel
private theorem endpoint_14_40_w2 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 2 2 221664207531327764 = some 221664207531327764 := by decide +kernel
private theorem endpoint_14_40_p4 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 4 221664207531327764 = some 221664207531327764 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 2 2 221664207531327764 221664207531327764 221664207531327764 endpoint_14_40_w0 endpoint_14_40_w2
private theorem endpoint_14_40_w4 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 4 2 221664207531327764 = some 221664207531327764 := by decide +kernel
private theorem endpoint_14_40_p6 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 6 221664207531327764 = some 221664207531327764 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 4 2 221664207531327764 221664207531327764 221664207531327764 endpoint_14_40_p4 endpoint_14_40_w4
private theorem endpoint_14_40_w6 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 6 2 221664207531327764 = some 221664207531327764 := by decide +kernel
private theorem endpoint_14_40_p8 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 8 221664207531327764 = some 221664207531327764 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 6 2 221664207531327764 221664207531327764 221664207531327764 endpoint_14_40_p6 endpoint_14_40_w6
private theorem endpoint_14_40_w8 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 8 2 221664207531327764 = some 221664207531327764 := by decide +kernel
private theorem endpoint_14_40_p10 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 10 221664207531327764 = some 221664207531327764 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 8 2 221664207531327764 221664207531327764 221664207531327764 endpoint_14_40_p8 endpoint_14_40_w8
private theorem endpoint_14_40_w10 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 10 2 221664207531327764 = some 221664207531327764 := by decide +kernel
private theorem endpoint_14_40_p12 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 12 221664207531327764 = some 221664207531327764 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 10 2 221664207531327764 221664207531327764 221664207531327764 endpoint_14_40_p10 endpoint_14_40_w10
private theorem endpoint_14_40_w12 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 12 1 221664207531327764 = some 221664207531327764 := by decide +kernel
private theorem endpoint_14_40_p13 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 13 221664207531327764 = some 221664207531327764 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 12 1 221664207531327764 221664207531327764 221664207531327764 endpoint_14_40_p12 endpoint_14_40_w12
def endpoint_14_40 : CertifiedEndpoint :=
  ⟨⟨14, 40, 3369⟩, 221664207531327764, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_40_flag endpoint_14_40_sources 13 221664207531327764 221664207531327764 rfl endpoint_14_40_base endpoint_14_40_p13) (by decide)⟩
private def endpoint_14_41_flag : Flag := ⟨14, 41, 3339⟩
private def endpoint_14_41_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_41_base : receiptBase endpoint_14_41_flag endpoint_14_41_sources = some 224374142618225212 := by decide +kernel
private theorem endpoint_14_41_w0 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 2 224374142618225212 = some 224374142618225212 := by decide +kernel
private theorem endpoint_14_41_w2 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 2 2 224374142618225212 = some 224374142618225212 := by decide +kernel
private theorem endpoint_14_41_p4 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 4 224374142618225212 = some 224374142618225212 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 2 2 224374142618225212 224374142618225212 224374142618225212 endpoint_14_41_w0 endpoint_14_41_w2
private theorem endpoint_14_41_w4 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 4 2 224374142618225212 = some 224374142618225212 := by decide +kernel
private theorem endpoint_14_41_p6 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 6 224374142618225212 = some 224374142618225212 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 4 2 224374142618225212 224374142618225212 224374142618225212 endpoint_14_41_p4 endpoint_14_41_w4
private theorem endpoint_14_41_w6 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 6 2 224374142618225212 = some 224374142618225212 := by decide +kernel
private theorem endpoint_14_41_p8 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 8 224374142618225212 = some 224374142618225212 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 6 2 224374142618225212 224374142618225212 224374142618225212 endpoint_14_41_p6 endpoint_14_41_w6
private theorem endpoint_14_41_w8 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 8 2 224374142618225212 = some 224374142618225212 := by decide +kernel
private theorem endpoint_14_41_p10 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 10 224374142618225212 = some 224374142618225212 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 8 2 224374142618225212 224374142618225212 224374142618225212 endpoint_14_41_p8 endpoint_14_41_w8
private theorem endpoint_14_41_w10 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 10 2 224374142618225212 = some 224374142618225212 := by decide +kernel
private theorem endpoint_14_41_p12 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 12 224374142618225212 = some 224374142618225212 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 10 2 224374142618225212 224374142618225212 224374142618225212 endpoint_14_41_p10 endpoint_14_41_w10
private theorem endpoint_14_41_w12 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 12 1 224374142618225212 = some 224374142618225212 := by decide +kernel
private theorem endpoint_14_41_p13 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 13 224374142618225212 = some 224374142618225212 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 12 1 224374142618225212 224374142618225212 224374142618225212 endpoint_14_41_p12 endpoint_14_41_w12
def endpoint_14_41 : CertifiedEndpoint :=
  ⟨⟨14, 41, 3339⟩, 224374142618225212, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_41_flag endpoint_14_41_sources 13 224374142618225212 224374142618225212 rfl endpoint_14_41_base endpoint_14_41_p13) (by decide)⟩
private def endpoint_14_42_flag : Flag := ⟨14, 42, 3309⟩
private def endpoint_14_42_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_42_base : receiptBase endpoint_14_42_flag endpoint_14_42_sources = some 227000649162690181 := by decide +kernel
private theorem endpoint_14_42_w0 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 2 227000649162690181 = some 227000649162690181 := by decide +kernel
private theorem endpoint_14_42_w2 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 2 2 227000649162690181 = some 227000649162690181 := by decide +kernel
private theorem endpoint_14_42_p4 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 4 227000649162690181 = some 227000649162690181 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 2 2 227000649162690181 227000649162690181 227000649162690181 endpoint_14_42_w0 endpoint_14_42_w2
private theorem endpoint_14_42_w4 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 4 2 227000649162690181 = some 227000649162690181 := by decide +kernel
private theorem endpoint_14_42_p6 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 6 227000649162690181 = some 227000649162690181 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 4 2 227000649162690181 227000649162690181 227000649162690181 endpoint_14_42_p4 endpoint_14_42_w4
private theorem endpoint_14_42_w6 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 6 2 227000649162690181 = some 227000649162690181 := by decide +kernel
private theorem endpoint_14_42_p8 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 8 227000649162690181 = some 227000649162690181 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 6 2 227000649162690181 227000649162690181 227000649162690181 endpoint_14_42_p6 endpoint_14_42_w6
private theorem endpoint_14_42_w8 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 8 2 227000649162690181 = some 227000649162690181 := by decide +kernel
private theorem endpoint_14_42_p10 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 10 227000649162690181 = some 227000649162690181 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 8 2 227000649162690181 227000649162690181 227000649162690181 endpoint_14_42_p8 endpoint_14_42_w8
private theorem endpoint_14_42_w10 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 10 2 227000649162690181 = some 227000649162690181 := by decide +kernel
private theorem endpoint_14_42_p12 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 12 227000649162690181 = some 227000649162690181 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 10 2 227000649162690181 227000649162690181 227000649162690181 endpoint_14_42_p10 endpoint_14_42_w10
private theorem endpoint_14_42_w12 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 12 1 227000649162690181 = some 227000649162690181 := by decide +kernel
private theorem endpoint_14_42_p13 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 13 227000649162690181 = some 227000649162690181 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 12 1 227000649162690181 227000649162690181 227000649162690181 endpoint_14_42_p12 endpoint_14_42_w12
def endpoint_14_42 : CertifiedEndpoint :=
  ⟨⟨14, 42, 3309⟩, 227000649162690181, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_42_flag endpoint_14_42_sources 13 227000649162690181 227000649162690181 rfl endpoint_14_42_base endpoint_14_42_p13) (by decide)⟩
private def endpoint_14_43_flag : Flag := ⟨14, 43, 3279⟩
private def endpoint_14_43_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_43_base : receiptBase endpoint_14_43_flag endpoint_14_43_sources = some 229543727164722672 := by decide +kernel
private theorem endpoint_14_43_w0 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 2 229543727164722672 = some 231739493330686899 := by decide +kernel
private theorem endpoint_14_43_w2 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 2 2 231739493330686899 = some 231739493330686899 := by decide +kernel
private theorem endpoint_14_43_p4 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 4 229543727164722672 = some 231739493330686899 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 2 2 229543727164722672 231739493330686899 231739493330686899 endpoint_14_43_w0 endpoint_14_43_w2
private theorem endpoint_14_43_w4 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 4 2 231739493330686899 = some 231739493330686899 := by decide +kernel
private theorem endpoint_14_43_p6 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 6 229543727164722672 = some 231739493330686899 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 4 2 229543727164722672 231739493330686899 231739493330686899 endpoint_14_43_p4 endpoint_14_43_w4
private theorem endpoint_14_43_w6 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 6 2 231739493330686899 = some 231739493330686899 := by decide +kernel
private theorem endpoint_14_43_p8 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 8 229543727164722672 = some 231739493330686899 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 6 2 229543727164722672 231739493330686899 231739493330686899 endpoint_14_43_p6 endpoint_14_43_w6
private theorem endpoint_14_43_w8 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 8 2 231739493330686899 = some 231739493330686899 := by decide +kernel
private theorem endpoint_14_43_p10 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 10 229543727164722672 = some 231739493330686899 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 8 2 229543727164722672 231739493330686899 231739493330686899 endpoint_14_43_p8 endpoint_14_43_w8
private theorem endpoint_14_43_w10 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 10 2 231739493330686899 = some 231739493330686899 := by decide +kernel
private theorem endpoint_14_43_p12 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 12 229543727164722672 = some 231739493330686899 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 10 2 229543727164722672 231739493330686899 231739493330686899 endpoint_14_43_p10 endpoint_14_43_w10
private theorem endpoint_14_43_w12 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 12 1 231739493330686899 = some 231739493330686899 := by decide +kernel
private theorem endpoint_14_43_p13 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 13 229543727164722672 = some 231739493330686899 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 12 1 229543727164722672 231739493330686899 231739493330686899 endpoint_14_43_p12 endpoint_14_43_w12
def endpoint_14_43 : CertifiedEndpoint :=
  ⟨⟨14, 43, 3279⟩, 231739493330686899, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_43_flag endpoint_14_43_sources 13 229543727164722672 231739493330686899 rfl endpoint_14_43_base endpoint_14_43_p13) (by decide)⟩
private def endpoint_14_44_flag : Flag := ⟨14, 44, 3248⟩
private def endpoint_14_44_sources : Sources := ⟨contact23, contact03, contact25⟩
private theorem endpoint_14_44_base : receiptBase endpoint_14_44_flag endpoint_14_44_sources = some 233204532842273968 := by decide +kernel
private theorem endpoint_14_44_w0 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 2 233204532842273968 = some 235472616919065600 := by decide +kernel
private theorem endpoint_14_44_w2 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 2 2 235472616919065600 = some 235472616919065600 := by decide +kernel
private theorem endpoint_14_44_p4 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 4 233204532842273968 = some 235472616919065600 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 2 2 233204532842273968 235472616919065600 235472616919065600 endpoint_14_44_w0 endpoint_14_44_w2
private theorem endpoint_14_44_w4 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 4 2 235472616919065600 = some 235472616919065600 := by decide +kernel
private theorem endpoint_14_44_p6 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 6 233204532842273968 = some 235472616919065600 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 4 2 233204532842273968 235472616919065600 235472616919065600 endpoint_14_44_p4 endpoint_14_44_w4
private theorem endpoint_14_44_w6 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 6 2 235472616919065600 = some 235472616919065600 := by decide +kernel
private theorem endpoint_14_44_p8 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 8 233204532842273968 = some 235472616919065600 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 6 2 233204532842273968 235472616919065600 235472616919065600 endpoint_14_44_p6 endpoint_14_44_w6
private theorem endpoint_14_44_w8 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 8 2 235472616919065600 = some 235472616919065600 := by decide +kernel
private theorem endpoint_14_44_p10 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 10 233204532842273968 = some 235472616919065600 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 8 2 233204532842273968 235472616919065600 235472616919065600 endpoint_14_44_p8 endpoint_14_44_w8
private theorem endpoint_14_44_w10 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 10 2 235472616919065600 = some 235472616919065600 := by decide +kernel
private theorem endpoint_14_44_p12 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 12 233204532842273968 = some 235472616919065600 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 10 2 233204532842273968 235472616919065600 235472616919065600 endpoint_14_44_p10 endpoint_14_44_w10
private theorem endpoint_14_44_w12 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 12 1 235472616919065600 = some 235472616919065600 := by decide +kernel
private theorem endpoint_14_44_p13 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 13 233204532842273968 = some 235472616919065600 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 12 1 233204532842273968 235472616919065600 235472616919065600 endpoint_14_44_p12 endpoint_14_44_w12
def endpoint_14_44 : CertifiedEndpoint :=
  ⟨⟨14, 44, 3248⟩, 235472616919065600, .terminal ⟨contact23, contact03, contact25⟩ (finish_receipt_window endpoint_14_44_flag endpoint_14_44_sources 13 233204532842273968 235472616919065600 rfl endpoint_14_44_base endpoint_14_44_p13) (by decide)⟩
private def endpoint_14_45_flag : Flag := ⟨14, 45, 3216⟩
private def endpoint_14_45_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_45_base : receiptBase endpoint_14_45_flag endpoint_14_45_sources = some 236582763007359245 := by decide +kernel
private theorem endpoint_14_45_w0 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 2 236582763007359245 = some 236582763007359245 := by decide +kernel
private theorem endpoint_14_45_w2 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 2 2 236582763007359245 = some 236582763007359245 := by decide +kernel
private theorem endpoint_14_45_p4 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 4 236582763007359245 = some 236582763007359245 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 2 2 236582763007359245 236582763007359245 236582763007359245 endpoint_14_45_w0 endpoint_14_45_w2
private theorem endpoint_14_45_w4 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 4 2 236582763007359245 = some 236582763007359245 := by decide +kernel
private theorem endpoint_14_45_p6 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 6 236582763007359245 = some 236582763007359245 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 4 2 236582763007359245 236582763007359245 236582763007359245 endpoint_14_45_p4 endpoint_14_45_w4
private theorem endpoint_14_45_w6 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 6 2 236582763007359245 = some 236582763007359245 := by decide +kernel
private theorem endpoint_14_45_p8 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 8 236582763007359245 = some 236582763007359245 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 6 2 236582763007359245 236582763007359245 236582763007359245 endpoint_14_45_p6 endpoint_14_45_w6
private theorem endpoint_14_45_w8 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 8 2 236582763007359245 = some 236582763007359245 := by decide +kernel
private theorem endpoint_14_45_p10 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 10 236582763007359245 = some 236582763007359245 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 8 2 236582763007359245 236582763007359245 236582763007359245 endpoint_14_45_p8 endpoint_14_45_w8
private theorem endpoint_14_45_w10 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 10 2 236582763007359245 = some 236582763007359245 := by decide +kernel
private theorem endpoint_14_45_p12 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 12 236582763007359245 = some 236582763007359245 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 10 2 236582763007359245 236582763007359245 236582763007359245 endpoint_14_45_p10 endpoint_14_45_w10
private theorem endpoint_14_45_w12 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 12 1 236582763007359245 = some 236582763007359245 := by decide +kernel
private theorem endpoint_14_45_p13 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 13 236582763007359245 = some 236582763007359245 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 12 1 236582763007359245 236582763007359245 236582763007359245 endpoint_14_45_p12 endpoint_14_45_w12
def endpoint_14_45 : CertifiedEndpoint :=
  ⟨⟨14, 45, 3216⟩, 236582763007359245, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_45_flag endpoint_14_45_sources 13 236582763007359245 236582763007359245 rfl endpoint_14_45_base endpoint_14_45_p13) (by decide)⟩
private def endpoint_14_46_flag : Flag := ⟨14, 46, 3183⟩
private def endpoint_14_46_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_46_base : receiptBase endpoint_14_46_flag endpoint_14_46_sources = some 238596994973246507 := by decide +kernel
private theorem endpoint_14_46_w0 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 2 238596994973246507 = some 240675685984922670 := by decide +kernel
private theorem endpoint_14_46_w2 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 2 2 240675685984922670 = some 240675685984922670 := by decide +kernel
private theorem endpoint_14_46_p4 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 4 238596994973246507 = some 240675685984922670 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 2 2 238596994973246507 240675685984922670 240675685984922670 endpoint_14_46_w0 endpoint_14_46_w2
private theorem endpoint_14_46_w4 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 4 2 240675685984922670 = some 240675685984922670 := by decide +kernel
private theorem endpoint_14_46_p6 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 6 238596994973246507 = some 240675685984922670 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 4 2 238596994973246507 240675685984922670 240675685984922670 endpoint_14_46_p4 endpoint_14_46_w4
private theorem endpoint_14_46_w6 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 6 2 240675685984922670 = some 240675685984922670 := by decide +kernel
private theorem endpoint_14_46_p8 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 8 238596994973246507 = some 240675685984922670 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 6 2 238596994973246507 240675685984922670 240675685984922670 endpoint_14_46_p6 endpoint_14_46_w6
private theorem endpoint_14_46_w8 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 8 2 240675685984922670 = some 240675685984922670 := by decide +kernel
private theorem endpoint_14_46_p10 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 10 238596994973246507 = some 240675685984922670 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 8 2 238596994973246507 240675685984922670 240675685984922670 endpoint_14_46_p8 endpoint_14_46_w8
private theorem endpoint_14_46_w10 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 10 2 240675685984922670 = some 240675685984922670 := by decide +kernel
private theorem endpoint_14_46_p12 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 12 238596994973246507 = some 240675685984922670 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 10 2 238596994973246507 240675685984922670 240675685984922670 endpoint_14_46_p10 endpoint_14_46_w10
private theorem endpoint_14_46_w12 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 12 1 240675685984922670 = some 240675685984922670 := by decide +kernel
private theorem endpoint_14_46_p13 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 13 238596994973246507 = some 240675685984922670 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 12 1 238596994973246507 240675685984922670 240675685984922670 endpoint_14_46_p12 endpoint_14_46_w12
def endpoint_14_46 : CertifiedEndpoint :=
  ⟨⟨14, 46, 3183⟩, 240675685984922670, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_46_flag endpoint_14_46_sources 13 238596994973246507 240675685984922670 rfl endpoint_14_46_base endpoint_14_46_p13) (by decide)⟩
private def endpoint_14_47_flag : Flag := ⟨14, 47, 3150⟩
private def endpoint_14_47_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_47_base : receiptBase endpoint_14_47_flag endpoint_14_47_sources = some 240519899133376284 := by decide +kernel
private theorem endpoint_14_47_w0 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 2 240519899133376284 = some 245592394765853247 := by decide +kernel
private theorem endpoint_14_47_w2 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 2 2 245592394765853247 = some 245592394765853247 := by decide +kernel
private theorem endpoint_14_47_p4 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 4 240519899133376284 = some 245592394765853247 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 2 2 240519899133376284 245592394765853247 245592394765853247 endpoint_14_47_w0 endpoint_14_47_w2
private theorem endpoint_14_47_w4 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 4 2 245592394765853247 = some 245592394765853247 := by decide +kernel
private theorem endpoint_14_47_p6 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 6 240519899133376284 = some 245592394765853247 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 4 2 240519899133376284 245592394765853247 245592394765853247 endpoint_14_47_p4 endpoint_14_47_w4
private theorem endpoint_14_47_w6 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 6 2 245592394765853247 = some 245592394765853247 := by decide +kernel
private theorem endpoint_14_47_p8 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 8 240519899133376284 = some 245592394765853247 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 6 2 240519899133376284 245592394765853247 245592394765853247 endpoint_14_47_p6 endpoint_14_47_w6
private theorem endpoint_14_47_w8 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 8 2 245592394765853247 = some 245592394765853247 := by decide +kernel
private theorem endpoint_14_47_p10 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 10 240519899133376284 = some 245592394765853247 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 8 2 240519899133376284 245592394765853247 245592394765853247 endpoint_14_47_p8 endpoint_14_47_w8
private theorem endpoint_14_47_w10 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 10 2 245592394765853247 = some 245592394765853247 := by decide +kernel
private theorem endpoint_14_47_p12 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 12 240519899133376284 = some 245592394765853247 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 10 2 240519899133376284 245592394765853247 245592394765853247 endpoint_14_47_p10 endpoint_14_47_w10
private theorem endpoint_14_47_w12 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 12 1 245592394765853247 = some 245592394765853247 := by decide +kernel
private theorem endpoint_14_47_p13 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 13 240519899133376284 = some 245592394765853247 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 12 1 240519899133376284 245592394765853247 245592394765853247 endpoint_14_47_p12 endpoint_14_47_w12
def endpoint_14_47 : CertifiedEndpoint :=
  ⟨⟨14, 47, 3150⟩, 245592394765853247, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_47_flag endpoint_14_47_sources 13 240519899133376284 245592394765853247 rfl endpoint_14_47_base endpoint_14_47_p13) (by decide)⟩
private def endpoint_14_48_flag : Flag := ⟨14, 48, 3116⟩
private def endpoint_14_48_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_48_base : receiptBase endpoint_14_48_flag endpoint_14_48_sources = some 243034747188593979 := by decide +kernel
private theorem endpoint_14_48_w0 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 2 243034747188593979 = some 243130250749265948 := by decide +kernel
private theorem endpoint_14_48_w2 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 2 2 243130250749265948 = some 243130250749265948 := by decide +kernel
private theorem endpoint_14_48_p4 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 4 243034747188593979 = some 243130250749265948 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 2 2 243034747188593979 243130250749265948 243130250749265948 endpoint_14_48_w0 endpoint_14_48_w2
private theorem endpoint_14_48_w4 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 4 2 243130250749265948 = some 243130250749265948 := by decide +kernel
private theorem endpoint_14_48_p6 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 6 243034747188593979 = some 243130250749265948 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 4 2 243034747188593979 243130250749265948 243130250749265948 endpoint_14_48_p4 endpoint_14_48_w4
private theorem endpoint_14_48_w6 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 6 2 243130250749265948 = some 243130250749265948 := by decide +kernel
private theorem endpoint_14_48_p8 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 8 243034747188593979 = some 243130250749265948 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 6 2 243034747188593979 243130250749265948 243130250749265948 endpoint_14_48_p6 endpoint_14_48_w6
private theorem endpoint_14_48_w8 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 8 2 243130250749265948 = some 243130250749265948 := by decide +kernel
private theorem endpoint_14_48_p10 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 10 243034747188593979 = some 243130250749265948 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 8 2 243034747188593979 243130250749265948 243130250749265948 endpoint_14_48_p8 endpoint_14_48_w8
private theorem endpoint_14_48_w10 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 10 2 243130250749265948 = some 243130250749265948 := by decide +kernel
private theorem endpoint_14_48_p12 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 12 243034747188593979 = some 243130250749265948 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 10 2 243034747188593979 243130250749265948 243130250749265948 endpoint_14_48_p10 endpoint_14_48_w10
private theorem endpoint_14_48_w12 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 12 1 243130250749265948 = some 243130250749265948 := by decide +kernel
private theorem endpoint_14_48_p13 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 13 243034747188593979 = some 243130250749265948 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 12 1 243034747188593979 243130250749265948 243130250749265948 endpoint_14_48_p12 endpoint_14_48_w12
def endpoint_14_48 : CertifiedEndpoint :=
  ⟨⟨14, 48, 3116⟩, 243130250749265948, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_48_flag endpoint_14_48_sources 13 243034747188593979 243130250749265948 rfl endpoint_14_48_base endpoint_14_48_p13) (by decide)⟩
private def endpoint_14_49_flag : Flag := ⟨14, 49, 3081⟩
private def endpoint_14_49_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_49_base : receiptBase endpoint_14_49_flag endpoint_14_49_sources = some 244629121235945888 := by decide +kernel
private theorem endpoint_14_49_w0 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 2 244629121235945888 = some 247633429683162591 := by decide +kernel
private theorem endpoint_14_49_w2 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 2 2 247633429683162591 = some 247633429683162591 := by decide +kernel
private theorem endpoint_14_49_p4 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 4 244629121235945888 = some 247633429683162591 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 2 2 244629121235945888 247633429683162591 247633429683162591 endpoint_14_49_w0 endpoint_14_49_w2
private theorem endpoint_14_49_w4 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 4 2 247633429683162591 = some 247633429683162591 := by decide +kernel
private theorem endpoint_14_49_p6 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 6 244629121235945888 = some 247633429683162591 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 4 2 244629121235945888 247633429683162591 247633429683162591 endpoint_14_49_p4 endpoint_14_49_w4
private theorem endpoint_14_49_w6 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 6 2 247633429683162591 = some 247633429683162591 := by decide +kernel
private theorem endpoint_14_49_p8 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 8 244629121235945888 = some 247633429683162591 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 6 2 244629121235945888 247633429683162591 247633429683162591 endpoint_14_49_p6 endpoint_14_49_w6
private theorem endpoint_14_49_w8 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 8 2 247633429683162591 = some 247633429683162591 := by decide +kernel
private theorem endpoint_14_49_p10 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 10 244629121235945888 = some 247633429683162591 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 8 2 244629121235945888 247633429683162591 247633429683162591 endpoint_14_49_p8 endpoint_14_49_w8
private theorem endpoint_14_49_w10 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 10 2 247633429683162591 = some 247633429683162591 := by decide +kernel
private theorem endpoint_14_49_p12 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 12 244629121235945888 = some 247633429683162591 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 10 2 244629121235945888 247633429683162591 247633429683162591 endpoint_14_49_p10 endpoint_14_49_w10
private theorem endpoint_14_49_w12 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 12 1 247633429683162591 = some 247633429683162591 := by decide +kernel
private theorem endpoint_14_49_p13 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 13 244629121235945888 = some 247633429683162591 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 12 1 244629121235945888 247633429683162591 247633429683162591 endpoint_14_49_p12 endpoint_14_49_w12
def endpoint_14_49 : CertifiedEndpoint :=
  ⟨⟨14, 49, 3081⟩, 247633429683162591, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_49_flag endpoint_14_49_sources 13 244629121235945888 247633429683162591 rfl endpoint_14_49_base endpoint_14_49_p13) (by decide)⟩
private def endpoint_14_50_flag : Flag := ⟨14, 50, 3045⟩
private def endpoint_14_50_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_50_base : receiptBase endpoint_14_50_flag endpoint_14_50_sources = some 246046402397758126 := by decide +kernel
private theorem endpoint_14_50_w0 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 2 246046402397758126 = some 252015281301326784 := by decide +kernel
private theorem endpoint_14_50_w2 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 2 2 252015281301326784 = some 252015281301326784 := by decide +kernel
private theorem endpoint_14_50_p4 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 4 246046402397758126 = some 252015281301326784 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 2 2 246046402397758126 252015281301326784 252015281301326784 endpoint_14_50_w0 endpoint_14_50_w2
private theorem endpoint_14_50_w4 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 4 2 252015281301326784 = some 252015281301326784 := by decide +kernel
private theorem endpoint_14_50_p6 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 6 246046402397758126 = some 252015281301326784 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 4 2 246046402397758126 252015281301326784 252015281301326784 endpoint_14_50_p4 endpoint_14_50_w4
private theorem endpoint_14_50_w6 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 6 2 252015281301326784 = some 252015281301326784 := by decide +kernel
private theorem endpoint_14_50_p8 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 8 246046402397758126 = some 252015281301326784 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 6 2 246046402397758126 252015281301326784 252015281301326784 endpoint_14_50_p6 endpoint_14_50_w6
private theorem endpoint_14_50_w8 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 8 2 252015281301326784 = some 252015281301326784 := by decide +kernel
private theorem endpoint_14_50_p10 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 10 246046402397758126 = some 252015281301326784 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 8 2 246046402397758126 252015281301326784 252015281301326784 endpoint_14_50_p8 endpoint_14_50_w8
private theorem endpoint_14_50_w10 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 10 2 252015281301326784 = some 252015281301326784 := by decide +kernel
private theorem endpoint_14_50_p12 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 12 246046402397758126 = some 252015281301326784 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 10 2 246046402397758126 252015281301326784 252015281301326784 endpoint_14_50_p10 endpoint_14_50_w10
private theorem endpoint_14_50_w12 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 12 1 252015281301326784 = some 252015281301326784 := by decide +kernel
private theorem endpoint_14_50_p13 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 13 246046402397758126 = some 252015281301326784 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 12 1 246046402397758126 252015281301326784 252015281301326784 endpoint_14_50_p12 endpoint_14_50_w12
def endpoint_14_50 : CertifiedEndpoint :=
  ⟨⟨14, 50, 3045⟩, 252015281301326784, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_50_flag endpoint_14_50_sources 13 246046402397758126 252015281301326784 rfl endpoint_14_50_base endpoint_14_50_p13) (by decide)⟩
private def endpoint_14_51_flag : Flag := ⟨14, 51, 3009⟩
private def endpoint_14_51_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_51_base : receiptBase endpoint_14_51_flag endpoint_14_51_sources = some 247363520091122972 := by decide +kernel
private theorem endpoint_14_51_w0 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 2 247363520091122972 = some 256317828642249487 := by decide +kernel
private theorem endpoint_14_51_w2 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 2 2 256317828642249487 = some 256317828642249487 := by decide +kernel
private theorem endpoint_14_51_p4 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 4 247363520091122972 = some 256317828642249487 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 2 2 247363520091122972 256317828642249487 256317828642249487 endpoint_14_51_w0 endpoint_14_51_w2
private theorem endpoint_14_51_w4 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 4 2 256317828642249487 = some 256317828642249487 := by decide +kernel
private theorem endpoint_14_51_p6 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 6 247363520091122972 = some 256317828642249487 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 4 2 247363520091122972 256317828642249487 256317828642249487 endpoint_14_51_p4 endpoint_14_51_w4
private theorem endpoint_14_51_w6 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 6 2 256317828642249487 = some 256317828642249487 := by decide +kernel
private theorem endpoint_14_51_p8 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 8 247363520091122972 = some 256317828642249487 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 6 2 247363520091122972 256317828642249487 256317828642249487 endpoint_14_51_p6 endpoint_14_51_w6
private theorem endpoint_14_51_w8 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 8 2 256317828642249487 = some 256317828642249487 := by decide +kernel
private theorem endpoint_14_51_p10 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 10 247363520091122972 = some 256317828642249487 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 8 2 247363520091122972 256317828642249487 256317828642249487 endpoint_14_51_p8 endpoint_14_51_w8
private theorem endpoint_14_51_w10 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 10 2 256317828642249487 = some 256317828642249487 := by decide +kernel
private theorem endpoint_14_51_p12 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 12 247363520091122972 = some 256317828642249487 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 10 2 247363520091122972 256317828642249487 256317828642249487 endpoint_14_51_p10 endpoint_14_51_w10
private theorem endpoint_14_51_w12 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 12 1 256317828642249487 = some 256317828642249487 := by decide +kernel
private theorem endpoint_14_51_p13 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 13 247363520091122972 = some 256317828642249487 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 12 1 247363520091122972 256317828642249487 256317828642249487 endpoint_14_51_p12 endpoint_14_51_w12
def endpoint_14_51 : CertifiedEndpoint :=
  ⟨⟨14, 51, 3009⟩, 256317828642249487, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_51_flag endpoint_14_51_sources 13 247363520091122972 256317828642249487 rfl endpoint_14_51_base endpoint_14_51_p13) (by decide)⟩
private def endpoint_14_52_flag : Flag := ⟨14, 52, 2971⟩
private def endpoint_14_52_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_52_base : receiptBase endpoint_14_52_flag endpoint_14_52_sources = some 248415638663395878 := by decide +kernel
private theorem endpoint_14_52_w0 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 2 248415638663395878 = some 260448572919923764 := by decide +kernel
private theorem endpoint_14_52_w2 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 2 2 260448572919923764 = some 260448572919923764 := by decide +kernel
private theorem endpoint_14_52_p4 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 4 248415638663395878 = some 260448572919923764 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 2 2 248415638663395878 260448572919923764 260448572919923764 endpoint_14_52_w0 endpoint_14_52_w2
private theorem endpoint_14_52_w4 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 4 2 260448572919923764 = some 260448572919923764 := by decide +kernel
private theorem endpoint_14_52_p6 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 6 248415638663395878 = some 260448572919923764 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 4 2 248415638663395878 260448572919923764 260448572919923764 endpoint_14_52_p4 endpoint_14_52_w4
private theorem endpoint_14_52_w6 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 6 2 260448572919923764 = some 260448572919923764 := by decide +kernel
private theorem endpoint_14_52_p8 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 8 248415638663395878 = some 260448572919923764 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 6 2 248415638663395878 260448572919923764 260448572919923764 endpoint_14_52_p6 endpoint_14_52_w6
private theorem endpoint_14_52_w8 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 8 2 260448572919923764 = some 260448572919923764 := by decide +kernel
private theorem endpoint_14_52_p10 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 10 248415638663395878 = some 260448572919923764 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 8 2 248415638663395878 260448572919923764 260448572919923764 endpoint_14_52_p8 endpoint_14_52_w8
private theorem endpoint_14_52_w10 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 10 2 260448572919923764 = some 260448572919923764 := by decide +kernel
private theorem endpoint_14_52_p12 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 12 248415638663395878 = some 260448572919923764 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 10 2 248415638663395878 260448572919923764 260448572919923764 endpoint_14_52_p10 endpoint_14_52_w10
private theorem endpoint_14_52_w12 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 12 1 260448572919923764 = some 260448572919923764 := by decide +kernel
private theorem endpoint_14_52_p13 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 13 248415638663395878 = some 260448572919923764 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 12 1 248415638663395878 260448572919923764 260448572919923764 endpoint_14_52_p12 endpoint_14_52_w12
def endpoint_14_52 : CertifiedEndpoint :=
  ⟨⟨14, 52, 2971⟩, 260448572919923764, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_52_flag endpoint_14_52_sources 13 248415638663395878 260448572919923764 rfl endpoint_14_52_base endpoint_14_52_p13) (by decide)⟩
private def endpoint_14_53_flag : Flag := ⟨14, 53, 2932⟩
private def endpoint_14_53_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_14_53_base : receiptBase endpoint_14_53_flag endpoint_14_53_sources = some 250143919960568892 := by decide +kernel
private theorem endpoint_14_53_w0 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 2 250143919960568892 = some 258643884593848119 := by decide +kernel
private theorem endpoint_14_53_w2 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 2 2 258643884593848119 = some 258643884593848119 := by decide +kernel
private theorem endpoint_14_53_p4 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 4 250143919960568892 = some 258643884593848119 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 2 2 250143919960568892 258643884593848119 258643884593848119 endpoint_14_53_w0 endpoint_14_53_w2
private theorem endpoint_14_53_w4 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 4 2 258643884593848119 = some 258643884593848119 := by decide +kernel
private theorem endpoint_14_53_p6 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 6 250143919960568892 = some 258643884593848119 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 4 2 250143919960568892 258643884593848119 258643884593848119 endpoint_14_53_p4 endpoint_14_53_w4
private theorem endpoint_14_53_w6 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 6 2 258643884593848119 = some 258643884593848119 := by decide +kernel
private theorem endpoint_14_53_p8 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 8 250143919960568892 = some 258643884593848119 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 6 2 250143919960568892 258643884593848119 258643884593848119 endpoint_14_53_p6 endpoint_14_53_w6
private theorem endpoint_14_53_w8 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 8 2 258643884593848119 = some 258643884593848119 := by decide +kernel
private theorem endpoint_14_53_p10 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 10 250143919960568892 = some 258643884593848119 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 8 2 250143919960568892 258643884593848119 258643884593848119 endpoint_14_53_p8 endpoint_14_53_w8
private theorem endpoint_14_53_w10 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 10 2 258643884593848119 = some 258643884593848119 := by decide +kernel
private theorem endpoint_14_53_p12 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 12 250143919960568892 = some 258643884593848119 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 10 2 250143919960568892 258643884593848119 258643884593848119 endpoint_14_53_p10 endpoint_14_53_w10
private theorem endpoint_14_53_w12 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 12 1 258643884593848119 = some 258643884593848119 := by decide +kernel
private theorem endpoint_14_53_p13 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 13 250143919960568892 = some 258643884593848119 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 12 1 250143919960568892 258643884593848119 258643884593848119 endpoint_14_53_p12 endpoint_14_53_w12
def endpoint_14_53 : CertifiedEndpoint :=
  ⟨⟨14, 53, 2932⟩, 258643884593848119, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_14_53_flag endpoint_14_53_sources 13 250143919960568892 258643884593848119 rfl endpoint_14_53_base endpoint_14_53_p13) (by decide)⟩
private def endpoint_14_54_flag : Flag := ⟨14, 54, 2892⟩
private def endpoint_14_54_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_54_base : receiptBase endpoint_14_54_flag endpoint_14_54_sources = some 253550024173933867 := by decide +kernel
private theorem endpoint_14_54_w0 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 2 253550024173933867 = some 253550024173933867 := by decide +kernel
private theorem endpoint_14_54_w2 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 2 2 253550024173933867 = some 253550024173933867 := by decide +kernel
private theorem endpoint_14_54_p4 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 4 253550024173933867 = some 253550024173933867 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 2 2 253550024173933867 253550024173933867 253550024173933867 endpoint_14_54_w0 endpoint_14_54_w2
private theorem endpoint_14_54_w4 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 4 2 253550024173933867 = some 253550024173933867 := by decide +kernel
private theorem endpoint_14_54_p6 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 6 253550024173933867 = some 253550024173933867 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 4 2 253550024173933867 253550024173933867 253550024173933867 endpoint_14_54_p4 endpoint_14_54_w4
private theorem endpoint_14_54_w6 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 6 2 253550024173933867 = some 253550024173933867 := by decide +kernel
private theorem endpoint_14_54_p8 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 8 253550024173933867 = some 253550024173933867 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 6 2 253550024173933867 253550024173933867 253550024173933867 endpoint_14_54_p6 endpoint_14_54_w6
private theorem endpoint_14_54_w8 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 8 2 253550024173933867 = some 253550024173933867 := by decide +kernel
private theorem endpoint_14_54_p10 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 10 253550024173933867 = some 253550024173933867 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 8 2 253550024173933867 253550024173933867 253550024173933867 endpoint_14_54_p8 endpoint_14_54_w8
private theorem endpoint_14_54_w10 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 10 2 253550024173933867 = some 253550024173933867 := by decide +kernel
private theorem endpoint_14_54_p12 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 12 253550024173933867 = some 253550024173933867 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 10 2 253550024173933867 253550024173933867 253550024173933867 endpoint_14_54_p10 endpoint_14_54_w10
private theorem endpoint_14_54_w12 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 12 1 253550024173933867 = some 253550024173933867 := by decide +kernel
private theorem endpoint_14_54_p13 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 13 253550024173933867 = some 253550024173933867 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 12 1 253550024173933867 253550024173933867 253550024173933867 endpoint_14_54_p12 endpoint_14_54_w12
def endpoint_14_54 : CertifiedEndpoint :=
  ⟨⟨14, 54, 2892⟩, 253550024173933867, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_54_flag endpoint_14_54_sources 13 253550024173933867 253550024173933867 rfl endpoint_14_54_base endpoint_14_54_p13) (by decide)⟩
private def endpoint_14_55_flag : Flag := ⟨14, 55, 2851⟩
private def endpoint_14_55_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_55_base : receiptBase endpoint_14_55_flag endpoint_14_55_sources = some 254051540897526328 := by decide +kernel
private theorem endpoint_14_55_w0 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 2 254051540897526328 = some 254051540897526328 := by decide +kernel
private theorem endpoint_14_55_w2 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 2 2 254051540897526328 = some 254051540897526328 := by decide +kernel
private theorem endpoint_14_55_p4 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 4 254051540897526328 = some 254051540897526328 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 2 2 254051540897526328 254051540897526328 254051540897526328 endpoint_14_55_w0 endpoint_14_55_w2
private theorem endpoint_14_55_w4 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 4 2 254051540897526328 = some 254051540897526328 := by decide +kernel
private theorem endpoint_14_55_p6 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 6 254051540897526328 = some 254051540897526328 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 4 2 254051540897526328 254051540897526328 254051540897526328 endpoint_14_55_p4 endpoint_14_55_w4
private theorem endpoint_14_55_w6 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 6 2 254051540897526328 = some 254051540897526328 := by decide +kernel
private theorem endpoint_14_55_p8 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 8 254051540897526328 = some 254051540897526328 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 6 2 254051540897526328 254051540897526328 254051540897526328 endpoint_14_55_p6 endpoint_14_55_w6
private theorem endpoint_14_55_w8 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 8 2 254051540897526328 = some 254051540897526328 := by decide +kernel
private theorem endpoint_14_55_p10 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 10 254051540897526328 = some 254051540897526328 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 8 2 254051540897526328 254051540897526328 254051540897526328 endpoint_14_55_p8 endpoint_14_55_w8
private theorem endpoint_14_55_w10 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 10 2 254051540897526328 = some 254051540897526328 := by decide +kernel
private theorem endpoint_14_55_p12 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 12 254051540897526328 = some 254051540897526328 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 10 2 254051540897526328 254051540897526328 254051540897526328 endpoint_14_55_p10 endpoint_14_55_w10
private theorem endpoint_14_55_w12 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 12 1 254051540897526328 = some 254051540897526328 := by decide +kernel
private theorem endpoint_14_55_p13 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 13 254051540897526328 = some 254051540897526328 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 12 1 254051540897526328 254051540897526328 254051540897526328 endpoint_14_55_p12 endpoint_14_55_w12
def endpoint_14_55 : CertifiedEndpoint :=
  ⟨⟨14, 55, 2851⟩, 254051540897526328, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_55_flag endpoint_14_55_sources 13 254051540897526328 254051540897526328 rfl endpoint_14_55_base endpoint_14_55_p13) (by decide)⟩
private def endpoint_14_56_flag : Flag := ⟨14, 56, 2809⟩
private def endpoint_14_56_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_56_base : receiptBase endpoint_14_56_flag endpoint_14_56_sources = some 254346780019209154 := by decide +kernel
private theorem endpoint_14_56_w0 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 2 254346780019209154 = some 255385225562848848 := by decide +kernel
private theorem endpoint_14_56_w2 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 2 2 255385225562848848 = some 255385225562848848 := by decide +kernel
private theorem endpoint_14_56_p4 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 4 254346780019209154 = some 255385225562848848 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 2 2 254346780019209154 255385225562848848 255385225562848848 endpoint_14_56_w0 endpoint_14_56_w2
private theorem endpoint_14_56_w4 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 4 2 255385225562848848 = some 255385225562848848 := by decide +kernel
private theorem endpoint_14_56_p6 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 6 254346780019209154 = some 255385225562848848 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 4 2 254346780019209154 255385225562848848 255385225562848848 endpoint_14_56_p4 endpoint_14_56_w4
private theorem endpoint_14_56_w6 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 6 2 255385225562848848 = some 255385225562848848 := by decide +kernel
private theorem endpoint_14_56_p8 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 8 254346780019209154 = some 255385225562848848 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 6 2 254346780019209154 255385225562848848 255385225562848848 endpoint_14_56_p6 endpoint_14_56_w6
private theorem endpoint_14_56_w8 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 8 2 255385225562848848 = some 255385225562848848 := by decide +kernel
private theorem endpoint_14_56_p10 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 10 254346780019209154 = some 255385225562848848 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 8 2 254346780019209154 255385225562848848 255385225562848848 endpoint_14_56_p8 endpoint_14_56_w8
private theorem endpoint_14_56_w10 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 10 2 255385225562848848 = some 255385225562848848 := by decide +kernel
private theorem endpoint_14_56_p12 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 12 254346780019209154 = some 255385225562848848 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 10 2 254346780019209154 255385225562848848 255385225562848848 endpoint_14_56_p10 endpoint_14_56_w10
private theorem endpoint_14_56_w12 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 12 1 255385225562848848 = some 255385225562848848 := by decide +kernel
private theorem endpoint_14_56_p13 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 13 254346780019209154 = some 255385225562848848 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 12 1 254346780019209154 255385225562848848 255385225562848848 endpoint_14_56_p12 endpoint_14_56_w12
def endpoint_14_56 : CertifiedEndpoint :=
  ⟨⟨14, 56, 2809⟩, 255385225562848848, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_56_flag endpoint_14_56_sources 13 254346780019209154 255385225562848848 rfl endpoint_14_56_base endpoint_14_56_p13) (by decide)⟩
private def endpoint_14_57_flag : Flag := ⟨14, 57, 2765⟩
private def endpoint_14_57_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_57_base : receiptBase endpoint_14_57_flag endpoint_14_57_sources = some 254340704009736922 := by decide +kernel
private theorem endpoint_14_57_w0 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 2 254340704009736922 = some 258359108452680980 := by decide +kernel
private theorem endpoint_14_57_w2 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 2 2 258359108452680980 = some 258359108452680980 := by decide +kernel
private theorem endpoint_14_57_p4 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 4 254340704009736922 = some 258359108452680980 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 2 2 254340704009736922 258359108452680980 258359108452680980 endpoint_14_57_w0 endpoint_14_57_w2
private theorem endpoint_14_57_w4 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 4 2 258359108452680980 = some 258359108452680980 := by decide +kernel
private theorem endpoint_14_57_p6 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 6 254340704009736922 = some 258359108452680980 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 4 2 254340704009736922 258359108452680980 258359108452680980 endpoint_14_57_p4 endpoint_14_57_w4
private theorem endpoint_14_57_w6 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 6 2 258359108452680980 = some 258359108452680980 := by decide +kernel
private theorem endpoint_14_57_p8 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 8 254340704009736922 = some 258359108452680980 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 6 2 254340704009736922 258359108452680980 258359108452680980 endpoint_14_57_p6 endpoint_14_57_w6
private theorem endpoint_14_57_w8 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 8 2 258359108452680980 = some 258359108452680980 := by decide +kernel
private theorem endpoint_14_57_p10 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 10 254340704009736922 = some 258359108452680980 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 8 2 254340704009736922 258359108452680980 258359108452680980 endpoint_14_57_p8 endpoint_14_57_w8
private theorem endpoint_14_57_w10 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 10 2 258359108452680980 = some 258359108452680980 := by decide +kernel
private theorem endpoint_14_57_p12 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 12 254340704009736922 = some 258359108452680980 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 10 2 254340704009736922 258359108452680980 258359108452680980 endpoint_14_57_p10 endpoint_14_57_w10
private theorem endpoint_14_57_w12 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 12 1 258359108452680980 = some 258359108452680980 := by decide +kernel
private theorem endpoint_14_57_p13 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 13 254340704009736922 = some 258359108452680980 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 12 1 254340704009736922 258359108452680980 258359108452680980 endpoint_14_57_p12 endpoint_14_57_w12
def endpoint_14_57 : CertifiedEndpoint :=
  ⟨⟨14, 57, 2765⟩, 258359108452680980, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_57_flag endpoint_14_57_sources 13 254340704009736922 258359108452680980 rfl endpoint_14_57_base endpoint_14_57_p13) (by decide)⟩
private def endpoint_14_58_flag : Flag := ⟨14, 58, 2720⟩
private def endpoint_14_58_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_58_base : receiptBase endpoint_14_58_flag endpoint_14_58_sources = some 254117085580870074 := by decide +kernel
private theorem endpoint_14_58_w0 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 2 254117085580870074 = some 261184192722449360 := by decide +kernel
private theorem endpoint_14_58_w2 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 2 2 261184192722449360 = some 261184192722449360 := by decide +kernel
private theorem endpoint_14_58_p4 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 4 254117085580870074 = some 261184192722449360 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 2 2 254117085580870074 261184192722449360 261184192722449360 endpoint_14_58_w0 endpoint_14_58_w2
private theorem endpoint_14_58_w4 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 4 2 261184192722449360 = some 261184192722449360 := by decide +kernel
private theorem endpoint_14_58_p6 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 6 254117085580870074 = some 261184192722449360 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 4 2 254117085580870074 261184192722449360 261184192722449360 endpoint_14_58_p4 endpoint_14_58_w4
private theorem endpoint_14_58_w6 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 6 2 261184192722449360 = some 261184192722449360 := by decide +kernel
private theorem endpoint_14_58_p8 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 8 254117085580870074 = some 261184192722449360 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 6 2 254117085580870074 261184192722449360 261184192722449360 endpoint_14_58_p6 endpoint_14_58_w6
private theorem endpoint_14_58_w8 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 8 2 261184192722449360 = some 261184192722449360 := by decide +kernel
private theorem endpoint_14_58_p10 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 10 254117085580870074 = some 261184192722449360 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 8 2 254117085580870074 261184192722449360 261184192722449360 endpoint_14_58_p8 endpoint_14_58_w8
private theorem endpoint_14_58_w10 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 10 2 261184192722449360 = some 261184192722449360 := by decide +kernel
private theorem endpoint_14_58_p12 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 12 254117085580870074 = some 261184192722449360 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 10 2 254117085580870074 261184192722449360 261184192722449360 endpoint_14_58_p10 endpoint_14_58_w10
private theorem endpoint_14_58_w12 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 12 1 261184192722449360 = some 261184192722449360 := by decide +kernel
private theorem endpoint_14_58_p13 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 13 254117085580870074 = some 261184192722449360 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 12 1 254117085580870074 261184192722449360 261184192722449360 endpoint_14_58_p12 endpoint_14_58_w12
def endpoint_14_58 : CertifiedEndpoint :=
  ⟨⟨14, 58, 2720⟩, 261184192722449360, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_58_flag endpoint_14_58_sources 13 254117085580870074 261184192722449360 rfl endpoint_14_58_base endpoint_14_58_p13) (by decide)⟩
private def endpoint_14_59_flag : Flag := ⟨14, 59, 2673⟩
private def endpoint_14_59_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_59_base : receiptBase endpoint_14_59_flag endpoint_14_59_sources = some 259648929517692520 := by decide +kernel
private theorem endpoint_14_59_w0 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 2 259648929517692520 = some 259648929517692520 := by decide +kernel
private theorem endpoint_14_59_w2 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 2 2 259648929517692520 = some 259648929517692520 := by decide +kernel
private theorem endpoint_14_59_p4 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 4 259648929517692520 = some 259648929517692520 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 2 2 259648929517692520 259648929517692520 259648929517692520 endpoint_14_59_w0 endpoint_14_59_w2
private theorem endpoint_14_59_w4 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 4 2 259648929517692520 = some 259648929517692520 := by decide +kernel
private theorem endpoint_14_59_p6 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 6 259648929517692520 = some 259648929517692520 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 4 2 259648929517692520 259648929517692520 259648929517692520 endpoint_14_59_p4 endpoint_14_59_w4
private theorem endpoint_14_59_w6 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 6 2 259648929517692520 = some 259648929517692520 := by decide +kernel
private theorem endpoint_14_59_p8 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 8 259648929517692520 = some 259648929517692520 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 6 2 259648929517692520 259648929517692520 259648929517692520 endpoint_14_59_p6 endpoint_14_59_w6
private theorem endpoint_14_59_w8 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 8 2 259648929517692520 = some 259648929517692520 := by decide +kernel
private theorem endpoint_14_59_p10 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 10 259648929517692520 = some 259648929517692520 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 8 2 259648929517692520 259648929517692520 259648929517692520 endpoint_14_59_p8 endpoint_14_59_w8
private theorem endpoint_14_59_w10 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 10 2 259648929517692520 = some 259648929517692520 := by decide +kernel
private theorem endpoint_14_59_p12 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 12 259648929517692520 = some 259648929517692520 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 10 2 259648929517692520 259648929517692520 259648929517692520 endpoint_14_59_p10 endpoint_14_59_w10
private theorem endpoint_14_59_w12 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 12 1 259648929517692520 = some 259648929517692520 := by decide +kernel
private theorem endpoint_14_59_p13 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 13 259648929517692520 = some 259648929517692520 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 12 1 259648929517692520 259648929517692520 259648929517692520 endpoint_14_59_p12 endpoint_14_59_w12
def endpoint_14_59 : CertifiedEndpoint :=
  ⟨⟨14, 59, 2673⟩, 259648929517692520, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_59_flag endpoint_14_59_sources 13 259648929517692520 259648929517692520 rfl endpoint_14_59_base endpoint_14_59_p13) (by decide)⟩
private def endpoint_14_60_flag : Flag := ⟨14, 60, 2624⟩
private def endpoint_14_60_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_60_base : receiptBase endpoint_14_60_flag endpoint_14_60_sources = some 258773817712638625 := by decide +kernel
private theorem endpoint_14_60_w0 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 2 258773817712638625 = some 258773817712638625 := by decide +kernel
private theorem endpoint_14_60_w2 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 2 2 258773817712638625 = some 258773817712638625 := by decide +kernel
private theorem endpoint_14_60_p4 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 4 258773817712638625 = some 258773817712638625 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 2 2 258773817712638625 258773817712638625 258773817712638625 endpoint_14_60_w0 endpoint_14_60_w2
private theorem endpoint_14_60_w4 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 4 2 258773817712638625 = some 258773817712638625 := by decide +kernel
private theorem endpoint_14_60_p6 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 6 258773817712638625 = some 258773817712638625 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 4 2 258773817712638625 258773817712638625 258773817712638625 endpoint_14_60_p4 endpoint_14_60_w4
private theorem endpoint_14_60_w6 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 6 2 258773817712638625 = some 258773817712638625 := by decide +kernel
private theorem endpoint_14_60_p8 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 8 258773817712638625 = some 258773817712638625 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 6 2 258773817712638625 258773817712638625 258773817712638625 endpoint_14_60_p6 endpoint_14_60_w6
private theorem endpoint_14_60_w8 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 8 2 258773817712638625 = some 258773817712638625 := by decide +kernel
private theorem endpoint_14_60_p10 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 10 258773817712638625 = some 258773817712638625 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 8 2 258773817712638625 258773817712638625 258773817712638625 endpoint_14_60_p8 endpoint_14_60_w8
private theorem endpoint_14_60_w10 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 10 2 258773817712638625 = some 258773817712638625 := by decide +kernel
private theorem endpoint_14_60_p12 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 12 258773817712638625 = some 258773817712638625 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 10 2 258773817712638625 258773817712638625 258773817712638625 endpoint_14_60_p10 endpoint_14_60_w10
private theorem endpoint_14_60_w12 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 12 1 258773817712638625 = some 258773817712638625 := by decide +kernel
private theorem endpoint_14_60_p13 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 13 258773817712638625 = some 258773817712638625 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 12 1 258773817712638625 258773817712638625 258773817712638625 endpoint_14_60_p12 endpoint_14_60_w12
def endpoint_14_60 : CertifiedEndpoint :=
  ⟨⟨14, 60, 2624⟩, 258773817712638625, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_60_flag endpoint_14_60_sources 13 258773817712638625 258773817712638625 rfl endpoint_14_60_base endpoint_14_60_p13) (by decide)⟩
private def endpoint_14_61_flag : Flag := ⟨14, 61, 2574⟩
private def endpoint_14_61_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_61_base : receiptBase endpoint_14_61_flag endpoint_14_61_sources = some 257661246626932360 := by decide +kernel
private theorem endpoint_14_61_w0 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 2 257661246626932360 = some 257661246626932360 := by decide +kernel
private theorem endpoint_14_61_w2 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 2 2 257661246626932360 = some 257661246626932360 := by decide +kernel
private theorem endpoint_14_61_p4 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 4 257661246626932360 = some 257661246626932360 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 2 2 257661246626932360 257661246626932360 257661246626932360 endpoint_14_61_w0 endpoint_14_61_w2
private theorem endpoint_14_61_w4 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 4 2 257661246626932360 = some 257661246626932360 := by decide +kernel
private theorem endpoint_14_61_p6 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 6 257661246626932360 = some 257661246626932360 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 4 2 257661246626932360 257661246626932360 257661246626932360 endpoint_14_61_p4 endpoint_14_61_w4
private theorem endpoint_14_61_w6 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 6 2 257661246626932360 = some 257661246626932360 := by decide +kernel
private theorem endpoint_14_61_p8 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 8 257661246626932360 = some 257661246626932360 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 6 2 257661246626932360 257661246626932360 257661246626932360 endpoint_14_61_p6 endpoint_14_61_w6
private theorem endpoint_14_61_w8 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 8 2 257661246626932360 = some 257661246626932360 := by decide +kernel
private theorem endpoint_14_61_p10 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 10 257661246626932360 = some 257661246626932360 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 8 2 257661246626932360 257661246626932360 257661246626932360 endpoint_14_61_p8 endpoint_14_61_w8
private theorem endpoint_14_61_w10 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 10 2 257661246626932360 = some 257661246626932360 := by decide +kernel
private theorem endpoint_14_61_p12 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 12 257661246626932360 = some 257661246626932360 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 10 2 257661246626932360 257661246626932360 257661246626932360 endpoint_14_61_p10 endpoint_14_61_w10
private theorem endpoint_14_61_w12 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 12 1 257661246626932360 = some 257661246626932360 := by decide +kernel
private theorem endpoint_14_61_p13 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 13 257661246626932360 = some 257661246626932360 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 12 1 257661246626932360 257661246626932360 257661246626932360 endpoint_14_61_p12 endpoint_14_61_w12
def endpoint_14_61 : CertifiedEndpoint :=
  ⟨⟨14, 61, 2574⟩, 257661246626932360, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_61_flag endpoint_14_61_sources 13 257661246626932360 257661246626932360 rfl endpoint_14_61_base endpoint_14_61_p13) (by decide)⟩
private def endpoint_14_62_flag : Flag := ⟨14, 62, 2522⟩
private def endpoint_14_62_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_62_base : receiptBase endpoint_14_62_flag endpoint_14_62_sources = some 256207734646612964 := by decide +kernel
private theorem endpoint_14_62_w0 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 2 256207734646612964 = some 257504923616954616 := by decide +kernel
private theorem endpoint_14_62_w2 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 2 2 257504923616954616 = some 257504923616954616 := by decide +kernel
private theorem endpoint_14_62_p4 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 4 256207734646612964 = some 257504923616954616 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 2 2 256207734646612964 257504923616954616 257504923616954616 endpoint_14_62_w0 endpoint_14_62_w2
private theorem endpoint_14_62_w4 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 4 2 257504923616954616 = some 257504923616954616 := by decide +kernel
private theorem endpoint_14_62_p6 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 6 256207734646612964 = some 257504923616954616 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 4 2 256207734646612964 257504923616954616 257504923616954616 endpoint_14_62_p4 endpoint_14_62_w4
private theorem endpoint_14_62_w6 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 6 2 257504923616954616 = some 257504923616954616 := by decide +kernel
private theorem endpoint_14_62_p8 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 8 256207734646612964 = some 257504923616954616 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 6 2 256207734646612964 257504923616954616 257504923616954616 endpoint_14_62_p6 endpoint_14_62_w6
private theorem endpoint_14_62_w8 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 8 2 257504923616954616 = some 257504923616954616 := by decide +kernel
private theorem endpoint_14_62_p10 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 10 256207734646612964 = some 257504923616954616 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 8 2 256207734646612964 257504923616954616 257504923616954616 endpoint_14_62_p8 endpoint_14_62_w8
private theorem endpoint_14_62_w10 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 10 2 257504923616954616 = some 257504923616954616 := by decide +kernel
private theorem endpoint_14_62_p12 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 12 256207734646612964 = some 257504923616954616 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 10 2 256207734646612964 257504923616954616 257504923616954616 endpoint_14_62_p10 endpoint_14_62_w10
private theorem endpoint_14_62_w12 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 12 1 257504923616954616 = some 257504923616954616 := by decide +kernel
private theorem endpoint_14_62_p13 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 13 256207734646612964 = some 257504923616954616 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 12 1 256207734646612964 257504923616954616 257504923616954616 endpoint_14_62_p12 endpoint_14_62_w12
def endpoint_14_62 : CertifiedEndpoint :=
  ⟨⟨14, 62, 2522⟩, 257504923616954616, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_62_flag endpoint_14_62_sources 13 256207734646612964 257504923616954616 rfl endpoint_14_62_base endpoint_14_62_p13) (by decide)⟩
private def endpoint_14_63_flag : Flag := ⟨14, 63, 2469⟩
private def endpoint_14_63_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_63_base : receiptBase endpoint_14_63_flag endpoint_14_63_sources = some 254505481055814535 := by decide +kernel
private theorem endpoint_14_63_w0 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 2 254505481055814535 = some 259117336172670820 := by decide +kernel
private theorem endpoint_14_63_w2 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 2 2 259117336172670820 = some 259117336172670820 := by decide +kernel
private theorem endpoint_14_63_p4 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 4 254505481055814535 = some 259117336172670820 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 2 2 254505481055814535 259117336172670820 259117336172670820 endpoint_14_63_w0 endpoint_14_63_w2
private theorem endpoint_14_63_w4 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 4 2 259117336172670820 = some 259117336172670820 := by decide +kernel
private theorem endpoint_14_63_p6 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 6 254505481055814535 = some 259117336172670820 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 4 2 254505481055814535 259117336172670820 259117336172670820 endpoint_14_63_p4 endpoint_14_63_w4
private theorem endpoint_14_63_w6 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 6 2 259117336172670820 = some 259117336172670820 := by decide +kernel
private theorem endpoint_14_63_p8 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 8 254505481055814535 = some 259117336172670820 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 6 2 254505481055814535 259117336172670820 259117336172670820 endpoint_14_63_p6 endpoint_14_63_w6
private theorem endpoint_14_63_w8 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 8 2 259117336172670820 = some 259117336172670820 := by decide +kernel
private theorem endpoint_14_63_p10 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 10 254505481055814535 = some 259117336172670820 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 8 2 254505481055814535 259117336172670820 259117336172670820 endpoint_14_63_p8 endpoint_14_63_w8
private theorem endpoint_14_63_w10 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 10 2 259117336172670820 = some 259117336172670820 := by decide +kernel
private theorem endpoint_14_63_p12 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 12 254505481055814535 = some 259117336172670820 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 10 2 254505481055814535 259117336172670820 259117336172670820 endpoint_14_63_p10 endpoint_14_63_w10
private theorem endpoint_14_63_w12 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 12 1 259117336172670820 = some 259117336172670820 := by decide +kernel
private theorem endpoint_14_63_p13 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 13 254505481055814535 = some 259117336172670820 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 12 1 254505481055814535 259117336172670820 259117336172670820 endpoint_14_63_p12 endpoint_14_63_w12
def endpoint_14_63 : CertifiedEndpoint :=
  ⟨⟨14, 63, 2469⟩, 259117336172670820, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_63_flag endpoint_14_63_sources 13 254505481055814535 259117336172670820 rfl endpoint_14_63_base endpoint_14_63_p13) (by decide)⟩
private def endpoint_14_64_flag : Flag := ⟨14, 64, 2413⟩
private def endpoint_14_64_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_64_base : receiptBase endpoint_14_64_flag endpoint_14_64_sources = some 252346112335387220 := by decide +kernel
private theorem endpoint_14_64_w0 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 2 252346112335387220 = some 260437735068166240 := by decide +kernel
private theorem endpoint_14_64_w2 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 2 2 260437735068166240 = some 260437735068166240 := by decide +kernel
private theorem endpoint_14_64_p4 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 4 252346112335387220 = some 260437735068166240 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 2 2 252346112335387220 260437735068166240 260437735068166240 endpoint_14_64_w0 endpoint_14_64_w2
private theorem endpoint_14_64_w4 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 4 2 260437735068166240 = some 260437735068166240 := by decide +kernel
private theorem endpoint_14_64_p6 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 6 252346112335387220 = some 260437735068166240 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 4 2 252346112335387220 260437735068166240 260437735068166240 endpoint_14_64_p4 endpoint_14_64_w4
private theorem endpoint_14_64_w6 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 6 2 260437735068166240 = some 260437735068166240 := by decide +kernel
private theorem endpoint_14_64_p8 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 8 252346112335387220 = some 260437735068166240 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 6 2 252346112335387220 260437735068166240 260437735068166240 endpoint_14_64_p6 endpoint_14_64_w6
private theorem endpoint_14_64_w8 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 8 2 260437735068166240 = some 260437735068166240 := by decide +kernel
private theorem endpoint_14_64_p10 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 10 252346112335387220 = some 260437735068166240 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 8 2 252346112335387220 260437735068166240 260437735068166240 endpoint_14_64_p8 endpoint_14_64_w8
private theorem endpoint_14_64_w10 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 10 2 260437735068166240 = some 260437735068166240 := by decide +kernel
private theorem endpoint_14_64_p12 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 12 252346112335387220 = some 260437735068166240 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 10 2 252346112335387220 260437735068166240 260437735068166240 endpoint_14_64_p10 endpoint_14_64_w10
private theorem endpoint_14_64_w12 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 12 1 260437735068166240 = some 260437735068166240 := by decide +kernel
private theorem endpoint_14_64_p13 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 13 252346112335387220 = some 260437735068166240 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 12 1 252346112335387220 260437735068166240 260437735068166240 endpoint_14_64_p12 endpoint_14_64_w12
def endpoint_14_64 : CertifiedEndpoint :=
  ⟨⟨14, 64, 2413⟩, 260437735068166240, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_64_flag endpoint_14_64_sources 13 252346112335387220 260437735068166240 rfl endpoint_14_64_base endpoint_14_64_p13) (by decide)⟩
private def endpoint_14_65_flag : Flag := ⟨14, 65, 2355⟩
private def endpoint_14_65_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_65_base : receiptBase endpoint_14_65_flag endpoint_14_65_sources = some 249820417478236784 := by decide +kernel
private theorem endpoint_14_65_w0 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 2 249820417478236784 = some 261516596050956852 := by decide +kernel
private theorem endpoint_14_65_w2 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 2 2 261516596050956852 = some 261516596050956852 := by decide +kernel
private theorem endpoint_14_65_p4 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 4 249820417478236784 = some 261516596050956852 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 2 2 249820417478236784 261516596050956852 261516596050956852 endpoint_14_65_w0 endpoint_14_65_w2
private theorem endpoint_14_65_w4 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 4 2 261516596050956852 = some 261516596050956852 := by decide +kernel
private theorem endpoint_14_65_p6 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 6 249820417478236784 = some 261516596050956852 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 4 2 249820417478236784 261516596050956852 261516596050956852 endpoint_14_65_p4 endpoint_14_65_w4
private theorem endpoint_14_65_w6 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 6 2 261516596050956852 = some 261516596050956852 := by decide +kernel
private theorem endpoint_14_65_p8 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 8 249820417478236784 = some 261516596050956852 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 6 2 249820417478236784 261516596050956852 261516596050956852 endpoint_14_65_p6 endpoint_14_65_w6
private theorem endpoint_14_65_w8 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 8 2 261516596050956852 = some 261516596050956852 := by decide +kernel
private theorem endpoint_14_65_p10 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 10 249820417478236784 = some 261516596050956852 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 8 2 249820417478236784 261516596050956852 261516596050956852 endpoint_14_65_p8 endpoint_14_65_w8
private theorem endpoint_14_65_w10 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 10 2 261516596050956852 = some 261516596050956852 := by decide +kernel
private theorem endpoint_14_65_p12 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 12 249820417478236784 = some 261516596050956852 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 10 2 249820417478236784 261516596050956852 261516596050956852 endpoint_14_65_p10 endpoint_14_65_w10
private theorem endpoint_14_65_w12 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 12 1 261516596050956852 = some 261516596050956852 := by decide +kernel
private theorem endpoint_14_65_p13 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 13 249820417478236784 = some 261516596050956852 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 12 1 249820417478236784 261516596050956852 261516596050956852 endpoint_14_65_p12 endpoint_14_65_w12
def endpoint_14_65 : CertifiedEndpoint :=
  ⟨⟨14, 65, 2355⟩, 261516596050956852, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_65_flag endpoint_14_65_sources 13 249820417478236784 261516596050956852 rfl endpoint_14_65_base endpoint_14_65_p13) (by decide)⟩
private def endpoint_14_66_flag : Flag := ⟨14, 66, 2295⟩
private def endpoint_14_66_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_14_66_base : receiptBase endpoint_14_66_flag endpoint_14_66_sources = some 248171419881485376 := by decide +kernel
private theorem endpoint_14_66_w0 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 2 248171419881485376 = some 249304073759032960 := by decide +kernel
private theorem endpoint_14_66_w2 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 2 2 249304073759032960 = some 249304073759032960 := by decide +kernel
private theorem endpoint_14_66_p4 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 4 248171419881485376 = some 249304073759032960 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 2 2 248171419881485376 249304073759032960 249304073759032960 endpoint_14_66_w0 endpoint_14_66_w2
private theorem endpoint_14_66_w4 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 4 2 249304073759032960 = some 249304073759032960 := by decide +kernel
private theorem endpoint_14_66_p6 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 6 248171419881485376 = some 249304073759032960 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 4 2 248171419881485376 249304073759032960 249304073759032960 endpoint_14_66_p4 endpoint_14_66_w4
private theorem endpoint_14_66_w6 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 6 2 249304073759032960 = some 249304073759032960 := by decide +kernel
private theorem endpoint_14_66_p8 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 8 248171419881485376 = some 249304073759032960 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 6 2 248171419881485376 249304073759032960 249304073759032960 endpoint_14_66_p6 endpoint_14_66_w6
private theorem endpoint_14_66_w8 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 8 2 249304073759032960 = some 249304073759032960 := by decide +kernel
private theorem endpoint_14_66_p10 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 10 248171419881485376 = some 249304073759032960 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 8 2 248171419881485376 249304073759032960 249304073759032960 endpoint_14_66_p8 endpoint_14_66_w8
private theorem endpoint_14_66_w10 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 10 2 249304073759032960 = some 249304073759032960 := by decide +kernel
private theorem endpoint_14_66_p12 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 12 248171419881485376 = some 249304073759032960 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 10 2 248171419881485376 249304073759032960 249304073759032960 endpoint_14_66_p10 endpoint_14_66_w10
private theorem endpoint_14_66_w12 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 12 1 249304073759032960 = some 249304073759032960 := by decide +kernel
private theorem endpoint_14_66_p13 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 13 248171419881485376 = some 249304073759032960 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 12 1 248171419881485376 249304073759032960 249304073759032960 endpoint_14_66_p12 endpoint_14_66_w12
def endpoint_14_66 : CertifiedEndpoint :=
  ⟨⟨14, 66, 2295⟩, 249304073759032960, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_14_66_flag endpoint_14_66_sources 13 248171419881485376 249304073759032960 rfl endpoint_14_66_base endpoint_14_66_p13) (by decide)⟩
private def endpoint_14_67_flag : Flag := ⟨14, 67, 2233⟩
private def endpoint_14_67_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_14_67_base : receiptBase endpoint_14_67_flag endpoint_14_67_sources = some 244860029924742501 := by decide +kernel
private theorem endpoint_14_67_w0 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 2 244860029924742501 = some 249656989660121113 := by decide +kernel
private theorem endpoint_14_67_w2 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 2 2 249656989660121113 = some 249656989660121113 := by decide +kernel
private theorem endpoint_14_67_p4 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 4 244860029924742501 = some 249656989660121113 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 2 2 244860029924742501 249656989660121113 249656989660121113 endpoint_14_67_w0 endpoint_14_67_w2
private theorem endpoint_14_67_w4 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 4 2 249656989660121113 = some 249656989660121113 := by decide +kernel
private theorem endpoint_14_67_p6 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 6 244860029924742501 = some 249656989660121113 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 4 2 244860029924742501 249656989660121113 249656989660121113 endpoint_14_67_p4 endpoint_14_67_w4
private theorem endpoint_14_67_w6 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 6 2 249656989660121113 = some 249656989660121113 := by decide +kernel
private theorem endpoint_14_67_p8 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 8 244860029924742501 = some 249656989660121113 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 6 2 244860029924742501 249656989660121113 249656989660121113 endpoint_14_67_p6 endpoint_14_67_w6
private theorem endpoint_14_67_w8 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 8 2 249656989660121113 = some 249656989660121113 := by decide +kernel
private theorem endpoint_14_67_p10 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 10 244860029924742501 = some 249656989660121113 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 8 2 244860029924742501 249656989660121113 249656989660121113 endpoint_14_67_p8 endpoint_14_67_w8
private theorem endpoint_14_67_w10 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 10 2 249656989660121113 = some 249656989660121113 := by decide +kernel
private theorem endpoint_14_67_p12 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 12 244860029924742501 = some 249656989660121113 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 10 2 244860029924742501 249656989660121113 249656989660121113 endpoint_14_67_p10 endpoint_14_67_w10
private theorem endpoint_14_67_w12 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 12 1 249656989660121113 = some 249656989660121113 := by decide +kernel
private theorem endpoint_14_67_p13 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 13 244860029924742501 = some 249656989660121113 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 12 1 244860029924742501 249656989660121113 249656989660121113 endpoint_14_67_p12 endpoint_14_67_w12
def endpoint_14_67 : CertifiedEndpoint :=
  ⟨⟨14, 67, 2233⟩, 249656989660121113, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_14_67_flag endpoint_14_67_sources 13 244860029924742501 249656989660121113 rfl endpoint_14_67_base endpoint_14_67_p13) (by decide)⟩
private def endpoint_14_68_flag : Flag := ⟨14, 68, 2168⟩
private def endpoint_14_68_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_14_68_base : receiptBase endpoint_14_68_flag endpoint_14_68_sources = some 241182032943678238 := by decide +kernel
private theorem endpoint_14_68_w0 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 2 241182032943678238 = some 249686194242144672 := by decide +kernel
private theorem endpoint_14_68_w2 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 2 2 249686194242144672 = some 249686194242144672 := by decide +kernel
private theorem endpoint_14_68_p4 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 4 241182032943678238 = some 249686194242144672 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 2 2 241182032943678238 249686194242144672 249686194242144672 endpoint_14_68_w0 endpoint_14_68_w2
private theorem endpoint_14_68_w4 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 4 2 249686194242144672 = some 249686194242144672 := by decide +kernel
private theorem endpoint_14_68_p6 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 6 241182032943678238 = some 249686194242144672 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 4 2 241182032943678238 249686194242144672 249686194242144672 endpoint_14_68_p4 endpoint_14_68_w4
private theorem endpoint_14_68_w6 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 6 2 249686194242144672 = some 249686194242144672 := by decide +kernel
private theorem endpoint_14_68_p8 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 8 241182032943678238 = some 249686194242144672 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 6 2 241182032943678238 249686194242144672 249686194242144672 endpoint_14_68_p6 endpoint_14_68_w6
private theorem endpoint_14_68_w8 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 8 2 249686194242144672 = some 249686194242144672 := by decide +kernel
private theorem endpoint_14_68_p10 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 10 241182032943678238 = some 249686194242144672 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 8 2 241182032943678238 249686194242144672 249686194242144672 endpoint_14_68_p8 endpoint_14_68_w8
private theorem endpoint_14_68_w10 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 10 2 249686194242144672 = some 249686194242144672 := by decide +kernel
private theorem endpoint_14_68_p12 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 12 241182032943678238 = some 249686194242144672 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 10 2 241182032943678238 249686194242144672 249686194242144672 endpoint_14_68_p10 endpoint_14_68_w10
private theorem endpoint_14_68_w12 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 12 1 249686194242144672 = some 249686194242144672 := by decide +kernel
private theorem endpoint_14_68_p13 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 13 241182032943678238 = some 249686194242144672 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 12 1 241182032943678238 249686194242144672 249686194242144672 endpoint_14_68_p12 endpoint_14_68_w12
def endpoint_14_68 : CertifiedEndpoint :=
  ⟨⟨14, 68, 2168⟩, 249686194242144672, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_14_68_flag endpoint_14_68_sources 13 241182032943678238 249686194242144672 rfl endpoint_14_68_base endpoint_14_68_p13) (by decide)⟩
private def endpoint_14_69_flag : Flag := ⟨14, 69, 2102⟩
private def endpoint_14_69_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_14_69_base : receiptBase endpoint_14_69_flag endpoint_14_69_sources = some 238455745446571267 := by decide +kernel
private theorem endpoint_14_69_w0 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 2 238455745446571267 = some 242719650050762963 := by decide +kernel
private theorem endpoint_14_69_w2 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 2 2 242719650050762963 = some 242719650050762963 := by decide +kernel
private theorem endpoint_14_69_p4 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 4 238455745446571267 = some 242719650050762963 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 2 2 238455745446571267 242719650050762963 242719650050762963 endpoint_14_69_w0 endpoint_14_69_w2
private theorem endpoint_14_69_w4 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 4 2 242719650050762963 = some 242719650050762963 := by decide +kernel
private theorem endpoint_14_69_p6 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 6 238455745446571267 = some 242719650050762963 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 4 2 238455745446571267 242719650050762963 242719650050762963 endpoint_14_69_p4 endpoint_14_69_w4
private theorem endpoint_14_69_w6 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 6 2 242719650050762963 = some 242719650050762963 := by decide +kernel
private theorem endpoint_14_69_p8 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 8 238455745446571267 = some 242719650050762963 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 6 2 238455745446571267 242719650050762963 242719650050762963 endpoint_14_69_p6 endpoint_14_69_w6
private theorem endpoint_14_69_w8 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 8 2 242719650050762963 = some 242719650050762963 := by decide +kernel
private theorem endpoint_14_69_p10 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 10 238455745446571267 = some 242719650050762963 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 8 2 238455745446571267 242719650050762963 242719650050762963 endpoint_14_69_p8 endpoint_14_69_w8
private theorem endpoint_14_69_w10 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 10 2 242719650050762963 = some 242719650050762963 := by decide +kernel
private theorem endpoint_14_69_p12 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 12 238455745446571267 = some 242719650050762963 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 10 2 238455745446571267 242719650050762963 242719650050762963 endpoint_14_69_p10 endpoint_14_69_w10
private theorem endpoint_14_69_w12 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 12 1 242719650050762963 = some 242719650050762963 := by decide +kernel
private theorem endpoint_14_69_p13 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 13 238455745446571267 = some 242719650050762963 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 12 1 238455745446571267 242719650050762963 242719650050762963 endpoint_14_69_p12 endpoint_14_69_w12
def endpoint_14_69 : CertifiedEndpoint :=
  ⟨⟨14, 69, 2102⟩, 242719650050762963, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_14_69_flag endpoint_14_69_sources 13 238455745446571267 242719650050762963 rfl endpoint_14_69_base endpoint_14_69_p13) (by decide)⟩
private def endpoint_14_70_flag : Flag := ⟨14, 70, 2033⟩
private def endpoint_14_70_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_14_70_base : receiptBase endpoint_14_70_flag endpoint_14_70_sources = some 235394115244029128 := by decide +kernel
private theorem endpoint_14_70_w0 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 2 235394115244029128 = some 235394115244029128 := by decide +kernel
private theorem endpoint_14_70_w2 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 2 2 235394115244029128 = some 235394115244029128 := by decide +kernel
private theorem endpoint_14_70_p4 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 4 235394115244029128 = some 235394115244029128 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 2 2 235394115244029128 235394115244029128 235394115244029128 endpoint_14_70_w0 endpoint_14_70_w2
private theorem endpoint_14_70_w4 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 4 2 235394115244029128 = some 235394115244029128 := by decide +kernel
private theorem endpoint_14_70_p6 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 6 235394115244029128 = some 235394115244029128 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 4 2 235394115244029128 235394115244029128 235394115244029128 endpoint_14_70_p4 endpoint_14_70_w4
private theorem endpoint_14_70_w6 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 6 2 235394115244029128 = some 235394115244029128 := by decide +kernel
private theorem endpoint_14_70_p8 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 8 235394115244029128 = some 235394115244029128 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 6 2 235394115244029128 235394115244029128 235394115244029128 endpoint_14_70_p6 endpoint_14_70_w6
private theorem endpoint_14_70_w8 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 8 2 235394115244029128 = some 235394115244029128 := by decide +kernel
private theorem endpoint_14_70_p10 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 10 235394115244029128 = some 235394115244029128 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 8 2 235394115244029128 235394115244029128 235394115244029128 endpoint_14_70_p8 endpoint_14_70_w8
private theorem endpoint_14_70_w10 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 10 2 235394115244029128 = some 235394115244029128 := by decide +kernel
private theorem endpoint_14_70_p12 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 12 235394115244029128 = some 235394115244029128 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 10 2 235394115244029128 235394115244029128 235394115244029128 endpoint_14_70_p10 endpoint_14_70_w10
private theorem endpoint_14_70_w12 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 12 1 235394115244029128 = some 235394115244029128 := by decide +kernel
private theorem endpoint_14_70_p13 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 13 235394115244029128 = some 235394115244029128 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 12 1 235394115244029128 235394115244029128 235394115244029128 endpoint_14_70_p12 endpoint_14_70_w12
def endpoint_14_70 : CertifiedEndpoint :=
  ⟨⟨14, 70, 2033⟩, 235394115244029128, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_14_70_flag endpoint_14_70_sources 13 235394115244029128 235394115244029128 rfl endpoint_14_70_base endpoint_14_70_p13) (by decide)⟩
private def endpoint_14_71_flag : Flag := ⟨14, 71, 1961⟩
private def endpoint_14_71_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_14_71_base : receiptBase endpoint_14_71_flag endpoint_14_71_sources = some 231767956130350882 := by decide +kernel
private theorem endpoint_14_71_w0 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 2 231767956130350882 = some 231767956130350882 := by decide +kernel
private theorem endpoint_14_71_w2 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 2 2 231767956130350882 = some 231767956130350882 := by decide +kernel
private theorem endpoint_14_71_p4 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 4 231767956130350882 = some 231767956130350882 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 2 2 231767956130350882 231767956130350882 231767956130350882 endpoint_14_71_w0 endpoint_14_71_w2
private theorem endpoint_14_71_w4 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 4 2 231767956130350882 = some 231767956130350882 := by decide +kernel
private theorem endpoint_14_71_p6 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 6 231767956130350882 = some 231767956130350882 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 4 2 231767956130350882 231767956130350882 231767956130350882 endpoint_14_71_p4 endpoint_14_71_w4
private theorem endpoint_14_71_w6 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 6 2 231767956130350882 = some 231767956130350882 := by decide +kernel
private theorem endpoint_14_71_p8 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 8 231767956130350882 = some 231767956130350882 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 6 2 231767956130350882 231767956130350882 231767956130350882 endpoint_14_71_p6 endpoint_14_71_w6
private theorem endpoint_14_71_w8 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 8 2 231767956130350882 = some 231767956130350882 := by decide +kernel
private theorem endpoint_14_71_p10 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 10 231767956130350882 = some 231767956130350882 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 8 2 231767956130350882 231767956130350882 231767956130350882 endpoint_14_71_p8 endpoint_14_71_w8
private theorem endpoint_14_71_w10 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 10 2 231767956130350882 = some 231767956130350882 := by decide +kernel
private theorem endpoint_14_71_p12 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 12 231767956130350882 = some 231767956130350882 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 10 2 231767956130350882 231767956130350882 231767956130350882 endpoint_14_71_p10 endpoint_14_71_w10
private theorem endpoint_14_71_w12 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 12 1 231767956130350882 = some 231767956130350882 := by decide +kernel
private theorem endpoint_14_71_p13 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 13 231767956130350882 = some 231767956130350882 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 12 1 231767956130350882 231767956130350882 231767956130350882 endpoint_14_71_p12 endpoint_14_71_w12
def endpoint_14_71 : CertifiedEndpoint :=
  ⟨⟨14, 71, 1961⟩, 231767956130350882, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_14_71_flag endpoint_14_71_sources 13 231767956130350882 231767956130350882 rfl endpoint_14_71_base endpoint_14_71_p13) (by decide)⟩
private def endpoint_14_72_flag : Flag := ⟨14, 72, 1887⟩
private def endpoint_14_72_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_14_72_base : receiptBase endpoint_14_72_flag endpoint_14_72_sources = some 225882936420228700 := by decide +kernel
private theorem endpoint_14_72_w0 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 2 225882936420228700 = some 225882936420228700 := by decide +kernel
private theorem endpoint_14_72_w2 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 2 2 225882936420228700 = some 225882936420228700 := by decide +kernel
private theorem endpoint_14_72_p4 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 4 225882936420228700 = some 225882936420228700 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 2 2 225882936420228700 225882936420228700 225882936420228700 endpoint_14_72_w0 endpoint_14_72_w2
private theorem endpoint_14_72_w4 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 4 2 225882936420228700 = some 225882936420228700 := by decide +kernel
private theorem endpoint_14_72_p6 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 6 225882936420228700 = some 225882936420228700 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 4 2 225882936420228700 225882936420228700 225882936420228700 endpoint_14_72_p4 endpoint_14_72_w4
private theorem endpoint_14_72_w6 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 6 2 225882936420228700 = some 225882936420228700 := by decide +kernel
private theorem endpoint_14_72_p8 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 8 225882936420228700 = some 225882936420228700 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 6 2 225882936420228700 225882936420228700 225882936420228700 endpoint_14_72_p6 endpoint_14_72_w6
private theorem endpoint_14_72_w8 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 8 2 225882936420228700 = some 225882936420228700 := by decide +kernel
private theorem endpoint_14_72_p10 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 10 225882936420228700 = some 225882936420228700 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 8 2 225882936420228700 225882936420228700 225882936420228700 endpoint_14_72_p8 endpoint_14_72_w8
private theorem endpoint_14_72_w10 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 10 2 225882936420228700 = some 225882936420228700 := by decide +kernel
private theorem endpoint_14_72_p12 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 12 225882936420228700 = some 225882936420228700 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 10 2 225882936420228700 225882936420228700 225882936420228700 endpoint_14_72_p10 endpoint_14_72_w10
private theorem endpoint_14_72_w12 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 12 1 225882936420228700 = some 225882936420228700 := by decide +kernel
private theorem endpoint_14_72_p13 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 13 225882936420228700 = some 225882936420228700 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 12 1 225882936420228700 225882936420228700 225882936420228700 endpoint_14_72_p12 endpoint_14_72_w12
def endpoint_14_72 : CertifiedEndpoint :=
  ⟨⟨14, 72, 1887⟩, 225882936420228700, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_14_72_flag endpoint_14_72_sources 13 225882936420228700 225882936420228700 rfl endpoint_14_72_base endpoint_14_72_p13) (by decide)⟩
private def endpoint_14_73_flag : Flag := ⟨14, 73, 1811⟩
private def endpoint_14_73_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_14_73_base : receiptBase endpoint_14_73_flag endpoint_14_73_sources = some 221302535896049847 := by decide +kernel
private theorem endpoint_14_73_w0 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 2 221302535896049847 = some 221302535896049847 := by decide +kernel
private theorem endpoint_14_73_w2 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 2 2 221302535896049847 = some 221302535896049847 := by decide +kernel
private theorem endpoint_14_73_p4 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 4 221302535896049847 = some 221302535896049847 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 2 2 221302535896049847 221302535896049847 221302535896049847 endpoint_14_73_w0 endpoint_14_73_w2
private theorem endpoint_14_73_w4 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 4 2 221302535896049847 = some 221302535896049847 := by decide +kernel
private theorem endpoint_14_73_p6 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 6 221302535896049847 = some 221302535896049847 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 4 2 221302535896049847 221302535896049847 221302535896049847 endpoint_14_73_p4 endpoint_14_73_w4
private theorem endpoint_14_73_w6 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 6 2 221302535896049847 = some 221302535896049847 := by decide +kernel
private theorem endpoint_14_73_p8 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 8 221302535896049847 = some 221302535896049847 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 6 2 221302535896049847 221302535896049847 221302535896049847 endpoint_14_73_p6 endpoint_14_73_w6
private theorem endpoint_14_73_w8 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 8 2 221302535896049847 = some 221302535896049847 := by decide +kernel
private theorem endpoint_14_73_p10 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 10 221302535896049847 = some 221302535896049847 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 8 2 221302535896049847 221302535896049847 221302535896049847 endpoint_14_73_p8 endpoint_14_73_w8
private theorem endpoint_14_73_w10 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 10 2 221302535896049847 = some 221302535896049847 := by decide +kernel
private theorem endpoint_14_73_p12 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 12 221302535896049847 = some 221302535896049847 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 10 2 221302535896049847 221302535896049847 221302535896049847 endpoint_14_73_p10 endpoint_14_73_w10
private theorem endpoint_14_73_w12 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 12 1 221302535896049847 = some 221302535896049847 := by decide +kernel
private theorem endpoint_14_73_p13 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 13 221302535896049847 = some 221302535896049847 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 12 1 221302535896049847 221302535896049847 221302535896049847 endpoint_14_73_p12 endpoint_14_73_w12
def endpoint_14_73 : CertifiedEndpoint :=
  ⟨⟨14, 73, 1811⟩, 221302535896049847, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_14_73_flag endpoint_14_73_sources 13 221302535896049847 221302535896049847 rfl endpoint_14_73_base endpoint_14_73_p13) (by decide)⟩
private def endpoint_14_74_flag : Flag := ⟨14, 74, 1733⟩
private def endpoint_14_74_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_14_74_base : receiptBase endpoint_14_74_flag endpoint_14_74_sources = some 214419639332896130 := by decide +kernel
private theorem endpoint_14_74_w0 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 2 214419639332896130 = some 214419639332896130 := by decide +kernel
private theorem endpoint_14_74_w2 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 2 2 214419639332896130 = some 214419639332896130 := by decide +kernel
private theorem endpoint_14_74_p4 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 4 214419639332896130 = some 214419639332896130 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 2 2 214419639332896130 214419639332896130 214419639332896130 endpoint_14_74_w0 endpoint_14_74_w2
private theorem endpoint_14_74_w4 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 4 2 214419639332896130 = some 214419639332896130 := by decide +kernel
private theorem endpoint_14_74_p6 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 6 214419639332896130 = some 214419639332896130 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 4 2 214419639332896130 214419639332896130 214419639332896130 endpoint_14_74_p4 endpoint_14_74_w4
private theorem endpoint_14_74_w6 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 6 2 214419639332896130 = some 214419639332896130 := by decide +kernel
private theorem endpoint_14_74_p8 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 8 214419639332896130 = some 214419639332896130 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 6 2 214419639332896130 214419639332896130 214419639332896130 endpoint_14_74_p6 endpoint_14_74_w6
private theorem endpoint_14_74_w8 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 8 2 214419639332896130 = some 214419639332896130 := by decide +kernel
private theorem endpoint_14_74_p10 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 10 214419639332896130 = some 214419639332896130 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 8 2 214419639332896130 214419639332896130 214419639332896130 endpoint_14_74_p8 endpoint_14_74_w8
private theorem endpoint_14_74_w10 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 10 2 214419639332896130 = some 214419639332896130 := by decide +kernel
private theorem endpoint_14_74_p12 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 12 214419639332896130 = some 214419639332896130 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 10 2 214419639332896130 214419639332896130 214419639332896130 endpoint_14_74_p10 endpoint_14_74_w10
private theorem endpoint_14_74_w12 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 12 1 214419639332896130 = some 214419639332896130 := by decide +kernel
private theorem endpoint_14_74_p13 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 13 214419639332896130 = some 214419639332896130 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 12 1 214419639332896130 214419639332896130 214419639332896130 endpoint_14_74_p12 endpoint_14_74_w12
def endpoint_14_74 : CertifiedEndpoint :=
  ⟨⟨14, 74, 1733⟩, 214419639332896130, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_14_74_flag endpoint_14_74_sources 13 214419639332896130 214419639332896130 rfl endpoint_14_74_base endpoint_14_74_p13) (by decide)⟩
private def endpoint_14_75_flag : Flag := ⟨14, 75, 1652⟩
private def endpoint_14_75_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_14_75_base : receiptBase endpoint_14_75_flag endpoint_14_75_sources = some 206930661964644669 := by decide +kernel
private theorem endpoint_14_75_w0 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 2 206930661964644669 = some 206930661964644669 := by decide +kernel
private theorem endpoint_14_75_w2 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 2 2 206930661964644669 = some 206930661964644669 := by decide +kernel
private theorem endpoint_14_75_p4 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 4 206930661964644669 = some 206930661964644669 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 2 2 206930661964644669 206930661964644669 206930661964644669 endpoint_14_75_w0 endpoint_14_75_w2
private theorem endpoint_14_75_w4 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 4 2 206930661964644669 = some 206930661964644669 := by decide +kernel
private theorem endpoint_14_75_p6 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 6 206930661964644669 = some 206930661964644669 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 4 2 206930661964644669 206930661964644669 206930661964644669 endpoint_14_75_p4 endpoint_14_75_w4
private theorem endpoint_14_75_w6 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 6 2 206930661964644669 = some 206930661964644669 := by decide +kernel
private theorem endpoint_14_75_p8 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 8 206930661964644669 = some 206930661964644669 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 6 2 206930661964644669 206930661964644669 206930661964644669 endpoint_14_75_p6 endpoint_14_75_w6
private theorem endpoint_14_75_w8 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 8 2 206930661964644669 = some 206930661964644669 := by decide +kernel
private theorem endpoint_14_75_p10 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 10 206930661964644669 = some 206930661964644669 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 8 2 206930661964644669 206930661964644669 206930661964644669 endpoint_14_75_p8 endpoint_14_75_w8
private theorem endpoint_14_75_w10 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 10 2 206930661964644669 = some 206930661964644669 := by decide +kernel
private theorem endpoint_14_75_p12 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 12 206930661964644669 = some 206930661964644669 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 10 2 206930661964644669 206930661964644669 206930661964644669 endpoint_14_75_p10 endpoint_14_75_w10
private theorem endpoint_14_75_w12 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 12 1 206930661964644669 = some 206930661964644669 := by decide +kernel
private theorem endpoint_14_75_p13 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 13 206930661964644669 = some 206930661964644669 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 12 1 206930661964644669 206930661964644669 206930661964644669 endpoint_14_75_p12 endpoint_14_75_w12
def endpoint_14_75 : CertifiedEndpoint :=
  ⟨⟨14, 75, 1652⟩, 206930661964644669, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_14_75_flag endpoint_14_75_sources 13 206930661964644669 206930661964644669 rfl endpoint_14_75_base endpoint_14_75_p13) (by decide)⟩
private def endpoint_14_76_flag : Flag := ⟨14, 76, 1568⟩
private def endpoint_14_76_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_14_76_base : receiptBase endpoint_14_76_flag endpoint_14_76_sources = some 200387628557766606 := by decide +kernel
private theorem endpoint_14_76_w0 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 2 200387628557766606 = some 200387628557766606 := by decide +kernel
private theorem endpoint_14_76_w2 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 2 2 200387628557766606 = some 200387628557766606 := by decide +kernel
private theorem endpoint_14_76_p4 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 4 200387628557766606 = some 200387628557766606 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 2 2 200387628557766606 200387628557766606 200387628557766606 endpoint_14_76_w0 endpoint_14_76_w2
private theorem endpoint_14_76_w4 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 4 2 200387628557766606 = some 200387628557766606 := by decide +kernel
private theorem endpoint_14_76_p6 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 6 200387628557766606 = some 200387628557766606 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 4 2 200387628557766606 200387628557766606 200387628557766606 endpoint_14_76_p4 endpoint_14_76_w4
private theorem endpoint_14_76_w6 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 6 2 200387628557766606 = some 200387628557766606 := by decide +kernel
private theorem endpoint_14_76_p8 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 8 200387628557766606 = some 200387628557766606 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 6 2 200387628557766606 200387628557766606 200387628557766606 endpoint_14_76_p6 endpoint_14_76_w6
private theorem endpoint_14_76_w8 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 8 2 200387628557766606 = some 200387628557766606 := by decide +kernel
private theorem endpoint_14_76_p10 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 10 200387628557766606 = some 200387628557766606 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 8 2 200387628557766606 200387628557766606 200387628557766606 endpoint_14_76_p8 endpoint_14_76_w8
private theorem endpoint_14_76_w10 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 10 2 200387628557766606 = some 200387628557766606 := by decide +kernel
private theorem endpoint_14_76_p12 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 12 200387628557766606 = some 200387628557766606 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 10 2 200387628557766606 200387628557766606 200387628557766606 endpoint_14_76_p10 endpoint_14_76_w10
private theorem endpoint_14_76_w12 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 12 1 200387628557766606 = some 200387628557766606 := by decide +kernel
private theorem endpoint_14_76_p13 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 13 200387628557766606 = some 200387628557766606 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 12 1 200387628557766606 200387628557766606 200387628557766606 endpoint_14_76_p12 endpoint_14_76_w12
def endpoint_14_76 : CertifiedEndpoint :=
  ⟨⟨14, 76, 1568⟩, 200387628557766606, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_14_76_flag endpoint_14_76_sources 13 200387628557766606 200387628557766606 rfl endpoint_14_76_base endpoint_14_76_p13) (by decide)⟩
private def endpoint_14_77_flag : Flag := ⟨14, 77, 1482⟩
private def endpoint_14_77_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_14_77_base : receiptBase endpoint_14_77_flag endpoint_14_77_sources = some 191732932957858335 := by decide +kernel
private theorem endpoint_14_77_w0 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 2 191732932957858335 = some 191732932957858335 := by decide +kernel
private theorem endpoint_14_77_w2 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 2 2 191732932957858335 = some 191732932957858335 := by decide +kernel
private theorem endpoint_14_77_p4 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 4 191732932957858335 = some 191732932957858335 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 2 2 191732932957858335 191732932957858335 191732932957858335 endpoint_14_77_w0 endpoint_14_77_w2
private theorem endpoint_14_77_w4 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 4 2 191732932957858335 = some 191732932957858335 := by decide +kernel
private theorem endpoint_14_77_p6 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 6 191732932957858335 = some 191732932957858335 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 4 2 191732932957858335 191732932957858335 191732932957858335 endpoint_14_77_p4 endpoint_14_77_w4
private theorem endpoint_14_77_w6 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 6 2 191732932957858335 = some 191732932957858335 := by decide +kernel
private theorem endpoint_14_77_p8 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 8 191732932957858335 = some 191732932957858335 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 6 2 191732932957858335 191732932957858335 191732932957858335 endpoint_14_77_p6 endpoint_14_77_w6
private theorem endpoint_14_77_w8 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 8 2 191732932957858335 = some 191732932957858335 := by decide +kernel
private theorem endpoint_14_77_p10 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 10 191732932957858335 = some 191732932957858335 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 8 2 191732932957858335 191732932957858335 191732932957858335 endpoint_14_77_p8 endpoint_14_77_w8
private theorem endpoint_14_77_w10 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 10 2 191732932957858335 = some 191732932957858335 := by decide +kernel
private theorem endpoint_14_77_p12 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 12 191732932957858335 = some 191732932957858335 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 10 2 191732932957858335 191732932957858335 191732932957858335 endpoint_14_77_p10 endpoint_14_77_w10
private theorem endpoint_14_77_w12 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 12 1 191732932957858335 = some 191732932957858335 := by decide +kernel
private theorem endpoint_14_77_p13 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 13 191732932957858335 = some 191732932957858335 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 12 1 191732932957858335 191732932957858335 191732932957858335 endpoint_14_77_p12 endpoint_14_77_w12
def endpoint_14_77 : CertifiedEndpoint :=
  ⟨⟨14, 77, 1482⟩, 191732932957858335, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_14_77_flag endpoint_14_77_sources 13 191732932957858335 191732932957858335 rfl endpoint_14_77_base endpoint_14_77_p13) (by decide)⟩
private def endpoint_14_78_flag : Flag := ⟨14, 78, 1393⟩
private def endpoint_14_78_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_14_78_base : receiptBase endpoint_14_78_flag endpoint_14_78_sources = some 183929753372541037 := by decide +kernel
private theorem endpoint_14_78_w0 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 2 183929753372541037 = some 183929753372541037 := by decide +kernel
private theorem endpoint_14_78_w2 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 2 2 183929753372541037 = some 183929753372541037 := by decide +kernel
private theorem endpoint_14_78_p4 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 4 183929753372541037 = some 183929753372541037 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 2 2 183929753372541037 183929753372541037 183929753372541037 endpoint_14_78_w0 endpoint_14_78_w2
private theorem endpoint_14_78_w4 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 4 2 183929753372541037 = some 183929753372541037 := by decide +kernel
private theorem endpoint_14_78_p6 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 6 183929753372541037 = some 183929753372541037 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 4 2 183929753372541037 183929753372541037 183929753372541037 endpoint_14_78_p4 endpoint_14_78_w4
private theorem endpoint_14_78_w6 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 6 2 183929753372541037 = some 183929753372541037 := by decide +kernel
private theorem endpoint_14_78_p8 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 8 183929753372541037 = some 183929753372541037 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 6 2 183929753372541037 183929753372541037 183929753372541037 endpoint_14_78_p6 endpoint_14_78_w6
private theorem endpoint_14_78_w8 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 8 2 183929753372541037 = some 183929753372541037 := by decide +kernel
private theorem endpoint_14_78_p10 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 10 183929753372541037 = some 183929753372541037 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 8 2 183929753372541037 183929753372541037 183929753372541037 endpoint_14_78_p8 endpoint_14_78_w8
private theorem endpoint_14_78_w10 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 10 2 183929753372541037 = some 183929753372541037 := by decide +kernel
private theorem endpoint_14_78_p12 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 12 183929753372541037 = some 183929753372541037 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 10 2 183929753372541037 183929753372541037 183929753372541037 endpoint_14_78_p10 endpoint_14_78_w10
private theorem endpoint_14_78_w12 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 12 1 183929753372541037 = some 183929753372541037 := by decide +kernel
private theorem endpoint_14_78_p13 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 13 183929753372541037 = some 183929753372541037 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 12 1 183929753372541037 183929753372541037 183929753372541037 endpoint_14_78_p12 endpoint_14_78_w12
def endpoint_14_78 : CertifiedEndpoint :=
  ⟨⟨14, 78, 1393⟩, 183929753372541037, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_14_78_flag endpoint_14_78_sources 13 183929753372541037 183929753372541037 rfl endpoint_14_78_base endpoint_14_78_p13) (by decide)⟩
private def endpoint_14_79_flag : Flag := ⟨14, 79, 1302⟩
private def endpoint_14_79_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_14_79_base : receiptBase endpoint_14_79_flag endpoint_14_79_sources = some 173968459611830265 := by decide +kernel
private theorem endpoint_14_79_w0 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 2 173968459611830265 = some 173968459611830265 := by decide +kernel
private theorem endpoint_14_79_w2 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 2 2 173968459611830265 = some 173968459611830265 := by decide +kernel
private theorem endpoint_14_79_p4 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 4 173968459611830265 = some 173968459611830265 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 2 2 173968459611830265 173968459611830265 173968459611830265 endpoint_14_79_w0 endpoint_14_79_w2
private theorem endpoint_14_79_w4 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 4 2 173968459611830265 = some 173968459611830265 := by decide +kernel
private theorem endpoint_14_79_p6 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 6 173968459611830265 = some 173968459611830265 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 4 2 173968459611830265 173968459611830265 173968459611830265 endpoint_14_79_p4 endpoint_14_79_w4
private theorem endpoint_14_79_w6 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 6 2 173968459611830265 = some 173968459611830265 := by decide +kernel
private theorem endpoint_14_79_p8 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 8 173968459611830265 = some 173968459611830265 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 6 2 173968459611830265 173968459611830265 173968459611830265 endpoint_14_79_p6 endpoint_14_79_w6
private theorem endpoint_14_79_w8 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 8 2 173968459611830265 = some 173968459611830265 := by decide +kernel
private theorem endpoint_14_79_p10 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 10 173968459611830265 = some 173968459611830265 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 8 2 173968459611830265 173968459611830265 173968459611830265 endpoint_14_79_p8 endpoint_14_79_w8
private theorem endpoint_14_79_w10 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 10 2 173968459611830265 = some 173968459611830265 := by decide +kernel
private theorem endpoint_14_79_p12 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 12 173968459611830265 = some 173968459611830265 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 10 2 173968459611830265 173968459611830265 173968459611830265 endpoint_14_79_p10 endpoint_14_79_w10
private theorem endpoint_14_79_w12 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 12 1 173968459611830265 = some 173968459611830265 := by decide +kernel
private theorem endpoint_14_79_p13 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 13 173968459611830265 = some 173968459611830265 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 12 1 173968459611830265 173968459611830265 173968459611830265 endpoint_14_79_p12 endpoint_14_79_w12
def endpoint_14_79 : CertifiedEndpoint :=
  ⟨⟨14, 79, 1302⟩, 173968459611830265, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_14_79_flag endpoint_14_79_sources 13 173968459611830265 173968459611830265 rfl endpoint_14_79_base endpoint_14_79_p13) (by decide)⟩
private def endpoint_14_80_flag : Flag := ⟨14, 80, 1209⟩
private def endpoint_14_80_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_14_80_base : receiptBase endpoint_14_80_flag endpoint_14_80_sources = some 163467605235653279 := by decide +kernel
private theorem endpoint_14_80_w0 : receiptWindow endpoint_14_80_flag endpoint_14_80_sources 0 2 163467605235653279 = some 163467605235653279 := by decide +kernel
private theorem endpoint_14_80_w2 : receiptWindow endpoint_14_80_flag endpoint_14_80_sources 2 2 163467605235653279 = some 163467605235653279 := by decide +kernel
private theorem endpoint_14_80_p4 : receiptWindow endpoint_14_80_flag endpoint_14_80_sources 0 4 163467605235653279 = some 163467605235653279 :=
  join_receipt_window endpoint_14_80_flag endpoint_14_80_sources 0 2 2 163467605235653279 163467605235653279 163467605235653279 endpoint_14_80_w0 endpoint_14_80_w2
private theorem endpoint_14_80_w4 : receiptWindow endpoint_14_80_flag endpoint_14_80_sources 4 2 163467605235653279 = some 163467605235653279 := by decide +kernel
private theorem endpoint_14_80_p6 : receiptWindow endpoint_14_80_flag endpoint_14_80_sources 0 6 163467605235653279 = some 163467605235653279 :=
  join_receipt_window endpoint_14_80_flag endpoint_14_80_sources 0 4 2 163467605235653279 163467605235653279 163467605235653279 endpoint_14_80_p4 endpoint_14_80_w4
private theorem endpoint_14_80_w6 : receiptWindow endpoint_14_80_flag endpoint_14_80_sources 6 2 163467605235653279 = some 163467605235653279 := by decide +kernel
private theorem endpoint_14_80_p8 : receiptWindow endpoint_14_80_flag endpoint_14_80_sources 0 8 163467605235653279 = some 163467605235653279 :=
  join_receipt_window endpoint_14_80_flag endpoint_14_80_sources 0 6 2 163467605235653279 163467605235653279 163467605235653279 endpoint_14_80_p6 endpoint_14_80_w6
private theorem endpoint_14_80_w8 : receiptWindow endpoint_14_80_flag endpoint_14_80_sources 8 2 163467605235653279 = some 163467605235653279 := by decide +kernel
private theorem endpoint_14_80_p10 : receiptWindow endpoint_14_80_flag endpoint_14_80_sources 0 10 163467605235653279 = some 163467605235653279 :=
  join_receipt_window endpoint_14_80_flag endpoint_14_80_sources 0 8 2 163467605235653279 163467605235653279 163467605235653279 endpoint_14_80_p8 endpoint_14_80_w8
private theorem endpoint_14_80_w10 : receiptWindow endpoint_14_80_flag endpoint_14_80_sources 10 2 163467605235653279 = some 163467605235653279 := by decide +kernel
private theorem endpoint_14_80_p12 : receiptWindow endpoint_14_80_flag endpoint_14_80_sources 0 12 163467605235653279 = some 163467605235653279 :=
  join_receipt_window endpoint_14_80_flag endpoint_14_80_sources 0 10 2 163467605235653279 163467605235653279 163467605235653279 endpoint_14_80_p10 endpoint_14_80_w10
private theorem endpoint_14_80_w12 : receiptWindow endpoint_14_80_flag endpoint_14_80_sources 12 1 163467605235653279 = some 163467605235653279 := by decide +kernel
private theorem endpoint_14_80_p13 : receiptWindow endpoint_14_80_flag endpoint_14_80_sources 0 13 163467605235653279 = some 163467605235653279 :=
  join_receipt_window endpoint_14_80_flag endpoint_14_80_sources 0 12 1 163467605235653279 163467605235653279 163467605235653279 endpoint_14_80_p12 endpoint_14_80_w12
def endpoint_14_80 : CertifiedEndpoint :=
  ⟨⟨14, 80, 1209⟩, 163467605235653279, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_14_80_flag endpoint_14_80_sources 13 163467605235653279 163467605235653279 rfl endpoint_14_80_base endpoint_14_80_p13) (by decide)⟩
private def endpoint_14_81_flag : Flag := ⟨14, 81, 1113⟩
private def endpoint_14_81_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_14_81_base : receiptBase endpoint_14_81_flag endpoint_14_81_sources = some 152283233015102011 := by decide +kernel
private theorem endpoint_14_81_w0 : receiptWindow endpoint_14_81_flag endpoint_14_81_sources 0 2 152283233015102011 = some 156157371903072829 := by decide +kernel
private theorem endpoint_14_81_w2 : receiptWindow endpoint_14_81_flag endpoint_14_81_sources 2 2 156157371903072829 = some 156157371903072829 := by decide +kernel
private theorem endpoint_14_81_p4 : receiptWindow endpoint_14_81_flag endpoint_14_81_sources 0 4 152283233015102011 = some 156157371903072829 :=
  join_receipt_window endpoint_14_81_flag endpoint_14_81_sources 0 2 2 152283233015102011 156157371903072829 156157371903072829 endpoint_14_81_w0 endpoint_14_81_w2
private theorem endpoint_14_81_w4 : receiptWindow endpoint_14_81_flag endpoint_14_81_sources 4 2 156157371903072829 = some 156157371903072829 := by decide +kernel
private theorem endpoint_14_81_p6 : receiptWindow endpoint_14_81_flag endpoint_14_81_sources 0 6 152283233015102011 = some 156157371903072829 :=
  join_receipt_window endpoint_14_81_flag endpoint_14_81_sources 0 4 2 152283233015102011 156157371903072829 156157371903072829 endpoint_14_81_p4 endpoint_14_81_w4
private theorem endpoint_14_81_w6 : receiptWindow endpoint_14_81_flag endpoint_14_81_sources 6 2 156157371903072829 = some 156157371903072829 := by decide +kernel
private theorem endpoint_14_81_p8 : receiptWindow endpoint_14_81_flag endpoint_14_81_sources 0 8 152283233015102011 = some 156157371903072829 :=
  join_receipt_window endpoint_14_81_flag endpoint_14_81_sources 0 6 2 152283233015102011 156157371903072829 156157371903072829 endpoint_14_81_p6 endpoint_14_81_w6
private theorem endpoint_14_81_w8 : receiptWindow endpoint_14_81_flag endpoint_14_81_sources 8 2 156157371903072829 = some 156157371903072829 := by decide +kernel
private theorem endpoint_14_81_p10 : receiptWindow endpoint_14_81_flag endpoint_14_81_sources 0 10 152283233015102011 = some 156157371903072829 :=
  join_receipt_window endpoint_14_81_flag endpoint_14_81_sources 0 8 2 152283233015102011 156157371903072829 156157371903072829 endpoint_14_81_p8 endpoint_14_81_w8
private theorem endpoint_14_81_w10 : receiptWindow endpoint_14_81_flag endpoint_14_81_sources 10 2 156157371903072829 = some 156157371903072829 := by decide +kernel
private theorem endpoint_14_81_p12 : receiptWindow endpoint_14_81_flag endpoint_14_81_sources 0 12 152283233015102011 = some 156157371903072829 :=
  join_receipt_window endpoint_14_81_flag endpoint_14_81_sources 0 10 2 152283233015102011 156157371903072829 156157371903072829 endpoint_14_81_p10 endpoint_14_81_w10
private theorem endpoint_14_81_w12 : receiptWindow endpoint_14_81_flag endpoint_14_81_sources 12 1 156157371903072829 = some 156157371903072829 := by decide +kernel
private theorem endpoint_14_81_p13 : receiptWindow endpoint_14_81_flag endpoint_14_81_sources 0 13 152283233015102011 = some 156157371903072829 :=
  join_receipt_window endpoint_14_81_flag endpoint_14_81_sources 0 12 1 152283233015102011 156157371903072829 156157371903072829 endpoint_14_81_p12 endpoint_14_81_w12
def endpoint_14_81 : CertifiedEndpoint :=
  ⟨⟨14, 81, 1113⟩, 156157371903072829, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_14_81_flag endpoint_14_81_sources 13 152283233015102011 156157371903072829 rfl endpoint_14_81_base endpoint_14_81_p13) (by decide)⟩
def endpoint_14_82 : CertifiedEndpoint :=
  ⟨⟨14, 82, 1014⟩, 251871821739939654, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_83 : CertifiedEndpoint :=
  ⟨⟨14, 83, 913⟩, 228524953484834374, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_84 : CertifiedEndpoint :=
  ⟨⟨14, 84, 809⟩, 203669672192881555, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_85 : CertifiedEndpoint :=
  ⟨⟨14, 85, 702⟩, 177274589460970815, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_86 : CertifiedEndpoint :=
  ⟨⟨14, 86, 593⟩, 149582102142246683, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_87 : CertifiedEndpoint :=
  ⟨⟨14, 87, 482⟩, 120571284634635571, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_88 : CertifiedEndpoint :=
  ⟨⟨14, 88, 367⟩, 89659690422171677, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_89 : CertifiedEndpoint :=
  ⟨⟨14, 89, 250⟩, 57373964415291235, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_90 : CertifiedEndpoint :=
  ⟨⟨14, 90, 131⟩, 23693181011920657, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_15 : CertifiedEndpoint :=
  ⟨⟨15, 15, 3858⟩, 120252760414872183, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_16 : CertifiedEndpoint :=
  ⟨⟨15, 16, 3836⟩, 124256276606215566, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_17 : CertifiedEndpoint :=
  ⟨⟨15, 17, 3814⟩, 128205743570929969, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_18 : CertifiedEndpoint :=
  ⟨⟨15, 18, 3792⟩, 141600635837773092, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_19 : CertifiedEndpoint :=
  ⟨⟨15, 19, 3770⟩, 154826989394247965, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_20 : CertifiedEndpoint :=
  ⟨⟨15, 20, 3747⟩, 167839851952312847, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_21 : CertifiedEndpoint :=
  ⟨⟨15, 21, 3725⟩, 180725382783376370, .intrinsic (by decide +kernel) (by decide)⟩

def endpointBlock09 : List CertifiedEndpoint := [
  endpoint_13_47, endpoint_13_48, endpoint_13_49, endpoint_13_50, endpoint_13_51, endpoint_13_52, endpoint_13_53,
  endpoint_13_54, endpoint_13_55, endpoint_13_56, endpoint_13_57, endpoint_13_58, endpoint_13_59, endpoint_13_60,
  endpoint_13_61, endpoint_13_62, endpoint_13_63, endpoint_13_64, endpoint_13_65, endpoint_13_66, endpoint_13_67,
  endpoint_13_68, endpoint_13_69, endpoint_13_70, endpoint_13_71, endpoint_13_72, endpoint_13_73, endpoint_13_74,
  endpoint_13_75, endpoint_13_76, endpoint_13_77, endpoint_13_78, endpoint_13_79, endpoint_13_80, endpoint_13_81,
  endpoint_13_82, endpoint_13_83, endpoint_13_84, endpoint_13_85, endpoint_13_86, endpoint_13_87, endpoint_13_88,
  endpoint_13_89, endpoint_13_90, endpoint_13_91, endpoint_13_92, endpoint_14_14, endpoint_14_15, endpoint_14_16,
  endpoint_14_17, endpoint_14_18, endpoint_14_19, endpoint_14_20, endpoint_14_21, endpoint_14_22, endpoint_14_23,
  endpoint_14_24, endpoint_14_25, endpoint_14_26, endpoint_14_27, endpoint_14_28, endpoint_14_29, endpoint_14_30,
  endpoint_14_31, endpoint_14_32, endpoint_14_33, endpoint_14_34, endpoint_14_35, endpoint_14_36, endpoint_14_37,
  endpoint_14_38, endpoint_14_39, endpoint_14_40, endpoint_14_41, endpoint_14_42, endpoint_14_43, endpoint_14_44,
  endpoint_14_45, endpoint_14_46, endpoint_14_47, endpoint_14_48, endpoint_14_49, endpoint_14_50, endpoint_14_51,
  endpoint_14_52, endpoint_14_53, endpoint_14_54, endpoint_14_55, endpoint_14_56, endpoint_14_57, endpoint_14_58,
  endpoint_14_59, endpoint_14_60, endpoint_14_61, endpoint_14_62, endpoint_14_63, endpoint_14_64, endpoint_14_65,
  endpoint_14_66, endpoint_14_67, endpoint_14_68, endpoint_14_69, endpoint_14_70, endpoint_14_71, endpoint_14_72,
  endpoint_14_73, endpoint_14_74, endpoint_14_75, endpoint_14_76, endpoint_14_77, endpoint_14_78, endpoint_14_79,
  endpoint_14_80, endpoint_14_81, endpoint_14_82, endpoint_14_83, endpoint_14_84, endpoint_14_85, endpoint_14_86,
  endpoint_14_87, endpoint_14_88, endpoint_14_89, endpoint_14_90, endpoint_15_15, endpoint_15_16, endpoint_15_17,
  endpoint_15_18, endpoint_15_19, endpoint_15_20, endpoint_15_21
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
