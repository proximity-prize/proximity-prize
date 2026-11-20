import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_11_82_flag : Flag := ⟨11, 82, 1599⟩
private def endpoint_11_82_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_11_82_base : receiptBase endpoint_11_82_flag endpoint_11_82_sources = some 187710432605135989 := by decide +kernel
private theorem endpoint_11_82_w0 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 2 187710432605135989 = some 187710432605135989 := by decide +kernel
private theorem endpoint_11_82_w2 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 2 2 187710432605135989 = some 187710432605135989 := by decide +kernel
private theorem endpoint_11_82_p4 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 4 187710432605135989 = some 187710432605135989 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 2 2 187710432605135989 187710432605135989 187710432605135989 endpoint_11_82_w0 endpoint_11_82_w2
private theorem endpoint_11_82_w4 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 4 2 187710432605135989 = some 187710432605135989 := by decide +kernel
private theorem endpoint_11_82_p6 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 6 187710432605135989 = some 187710432605135989 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 4 2 187710432605135989 187710432605135989 187710432605135989 endpoint_11_82_p4 endpoint_11_82_w4
private theorem endpoint_11_82_w6 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 6 2 187710432605135989 = some 187710432605135989 := by decide +kernel
private theorem endpoint_11_82_p8 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 8 187710432605135989 = some 187710432605135989 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 6 2 187710432605135989 187710432605135989 187710432605135989 endpoint_11_82_p6 endpoint_11_82_w6
private theorem endpoint_11_82_w8 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 8 2 187710432605135989 = some 187710432605135989 := by decide +kernel
private theorem endpoint_11_82_p10 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 10 187710432605135989 = some 187710432605135989 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 8 2 187710432605135989 187710432605135989 187710432605135989 endpoint_11_82_p8 endpoint_11_82_w8
def endpoint_11_82 : CertifiedEndpoint :=
  ⟨⟨11, 82, 1599⟩, 187710432605135989, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_11_82_flag endpoint_11_82_sources 10 187710432605135989 187710432605135989 rfl endpoint_11_82_base endpoint_11_82_p10) (by decide)⟩
private def endpoint_11_83_flag : Flag := ⟨11, 83, 1503⟩
private def endpoint_11_83_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_11_83_base : receiptBase endpoint_11_83_flag endpoint_11_83_sources = some 178444099447813309 := by decide +kernel
private theorem endpoint_11_83_w0 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 0 2 178444099447813309 = some 178444099447813309 := by decide +kernel
private theorem endpoint_11_83_w2 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 2 2 178444099447813309 = some 178444099447813309 := by decide +kernel
private theorem endpoint_11_83_p4 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 0 4 178444099447813309 = some 178444099447813309 :=
  join_receipt_window endpoint_11_83_flag endpoint_11_83_sources 0 2 2 178444099447813309 178444099447813309 178444099447813309 endpoint_11_83_w0 endpoint_11_83_w2
private theorem endpoint_11_83_w4 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 4 2 178444099447813309 = some 178444099447813309 := by decide +kernel
private theorem endpoint_11_83_p6 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 0 6 178444099447813309 = some 178444099447813309 :=
  join_receipt_window endpoint_11_83_flag endpoint_11_83_sources 0 4 2 178444099447813309 178444099447813309 178444099447813309 endpoint_11_83_p4 endpoint_11_83_w4
private theorem endpoint_11_83_w6 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 6 2 178444099447813309 = some 178444099447813309 := by decide +kernel
private theorem endpoint_11_83_p8 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 0 8 178444099447813309 = some 178444099447813309 :=
  join_receipt_window endpoint_11_83_flag endpoint_11_83_sources 0 6 2 178444099447813309 178444099447813309 178444099447813309 endpoint_11_83_p6 endpoint_11_83_w6
private theorem endpoint_11_83_w8 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 8 2 178444099447813309 = some 178444099447813309 := by decide +kernel
private theorem endpoint_11_83_p10 : receiptWindow endpoint_11_83_flag endpoint_11_83_sources 0 10 178444099447813309 = some 178444099447813309 :=
  join_receipt_window endpoint_11_83_flag endpoint_11_83_sources 0 8 2 178444099447813309 178444099447813309 178444099447813309 endpoint_11_83_p8 endpoint_11_83_w8
def endpoint_11_83 : CertifiedEndpoint :=
  ⟨⟨11, 83, 1503⟩, 178444099447813309, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_11_83_flag endpoint_11_83_sources 10 178444099447813309 178444099447813309 rfl endpoint_11_83_base endpoint_11_83_p10) (by decide)⟩
private def endpoint_11_84_flag : Flag := ⟨11, 84, 1404⟩
private def endpoint_11_84_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_11_84_base : receiptBase endpoint_11_84_flag endpoint_11_84_sources = some 168573433124045985 := by decide +kernel
private theorem endpoint_11_84_w0 : receiptWindow endpoint_11_84_flag endpoint_11_84_sources 0 2 168573433124045985 = some 168573433124045985 := by decide +kernel
private theorem endpoint_11_84_w2 : receiptWindow endpoint_11_84_flag endpoint_11_84_sources 2 2 168573433124045985 = some 168573433124045985 := by decide +kernel
private theorem endpoint_11_84_p4 : receiptWindow endpoint_11_84_flag endpoint_11_84_sources 0 4 168573433124045985 = some 168573433124045985 :=
  join_receipt_window endpoint_11_84_flag endpoint_11_84_sources 0 2 2 168573433124045985 168573433124045985 168573433124045985 endpoint_11_84_w0 endpoint_11_84_w2
private theorem endpoint_11_84_w4 : receiptWindow endpoint_11_84_flag endpoint_11_84_sources 4 2 168573433124045985 = some 168573433124045985 := by decide +kernel
private theorem endpoint_11_84_p6 : receiptWindow endpoint_11_84_flag endpoint_11_84_sources 0 6 168573433124045985 = some 168573433124045985 :=
  join_receipt_window endpoint_11_84_flag endpoint_11_84_sources 0 4 2 168573433124045985 168573433124045985 168573433124045985 endpoint_11_84_p4 endpoint_11_84_w4
private theorem endpoint_11_84_w6 : receiptWindow endpoint_11_84_flag endpoint_11_84_sources 6 2 168573433124045985 = some 168573433124045985 := by decide +kernel
private theorem endpoint_11_84_p8 : receiptWindow endpoint_11_84_flag endpoint_11_84_sources 0 8 168573433124045985 = some 168573433124045985 :=
  join_receipt_window endpoint_11_84_flag endpoint_11_84_sources 0 6 2 168573433124045985 168573433124045985 168573433124045985 endpoint_11_84_p6 endpoint_11_84_w6
private theorem endpoint_11_84_w8 : receiptWindow endpoint_11_84_flag endpoint_11_84_sources 8 2 168573433124045985 = some 168573433124045985 := by decide +kernel
private theorem endpoint_11_84_p10 : receiptWindow endpoint_11_84_flag endpoint_11_84_sources 0 10 168573433124045985 = some 168573433124045985 :=
  join_receipt_window endpoint_11_84_flag endpoint_11_84_sources 0 8 2 168573433124045985 168573433124045985 168573433124045985 endpoint_11_84_p8 endpoint_11_84_w8
def endpoint_11_84 : CertifiedEndpoint :=
  ⟨⟨11, 84, 1404⟩, 168573433124045985, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_11_84_flag endpoint_11_84_sources 10 168573433124045985 168573433124045985 rfl endpoint_11_84_base endpoint_11_84_p10) (by decide)⟩
private def endpoint_11_85_flag : Flag := ⟨11, 85, 1303⟩
private def endpoint_11_85_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_11_85_base : receiptBase endpoint_11_85_flag endpoint_11_85_sources = some 158207083945667315 := by decide +kernel
private theorem endpoint_11_85_w0 : receiptWindow endpoint_11_85_flag endpoint_11_85_sources 0 2 158207083945667315 = some 158207083945667315 := by decide +kernel
private theorem endpoint_11_85_w2 : receiptWindow endpoint_11_85_flag endpoint_11_85_sources 2 2 158207083945667315 = some 158207083945667315 := by decide +kernel
private theorem endpoint_11_85_p4 : receiptWindow endpoint_11_85_flag endpoint_11_85_sources 0 4 158207083945667315 = some 158207083945667315 :=
  join_receipt_window endpoint_11_85_flag endpoint_11_85_sources 0 2 2 158207083945667315 158207083945667315 158207083945667315 endpoint_11_85_w0 endpoint_11_85_w2
private theorem endpoint_11_85_w4 : receiptWindow endpoint_11_85_flag endpoint_11_85_sources 4 2 158207083945667315 = some 158207083945667315 := by decide +kernel
private theorem endpoint_11_85_p6 : receiptWindow endpoint_11_85_flag endpoint_11_85_sources 0 6 158207083945667315 = some 158207083945667315 :=
  join_receipt_window endpoint_11_85_flag endpoint_11_85_sources 0 4 2 158207083945667315 158207083945667315 158207083945667315 endpoint_11_85_p4 endpoint_11_85_w4
private theorem endpoint_11_85_w6 : receiptWindow endpoint_11_85_flag endpoint_11_85_sources 6 2 158207083945667315 = some 158207083945667315 := by decide +kernel
private theorem endpoint_11_85_p8 : receiptWindow endpoint_11_85_flag endpoint_11_85_sources 0 8 158207083945667315 = some 158207083945667315 :=
  join_receipt_window endpoint_11_85_flag endpoint_11_85_sources 0 6 2 158207083945667315 158207083945667315 158207083945667315 endpoint_11_85_p6 endpoint_11_85_w6
private theorem endpoint_11_85_w8 : receiptWindow endpoint_11_85_flag endpoint_11_85_sources 8 2 158207083945667315 = some 158207083945667315 := by decide +kernel
private theorem endpoint_11_85_p10 : receiptWindow endpoint_11_85_flag endpoint_11_85_sources 0 10 158207083945667315 = some 158207083945667315 :=
  join_receipt_window endpoint_11_85_flag endpoint_11_85_sources 0 8 2 158207083945667315 158207083945667315 158207083945667315 endpoint_11_85_p8 endpoint_11_85_w8
def endpoint_11_85 : CertifiedEndpoint :=
  ⟨⟨11, 85, 1303⟩, 158207083945667315, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_11_85_flag endpoint_11_85_sources 10 158207083945667315 158207083945667315 rfl endpoint_11_85_base endpoint_11_85_p10) (by decide)⟩
def endpoint_11_86 : CertifiedEndpoint :=
  ⟨⟨11, 86, 1199⟩, 250407114221145659, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_87 : CertifiedEndpoint :=
  ⟨⟨11, 87, 1092⟩, 229899597064504627, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_88 : CertifiedEndpoint :=
  ⟨⟨11, 88, 983⟩, 208363271957898979, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_89 : CertifiedEndpoint :=
  ⟨⟨11, 89, 871⟩, 185556540905809528, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_90 : CertifiedEndpoint :=
  ⟨⟨11, 90, 756⟩, 161454973522015696, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_91 : CertifiedEndpoint :=
  ⟨⟨11, 91, 639⟩, 136264879466384724, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_92 : CertifiedEndpoint :=
  ⟨⟨11, 92, 519⟩, 109736517281323899, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_93 : CertifiedEndpoint :=
  ⟨⟨11, 93, 396⟩, 81845456580612643, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_94 : CertifiedEndpoint :=
  ⟨⟨11, 94, 271⟩, 52806150486191723, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_95 : CertifiedEndpoint :=
  ⟨⟨11, 95, 143⟩, 22360714078394900, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_12 : CertifiedEndpoint :=
  ⟨⟨12, 12, 4242⟩, 86176620373242762, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_13 : CertifiedEndpoint :=
  ⟨⟨12, 13, 4222⟩, 89854098312454886, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_14 : CertifiedEndpoint :=
  ⟨⟨12, 14, 4203⟩, 93515048825407817, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_15 : CertifiedEndpoint :=
  ⟨⟨12, 15, 4183⟩, 105458628650208616, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_16 : CertifiedEndpoint :=
  ⟨⟨12, 16, 4163⟩, 117280348615838561, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_17 : CertifiedEndpoint :=
  ⟨⟨12, 17, 4143⟩, 128980208722297652, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_18 : CertifiedEndpoint :=
  ⟨⟨12, 18, 4123⟩, 140558208969585889, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_19 : CertifiedEndpoint :=
  ⟨⟨12, 19, 4102⟩, 151977188338125275, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_20 : CertifiedEndpoint :=
  ⟨⟨12, 20, 4082⟩, 163308496675384710, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_21 : CertifiedEndpoint :=
  ⟨⟨12, 21, 4061⟩, 174474839750521106, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_22 : CertifiedEndpoint :=
  ⟨⟨12, 22, 4040⟩, 185513378583112460, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_23 : CertifiedEndpoint :=
  ⟨⟨12, 23, 4018⟩, 196375063386832399, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_24 : CertifiedEndpoint :=
  ⟨⟨12, 24, 3997⟩, 207155021542646575, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_25 : CertifiedEndpoint :=
  ⟨⟨12, 25, 3975⟩, 217752181286215148, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_26 : CertifiedEndpoint :=
  ⟨⟨12, 26, 3953⟩, 228215592403864491, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_27 : CertifiedEndpoint :=
  ⟨⟨12, 27, 3931⟩, 238545254895594604, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_28 : CertifiedEndpoint :=
  ⟨⟨12, 28, 3908⟩, 248677258016643644, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_29 : CertifiedEndpoint :=
  ⟨⟨12, 29, 3885⟩, 258669568128399266, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_12_30_flag : Flag := ⟨12, 30, 3862⟩
private def endpoint_12_30_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_30_base : receiptBase endpoint_12_30_flag endpoint_12_30_sources = some 178915523783184070 := by decide +kernel
private theorem endpoint_12_30_w0 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 2 178915523783184070 = some 178915523783184070 := by decide +kernel
private theorem endpoint_12_30_w2 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 2 2 178915523783184070 = some 178915523783184070 := by decide +kernel
private theorem endpoint_12_30_p4 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 4 178915523783184070 = some 178915523783184070 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 2 2 178915523783184070 178915523783184070 178915523783184070 endpoint_12_30_w0 endpoint_12_30_w2
private theorem endpoint_12_30_w4 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 4 2 178915523783184070 = some 178915523783184070 := by decide +kernel
private theorem endpoint_12_30_p6 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 6 178915523783184070 = some 178915523783184070 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 4 2 178915523783184070 178915523783184070 178915523783184070 endpoint_12_30_p4 endpoint_12_30_w4
private theorem endpoint_12_30_w6 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 6 2 178915523783184070 = some 178915523783184070 := by decide +kernel
private theorem endpoint_12_30_p8 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 8 178915523783184070 = some 178915523783184070 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 6 2 178915523783184070 178915523783184070 178915523783184070 endpoint_12_30_p6 endpoint_12_30_w6
private theorem endpoint_12_30_w8 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 8 2 178915523783184070 = some 178915523783184070 := by decide +kernel
private theorem endpoint_12_30_p10 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 10 178915523783184070 = some 178915523783184070 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 8 2 178915523783184070 178915523783184070 178915523783184070 endpoint_12_30_p8 endpoint_12_30_w8
private theorem endpoint_12_30_w10 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 10 1 178915523783184070 = some 178915523783184070 := by decide +kernel
private theorem endpoint_12_30_p11 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 11 178915523783184070 = some 178915523783184070 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 10 1 178915523783184070 178915523783184070 178915523783184070 endpoint_12_30_p10 endpoint_12_30_w10
def endpoint_12_30 : CertifiedEndpoint :=
  ⟨⟨12, 30, 3862⟩, 178915523783184070, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_30_flag endpoint_12_30_sources 11 178915523783184070 178915523783184070 rfl endpoint_12_30_base endpoint_12_30_p11) (by decide)⟩
private def endpoint_12_31_flag : Flag := ⟨12, 31, 3839⟩
private def endpoint_12_31_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_31_base : receiptBase endpoint_12_31_flag endpoint_12_31_sources = some 182653267687869688 := by decide +kernel
private theorem endpoint_12_31_w0 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 2 182653267687869688 = some 182653267687869688 := by decide +kernel
private theorem endpoint_12_31_w2 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 2 2 182653267687869688 = some 182653267687869688 := by decide +kernel
private theorem endpoint_12_31_p4 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 4 182653267687869688 = some 182653267687869688 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 2 2 182653267687869688 182653267687869688 182653267687869688 endpoint_12_31_w0 endpoint_12_31_w2
private theorem endpoint_12_31_w4 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 4 2 182653267687869688 = some 182653267687869688 := by decide +kernel
private theorem endpoint_12_31_p6 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 6 182653267687869688 = some 182653267687869688 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 4 2 182653267687869688 182653267687869688 182653267687869688 endpoint_12_31_p4 endpoint_12_31_w4
private theorem endpoint_12_31_w6 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 6 2 182653267687869688 = some 182653267687869688 := by decide +kernel
private theorem endpoint_12_31_p8 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 8 182653267687869688 = some 182653267687869688 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 6 2 182653267687869688 182653267687869688 182653267687869688 endpoint_12_31_p6 endpoint_12_31_w6
private theorem endpoint_12_31_w8 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 8 2 182653267687869688 = some 182653267687869688 := by decide +kernel
private theorem endpoint_12_31_p10 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 10 182653267687869688 = some 182653267687869688 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 8 2 182653267687869688 182653267687869688 182653267687869688 endpoint_12_31_p8 endpoint_12_31_w8
private theorem endpoint_12_31_w10 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 10 1 182653267687869688 = some 182653267687869688 := by decide +kernel
private theorem endpoint_12_31_p11 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 11 182653267687869688 = some 182653267687869688 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 10 1 182653267687869688 182653267687869688 182653267687869688 endpoint_12_31_p10 endpoint_12_31_w10
def endpoint_12_31 : CertifiedEndpoint :=
  ⟨⟨12, 31, 3839⟩, 182653267687869688, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_31_flag endpoint_12_31_sources 11 182653267687869688 182653267687869688 rfl endpoint_12_31_base endpoint_12_31_p11) (by decide)⟩
private def endpoint_12_32_flag : Flag := ⟨12, 32, 3815⟩
private def endpoint_12_32_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_32_base : receiptBase endpoint_12_32_flag endpoint_12_32_sources = some 186285509731309385 := by decide +kernel
private theorem endpoint_12_32_w0 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 2 186285509731309385 = some 186285509731309385 := by decide +kernel
private theorem endpoint_12_32_w2 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 2 2 186285509731309385 = some 186285509731309385 := by decide +kernel
private theorem endpoint_12_32_p4 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 4 186285509731309385 = some 186285509731309385 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 2 2 186285509731309385 186285509731309385 186285509731309385 endpoint_12_32_w0 endpoint_12_32_w2
private theorem endpoint_12_32_w4 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 4 2 186285509731309385 = some 186285509731309385 := by decide +kernel
private theorem endpoint_12_32_p6 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 6 186285509731309385 = some 186285509731309385 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 4 2 186285509731309385 186285509731309385 186285509731309385 endpoint_12_32_p4 endpoint_12_32_w4
private theorem endpoint_12_32_w6 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 6 2 186285509731309385 = some 186285509731309385 := by decide +kernel
private theorem endpoint_12_32_p8 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 8 186285509731309385 = some 186285509731309385 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 6 2 186285509731309385 186285509731309385 186285509731309385 endpoint_12_32_p6 endpoint_12_32_w6
private theorem endpoint_12_32_w8 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 8 2 186285509731309385 = some 186285509731309385 := by decide +kernel
private theorem endpoint_12_32_p10 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 10 186285509731309385 = some 186285509731309385 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 8 2 186285509731309385 186285509731309385 186285509731309385 endpoint_12_32_p8 endpoint_12_32_w8
private theorem endpoint_12_32_w10 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 10 1 186285509731309385 = some 186285509731309385 := by decide +kernel
private theorem endpoint_12_32_p11 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 11 186285509731309385 = some 186285509731309385 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 10 1 186285509731309385 186285509731309385 186285509731309385 endpoint_12_32_p10 endpoint_12_32_w10
def endpoint_12_32 : CertifiedEndpoint :=
  ⟨⟨12, 32, 3815⟩, 186285509731309385, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_32_flag endpoint_12_32_sources 11 186285509731309385 186285509731309385 rfl endpoint_12_32_base endpoint_12_32_p11) (by decide)⟩
private def endpoint_12_33_flag : Flag := ⟨12, 33, 3791⟩
private def endpoint_12_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_33_base : receiptBase endpoint_12_33_flag endpoint_12_33_sources = some 189857910241063932 := by decide +kernel
private theorem endpoint_12_33_w0 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 2 189857910241063932 = some 189857910241063932 := by decide +kernel
private theorem endpoint_12_33_w2 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 2 2 189857910241063932 = some 189857910241063932 := by decide +kernel
private theorem endpoint_12_33_p4 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 4 189857910241063932 = some 189857910241063932 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 2 2 189857910241063932 189857910241063932 189857910241063932 endpoint_12_33_w0 endpoint_12_33_w2
private theorem endpoint_12_33_w4 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 4 2 189857910241063932 = some 189857910241063932 := by decide +kernel
private theorem endpoint_12_33_p6 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 6 189857910241063932 = some 189857910241063932 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 4 2 189857910241063932 189857910241063932 189857910241063932 endpoint_12_33_p4 endpoint_12_33_w4
private theorem endpoint_12_33_w6 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 6 2 189857910241063932 = some 189857910241063932 := by decide +kernel
private theorem endpoint_12_33_p8 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 8 189857910241063932 = some 189857910241063932 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 6 2 189857910241063932 189857910241063932 189857910241063932 endpoint_12_33_p6 endpoint_12_33_w6
private theorem endpoint_12_33_w8 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 8 2 189857910241063932 = some 189857910241063932 := by decide +kernel
private theorem endpoint_12_33_p10 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 10 189857910241063932 = some 189857910241063932 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 8 2 189857910241063932 189857910241063932 189857910241063932 endpoint_12_33_p8 endpoint_12_33_w8
private theorem endpoint_12_33_w10 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 10 1 189857910241063932 = some 189857910241063932 := by decide +kernel
private theorem endpoint_12_33_p11 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 11 189857910241063932 = some 189857910241063932 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 10 1 189857910241063932 189857910241063932 189857910241063932 endpoint_12_33_p10 endpoint_12_33_w10
def endpoint_12_33 : CertifiedEndpoint :=
  ⟨⟨12, 33, 3791⟩, 189857910241063932, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_33_flag endpoint_12_33_sources 11 189857910241063932 189857910241063932 rfl endpoint_12_33_base endpoint_12_33_p11) (by decide)⟩
private def endpoint_12_34_flag : Flag := ⟨12, 34, 3767⟩
private def endpoint_12_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_34_base : receiptBase endpoint_12_34_flag endpoint_12_34_sources = some 193370469217133329 := by decide +kernel
private theorem endpoint_12_34_w0 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 2 193370469217133329 = some 193370469217133329 := by decide +kernel
private theorem endpoint_12_34_w2 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 2 2 193370469217133329 = some 193370469217133329 := by decide +kernel
private theorem endpoint_12_34_p4 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 4 193370469217133329 = some 193370469217133329 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 2 2 193370469217133329 193370469217133329 193370469217133329 endpoint_12_34_w0 endpoint_12_34_w2
private theorem endpoint_12_34_w4 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 4 2 193370469217133329 = some 193370469217133329 := by decide +kernel
private theorem endpoint_12_34_p6 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 6 193370469217133329 = some 193370469217133329 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 4 2 193370469217133329 193370469217133329 193370469217133329 endpoint_12_34_p4 endpoint_12_34_w4
private theorem endpoint_12_34_w6 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 6 2 193370469217133329 = some 193370469217133329 := by decide +kernel
private theorem endpoint_12_34_p8 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 8 193370469217133329 = some 193370469217133329 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 6 2 193370469217133329 193370469217133329 193370469217133329 endpoint_12_34_p6 endpoint_12_34_w6
private theorem endpoint_12_34_w8 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 8 2 193370469217133329 = some 193370469217133329 := by decide +kernel
private theorem endpoint_12_34_p10 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 10 193370469217133329 = some 193370469217133329 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 8 2 193370469217133329 193370469217133329 193370469217133329 endpoint_12_34_p8 endpoint_12_34_w8
private theorem endpoint_12_34_w10 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 10 1 193370469217133329 = some 193370469217133329 := by decide +kernel
private theorem endpoint_12_34_p11 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 11 193370469217133329 = some 193370469217133329 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 10 1 193370469217133329 193370469217133329 193370469217133329 endpoint_12_34_p10 endpoint_12_34_w10
def endpoint_12_34 : CertifiedEndpoint :=
  ⟨⟨12, 34, 3767⟩, 193370469217133329, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_34_flag endpoint_12_34_sources 11 193370469217133329 193370469217133329 rfl endpoint_12_34_base endpoint_12_34_p11) (by decide)⟩
private def endpoint_12_35_flag : Flag := ⟨12, 35, 3742⟩
private def endpoint_12_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_35_base : receiptBase endpoint_12_35_flag endpoint_12_35_sources = some 196771420512152711 := by decide +kernel
private theorem endpoint_12_35_w0 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 2 196771420512152711 = some 196771420512152711 := by decide +kernel
private theorem endpoint_12_35_w2 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 2 2 196771420512152711 = some 196771420512152711 := by decide +kernel
private theorem endpoint_12_35_p4 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 4 196771420512152711 = some 196771420512152711 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 2 2 196771420512152711 196771420512152711 196771420512152711 endpoint_12_35_w0 endpoint_12_35_w2
private theorem endpoint_12_35_w4 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 4 2 196771420512152711 = some 196771420512152711 := by decide +kernel
private theorem endpoint_12_35_p6 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 6 196771420512152711 = some 196771420512152711 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 4 2 196771420512152711 196771420512152711 196771420512152711 endpoint_12_35_p4 endpoint_12_35_w4
private theorem endpoint_12_35_w6 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 6 2 196771420512152711 = some 196771420512152711 := by decide +kernel
private theorem endpoint_12_35_p8 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 8 196771420512152711 = some 196771420512152711 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 6 2 196771420512152711 196771420512152711 196771420512152711 endpoint_12_35_p6 endpoint_12_35_w6
private theorem endpoint_12_35_w8 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 8 2 196771420512152711 = some 196771420512152711 := by decide +kernel
private theorem endpoint_12_35_p10 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 10 196771420512152711 = some 196771420512152711 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 8 2 196771420512152711 196771420512152711 196771420512152711 endpoint_12_35_p8 endpoint_12_35_w8
private theorem endpoint_12_35_w10 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 10 1 196771420512152711 = some 196771420512152711 := by decide +kernel
private theorem endpoint_12_35_p11 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 11 196771420512152711 = some 196771420512152711 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 10 1 196771420512152711 196771420512152711 196771420512152711 endpoint_12_35_p10 endpoint_12_35_w10
def endpoint_12_35 : CertifiedEndpoint :=
  ⟨⟨12, 35, 3742⟩, 196771420512152711, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_35_flag endpoint_12_35_sources 11 196771420512152711 196771420512152711 rfl endpoint_12_35_base endpoint_12_35_p11) (by decide)⟩
private def endpoint_12_36_flag : Flag := ⟨12, 36, 3717⟩
private def endpoint_12_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_36_base : receiptBase endpoint_12_36_flag endpoint_12_36_sources = some 200110087945565304 := by decide +kernel
private theorem endpoint_12_36_w0 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 2 200110087945565304 = some 200110087945565304 := by decide +kernel
private theorem endpoint_12_36_w2 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 2 2 200110087945565304 = some 200110087945565304 := by decide +kernel
private theorem endpoint_12_36_p4 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 4 200110087945565304 = some 200110087945565304 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 2 2 200110087945565304 200110087945565304 200110087945565304 endpoint_12_36_w0 endpoint_12_36_w2
private theorem endpoint_12_36_w4 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 4 2 200110087945565304 = some 200110087945565304 := by decide +kernel
private theorem endpoint_12_36_p6 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 6 200110087945565304 = some 200110087945565304 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 4 2 200110087945565304 200110087945565304 200110087945565304 endpoint_12_36_p4 endpoint_12_36_w4
private theorem endpoint_12_36_w6 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 6 2 200110087945565304 = some 200110087945565304 := by decide +kernel
private theorem endpoint_12_36_p8 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 8 200110087945565304 = some 200110087945565304 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 6 2 200110087945565304 200110087945565304 200110087945565304 endpoint_12_36_p6 endpoint_12_36_w6
private theorem endpoint_12_36_w8 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 8 2 200110087945565304 = some 200110087945565304 := by decide +kernel
private theorem endpoint_12_36_p10 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 10 200110087945565304 = some 200110087945565304 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 8 2 200110087945565304 200110087945565304 200110087945565304 endpoint_12_36_p8 endpoint_12_36_w8
private theorem endpoint_12_36_w10 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 10 1 200110087945565304 = some 200110087945565304 := by decide +kernel
private theorem endpoint_12_36_p11 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 11 200110087945565304 = some 200110087945565304 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 10 1 200110087945565304 200110087945565304 200110087945565304 endpoint_12_36_p10 endpoint_12_36_w10
def endpoint_12_36 : CertifiedEndpoint :=
  ⟨⟨12, 36, 3717⟩, 200110087945565304, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_36_flag endpoint_12_36_sources 11 200110087945565304 200110087945565304 rfl endpoint_12_36_base endpoint_12_36_p11) (by decide)⟩
private def endpoint_12_37_flag : Flag := ⟨12, 37, 3692⟩
private def endpoint_12_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_37_base : receiptBase endpoint_12_37_flag endpoint_12_37_sources = some 203386471517371109 := by decide +kernel
private theorem endpoint_12_37_w0 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 2 203386471517371109 = some 203386471517371109 := by decide +kernel
private theorem endpoint_12_37_w2 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 2 2 203386471517371109 = some 203386471517371109 := by decide +kernel
private theorem endpoint_12_37_p4 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 4 203386471517371109 = some 203386471517371109 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 2 2 203386471517371109 203386471517371109 203386471517371109 endpoint_12_37_w0 endpoint_12_37_w2
private theorem endpoint_12_37_w4 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 4 2 203386471517371109 = some 203386471517371109 := by decide +kernel
private theorem endpoint_12_37_p6 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 6 203386471517371109 = some 203386471517371109 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 4 2 203386471517371109 203386471517371109 203386471517371109 endpoint_12_37_p4 endpoint_12_37_w4
private theorem endpoint_12_37_w6 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 6 2 203386471517371109 = some 203386471517371109 := by decide +kernel
private theorem endpoint_12_37_p8 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 8 203386471517371109 = some 203386471517371109 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 6 2 203386471517371109 203386471517371109 203386471517371109 endpoint_12_37_p6 endpoint_12_37_w6
private theorem endpoint_12_37_w8 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 8 2 203386471517371109 = some 203386471517371109 := by decide +kernel
private theorem endpoint_12_37_p10 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 10 203386471517371109 = some 203386471517371109 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 8 2 203386471517371109 203386471517371109 203386471517371109 endpoint_12_37_p8 endpoint_12_37_w8
private theorem endpoint_12_37_w10 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 10 1 203386471517371109 = some 203386471517371109 := by decide +kernel
private theorem endpoint_12_37_p11 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 11 203386471517371109 = some 203386471517371109 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 10 1 203386471517371109 203386471517371109 203386471517371109 endpoint_12_37_p10 endpoint_12_37_w10
def endpoint_12_37 : CertifiedEndpoint :=
  ⟨⟨12, 37, 3692⟩, 203386471517371109, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_37_flag endpoint_12_37_sources 11 203386471517371109 203386471517371109 rfl endpoint_12_37_base endpoint_12_37_p11) (by decide)⟩
private def endpoint_12_38_flag : Flag := ⟨12, 38, 3666⟩
private def endpoint_12_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_38_base : receiptBase endpoint_12_38_flag endpoint_12_38_sources = some 206545141588322803 := by decide +kernel
private theorem endpoint_12_38_w0 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 2 206545141588322803 = some 206545141588322803 := by decide +kernel
private theorem endpoint_12_38_w2 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 2 2 206545141588322803 = some 206545141588322803 := by decide +kernel
private theorem endpoint_12_38_p4 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 4 206545141588322803 = some 206545141588322803 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 2 2 206545141588322803 206545141588322803 206545141588322803 endpoint_12_38_w0 endpoint_12_38_w2
private theorem endpoint_12_38_w4 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 4 2 206545141588322803 = some 206545141588322803 := by decide +kernel
private theorem endpoint_12_38_p6 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 6 206545141588322803 = some 206545141588322803 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 4 2 206545141588322803 206545141588322803 206545141588322803 endpoint_12_38_p4 endpoint_12_38_w4
private theorem endpoint_12_38_w6 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 6 2 206545141588322803 = some 206545141588322803 := by decide +kernel
private theorem endpoint_12_38_p8 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 8 206545141588322803 = some 206545141588322803 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 6 2 206545141588322803 206545141588322803 206545141588322803 endpoint_12_38_p6 endpoint_12_38_w6
private theorem endpoint_12_38_w8 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 8 2 206545141588322803 = some 206545141588322803 := by decide +kernel
private theorem endpoint_12_38_p10 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 10 206545141588322803 = some 206545141588322803 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 8 2 206545141588322803 206545141588322803 206545141588322803 endpoint_12_38_p8 endpoint_12_38_w8
private theorem endpoint_12_38_w10 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 10 1 206545141588322803 = some 206545141588322803 := by decide +kernel
private theorem endpoint_12_38_p11 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 11 206545141588322803 = some 206545141588322803 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 10 1 206545141588322803 206545141588322803 206545141588322803 endpoint_12_38_p10 endpoint_12_38_w10
def endpoint_12_38 : CertifiedEndpoint :=
  ⟨⟨12, 38, 3666⟩, 206545141588322803, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_38_flag endpoint_12_38_sources 11 206545141588322803 206545141588322803 rfl endpoint_12_38_base endpoint_12_38_p11) (by decide)⟩
private def endpoint_12_39_flag : Flag := ⟨12, 39, 3640⟩
private def endpoint_12_39_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_39_base : receiptBase endpoint_12_39_flag endpoint_12_39_sources = some 210477531896284709 := by decide +kernel
private theorem endpoint_12_39_w0 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 2 210477531896284709 = some 210477531896284709 := by decide +kernel
private theorem endpoint_12_39_w2 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 2 2 210477531896284709 = some 210477531896284709 := by decide +kernel
private theorem endpoint_12_39_p4 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 4 210477531896284709 = some 210477531896284709 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 2 2 210477531896284709 210477531896284709 210477531896284709 endpoint_12_39_w0 endpoint_12_39_w2
private theorem endpoint_12_39_w4 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 4 2 210477531896284709 = some 210477531896284709 := by decide +kernel
private theorem endpoint_12_39_p6 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 6 210477531896284709 = some 210477531896284709 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 4 2 210477531896284709 210477531896284709 210477531896284709 endpoint_12_39_p4 endpoint_12_39_w4
private theorem endpoint_12_39_w6 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 6 2 210477531896284709 = some 210477531896284709 := by decide +kernel
private theorem endpoint_12_39_p8 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 8 210477531896284709 = some 210477531896284709 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 6 2 210477531896284709 210477531896284709 210477531896284709 endpoint_12_39_p6 endpoint_12_39_w6
private theorem endpoint_12_39_w8 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 8 2 210477531896284709 = some 210477531896284709 := by decide +kernel
private theorem endpoint_12_39_p10 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 10 210477531896284709 = some 210477531896284709 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 8 2 210477531896284709 210477531896284709 210477531896284709 endpoint_12_39_p8 endpoint_12_39_w8
private theorem endpoint_12_39_w10 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 10 1 210477531896284709 = some 210477531896284709 := by decide +kernel
private theorem endpoint_12_39_p11 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 11 210477531896284709 = some 210477531896284709 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 10 1 210477531896284709 210477531896284709 210477531896284709 endpoint_12_39_p10 endpoint_12_39_w10
def endpoint_12_39 : CertifiedEndpoint :=
  ⟨⟨12, 39, 3640⟩, 210477531896284709, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_39_flag endpoint_12_39_sources 11 210477531896284709 210477531896284709 rfl endpoint_12_39_base endpoint_12_39_p11) (by decide)⟩
private def endpoint_12_40_flag : Flag := ⟨12, 40, 3613⟩
private def endpoint_12_40_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_40_base : receiptBase endpoint_12_40_flag endpoint_12_40_sources = some 213415058766740437 := by decide +kernel
private theorem endpoint_12_40_w0 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 2 213415058766740437 = some 213415058766740437 := by decide +kernel
private theorem endpoint_12_40_w2 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 2 2 213415058766740437 = some 213415058766740437 := by decide +kernel
private theorem endpoint_12_40_p4 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 4 213415058766740437 = some 213415058766740437 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 2 2 213415058766740437 213415058766740437 213415058766740437 endpoint_12_40_w0 endpoint_12_40_w2
private theorem endpoint_12_40_w4 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 4 2 213415058766740437 = some 213415058766740437 := by decide +kernel
private theorem endpoint_12_40_p6 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 6 213415058766740437 = some 213415058766740437 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 4 2 213415058766740437 213415058766740437 213415058766740437 endpoint_12_40_p4 endpoint_12_40_w4
private theorem endpoint_12_40_w6 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 6 2 213415058766740437 = some 213415058766740437 := by decide +kernel
private theorem endpoint_12_40_p8 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 8 213415058766740437 = some 213415058766740437 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 6 2 213415058766740437 213415058766740437 213415058766740437 endpoint_12_40_p6 endpoint_12_40_w6
private theorem endpoint_12_40_w8 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 8 2 213415058766740437 = some 213415058766740437 := by decide +kernel
private theorem endpoint_12_40_p10 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 10 213415058766740437 = some 213415058766740437 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 8 2 213415058766740437 213415058766740437 213415058766740437 endpoint_12_40_p8 endpoint_12_40_w8
private theorem endpoint_12_40_w10 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 10 1 213415058766740437 = some 213415058766740437 := by decide +kernel
private theorem endpoint_12_40_p11 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 11 213415058766740437 = some 213415058766740437 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 10 1 213415058766740437 213415058766740437 213415058766740437 endpoint_12_40_p10 endpoint_12_40_w10
def endpoint_12_40 : CertifiedEndpoint :=
  ⟨⟨12, 40, 3613⟩, 213415058766740437, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_40_flag endpoint_12_40_sources 11 213415058766740437 213415058766740437 rfl endpoint_12_40_base endpoint_12_40_p11) (by decide)⟩
private def endpoint_12_41_flag : Flag := ⟨12, 41, 3586⟩
private def endpoint_12_41_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_41_base : receiptBase endpoint_12_41_flag endpoint_12_41_sources = some 216285669055854681 := by decide +kernel
private theorem endpoint_12_41_w0 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 2 216285669055854681 = some 216285669055854681 := by decide +kernel
private theorem endpoint_12_41_w2 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 2 2 216285669055854681 = some 216285669055854681 := by decide +kernel
private theorem endpoint_12_41_p4 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 4 216285669055854681 = some 216285669055854681 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 2 2 216285669055854681 216285669055854681 216285669055854681 endpoint_12_41_w0 endpoint_12_41_w2
private theorem endpoint_12_41_w4 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 4 2 216285669055854681 = some 216285669055854681 := by decide +kernel
private theorem endpoint_12_41_p6 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 6 216285669055854681 = some 216285669055854681 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 4 2 216285669055854681 216285669055854681 216285669055854681 endpoint_12_41_p4 endpoint_12_41_w4
private theorem endpoint_12_41_w6 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 6 2 216285669055854681 = some 216285669055854681 := by decide +kernel
private theorem endpoint_12_41_p8 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 8 216285669055854681 = some 216285669055854681 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 6 2 216285669055854681 216285669055854681 216285669055854681 endpoint_12_41_p6 endpoint_12_41_w6
private theorem endpoint_12_41_w8 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 8 2 216285669055854681 = some 216285669055854681 := by decide +kernel
private theorem endpoint_12_41_p10 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 10 216285669055854681 = some 216285669055854681 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 8 2 216285669055854681 216285669055854681 216285669055854681 endpoint_12_41_p8 endpoint_12_41_w8
private theorem endpoint_12_41_w10 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 10 1 216285669055854681 = some 216285669055854681 := by decide +kernel
private theorem endpoint_12_41_p11 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 11 216285669055854681 = some 216285669055854681 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 10 1 216285669055854681 216285669055854681 216285669055854681 endpoint_12_41_p10 endpoint_12_41_w10
def endpoint_12_41 : CertifiedEndpoint :=
  ⟨⟨12, 41, 3586⟩, 216285669055854681, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_41_flag endpoint_12_41_sources 11 216285669055854681 216285669055854681 rfl endpoint_12_41_base endpoint_12_41_p11) (by decide)⟩
private def endpoint_12_42_flag : Flag := ⟨12, 42, 3558⟩
private def endpoint_12_42_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_42_base : receiptBase endpoint_12_42_flag endpoint_12_42_sources = some 219028735849036369 := by decide +kernel
private theorem endpoint_12_42_w0 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 2 219028735849036369 = some 219028735849036369 := by decide +kernel
private theorem endpoint_12_42_w2 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 2 2 219028735849036369 = some 219028735849036369 := by decide +kernel
private theorem endpoint_12_42_p4 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 4 219028735849036369 = some 219028735849036369 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 2 2 219028735849036369 219028735849036369 219028735849036369 endpoint_12_42_w0 endpoint_12_42_w2
private theorem endpoint_12_42_w4 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 4 2 219028735849036369 = some 219028735849036369 := by decide +kernel
private theorem endpoint_12_42_p6 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 6 219028735849036369 = some 219028735849036369 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 4 2 219028735849036369 219028735849036369 219028735849036369 endpoint_12_42_p4 endpoint_12_42_w4
private theorem endpoint_12_42_w6 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 6 2 219028735849036369 = some 219028735849036369 := by decide +kernel
private theorem endpoint_12_42_p8 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 8 219028735849036369 = some 219028735849036369 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 6 2 219028735849036369 219028735849036369 219028735849036369 endpoint_12_42_p6 endpoint_12_42_w6
private theorem endpoint_12_42_w8 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 8 2 219028735849036369 = some 219028735849036369 := by decide +kernel
private theorem endpoint_12_42_p10 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 10 219028735849036369 = some 219028735849036369 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 8 2 219028735849036369 219028735849036369 219028735849036369 endpoint_12_42_p8 endpoint_12_42_w8
private theorem endpoint_12_42_w10 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 10 1 219028735849036369 = some 219028735849036369 := by decide +kernel
private theorem endpoint_12_42_p11 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 11 219028735849036369 = some 219028735849036369 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 10 1 219028735849036369 219028735849036369 219028735849036369 endpoint_12_42_p10 endpoint_12_42_w10
def endpoint_12_42 : CertifiedEndpoint :=
  ⟨⟨12, 42, 3558⟩, 219028735849036369, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_42_flag endpoint_12_42_sources 11 219028735849036369 219028735849036369 rfl endpoint_12_42_base endpoint_12_42_p11) (by decide)⟩
private def endpoint_12_43_flag : Flag := ⟨12, 43, 3530⟩
private def endpoint_12_43_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_43_base : receiptBase endpoint_12_43_flag endpoint_12_43_sources = some 221702452730645973 := by decide +kernel
private theorem endpoint_12_43_w0 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 2 221702452730645973 = some 221702452730645973 := by decide +kernel
private theorem endpoint_12_43_w2 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 2 2 221702452730645973 = some 221702452730645973 := by decide +kernel
private theorem endpoint_12_43_p4 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 4 221702452730645973 = some 221702452730645973 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 2 2 221702452730645973 221702452730645973 221702452730645973 endpoint_12_43_w0 endpoint_12_43_w2
private theorem endpoint_12_43_w4 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 4 2 221702452730645973 = some 221702452730645973 := by decide +kernel
private theorem endpoint_12_43_p6 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 6 221702452730645973 = some 221702452730645973 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 4 2 221702452730645973 221702452730645973 221702452730645973 endpoint_12_43_p4 endpoint_12_43_w4
private theorem endpoint_12_43_w6 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 6 2 221702452730645973 = some 221702452730645973 := by decide +kernel
private theorem endpoint_12_43_p8 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 8 221702452730645973 = some 221702452730645973 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 6 2 221702452730645973 221702452730645973 221702452730645973 endpoint_12_43_p6 endpoint_12_43_w6
private theorem endpoint_12_43_w8 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 8 2 221702452730645973 = some 221702452730645973 := by decide +kernel
private theorem endpoint_12_43_p10 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 10 221702452730645973 = some 221702452730645973 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 8 2 221702452730645973 221702452730645973 221702452730645973 endpoint_12_43_p8 endpoint_12_43_w8
private theorem endpoint_12_43_w10 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 10 1 221702452730645973 = some 221702452730645973 := by decide +kernel
private theorem endpoint_12_43_p11 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 11 221702452730645973 = some 221702452730645973 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 10 1 221702452730645973 221702452730645973 221702452730645973 endpoint_12_43_p10 endpoint_12_43_w10
def endpoint_12_43 : CertifiedEndpoint :=
  ⟨⟨12, 43, 3530⟩, 221702452730645973, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_43_flag endpoint_12_43_sources 11 221702452730645973 221702452730645973 rfl endpoint_12_43_base endpoint_12_43_p11) (by decide)⟩
private def endpoint_12_44_flag : Flag := ⟨12, 44, 3502⟩
private def endpoint_12_44_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_44_base : receiptBase endpoint_12_44_flag endpoint_12_44_sources = some 224306819700683494 := by decide +kernel
private theorem endpoint_12_44_w0 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 2 224306819700683494 = some 224306819700683494 := by decide +kernel
private theorem endpoint_12_44_w2 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 2 2 224306819700683494 = some 224306819700683494 := by decide +kernel
private theorem endpoint_12_44_p4 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 4 224306819700683494 = some 224306819700683494 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 2 2 224306819700683494 224306819700683494 224306819700683494 endpoint_12_44_w0 endpoint_12_44_w2
private theorem endpoint_12_44_w4 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 4 2 224306819700683494 = some 224306819700683494 := by decide +kernel
private theorem endpoint_12_44_p6 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 6 224306819700683494 = some 224306819700683494 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 4 2 224306819700683494 224306819700683494 224306819700683494 endpoint_12_44_p4 endpoint_12_44_w4
private theorem endpoint_12_44_w6 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 6 2 224306819700683494 = some 224306819700683494 := by decide +kernel
private theorem endpoint_12_44_p8 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 8 224306819700683494 = some 224306819700683494 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 6 2 224306819700683494 224306819700683494 224306819700683494 endpoint_12_44_p6 endpoint_12_44_w6
private theorem endpoint_12_44_w8 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 8 2 224306819700683494 = some 224306819700683494 := by decide +kernel
private theorem endpoint_12_44_p10 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 10 224306819700683494 = some 224306819700683494 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 8 2 224306819700683494 224306819700683494 224306819700683494 endpoint_12_44_p8 endpoint_12_44_w8
private theorem endpoint_12_44_w10 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 10 1 224306819700683494 = some 224306819700683494 := by decide +kernel
private theorem endpoint_12_44_p11 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 11 224306819700683494 = some 224306819700683494 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 10 1 224306819700683494 224306819700683494 224306819700683494 endpoint_12_44_p10 endpoint_12_44_w10
def endpoint_12_44 : CertifiedEndpoint :=
  ⟨⟨12, 44, 3502⟩, 224306819700683494, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_44_flag endpoint_12_44_sources 11 224306819700683494 224306819700683494 rfl endpoint_12_44_base endpoint_12_44_p11) (by decide)⟩
private def endpoint_12_45_flag : Flag := ⟨12, 45, 3473⟩
private def endpoint_12_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_45_base : receiptBase endpoint_12_45_flag endpoint_12_45_sources = some 226777559849211960 := by decide +kernel
private theorem endpoint_12_45_w0 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 2 226777559849211960 = some 228676710863914329 := by decide +kernel
private theorem endpoint_12_45_w2 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 2 2 228676710863914329 = some 228676710863914329 := by decide +kernel
private theorem endpoint_12_45_p4 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 4 226777559849211960 = some 228676710863914329 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 2 2 226777559849211960 228676710863914329 228676710863914329 endpoint_12_45_w0 endpoint_12_45_w2
private theorem endpoint_12_45_w4 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 4 2 228676710863914329 = some 228676710863914329 := by decide +kernel
private theorem endpoint_12_45_p6 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 6 226777559849211960 = some 228676710863914329 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 4 2 226777559849211960 228676710863914329 228676710863914329 endpoint_12_45_p4 endpoint_12_45_w4
private theorem endpoint_12_45_w6 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 6 2 228676710863914329 = some 228676710863914329 := by decide +kernel
private theorem endpoint_12_45_p8 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 8 226777559849211960 = some 228676710863914329 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 6 2 226777559849211960 228676710863914329 228676710863914329 endpoint_12_45_p6 endpoint_12_45_w6
private theorem endpoint_12_45_w8 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 8 2 228676710863914329 = some 228676710863914329 := by decide +kernel
private theorem endpoint_12_45_p10 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 10 226777559849211960 = some 228676710863914329 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 8 2 226777559849211960 228676710863914329 228676710863914329 endpoint_12_45_p8 endpoint_12_45_w8
private theorem endpoint_12_45_w10 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 10 1 228676710863914329 = some 228676710863914329 := by decide +kernel
private theorem endpoint_12_45_p11 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 11 226777559849211960 = some 228676710863914329 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 10 1 226777559849211960 228676710863914329 228676710863914329 endpoint_12_45_p10 endpoint_12_45_w10
def endpoint_12_45 : CertifiedEndpoint :=
  ⟨⟨12, 45, 3473⟩, 228676710863914329, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_45_flag endpoint_12_45_sources 11 226777559849211960 228676710863914329 rfl endpoint_12_45_base endpoint_12_45_p11) (by decide)⟩
private def endpoint_12_46_flag : Flag := ⟨12, 46, 3443⟩
private def endpoint_12_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_46_base : receiptBase endpoint_12_46_flag endpoint_12_46_sources = some 229111023180885472 := by decide +kernel
private theorem endpoint_12_46_w0 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 2 229111023180885472 = some 233606649172911160 := by decide +kernel
private theorem endpoint_12_46_w2 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 2 2 233606649172911160 = some 233606649172911160 := by decide +kernel
private theorem endpoint_12_46_p4 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 4 229111023180885472 = some 233606649172911160 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 2 2 229111023180885472 233606649172911160 233606649172911160 endpoint_12_46_w0 endpoint_12_46_w2
private theorem endpoint_12_46_w4 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 4 2 233606649172911160 = some 233606649172911160 := by decide +kernel
private theorem endpoint_12_46_p6 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 6 229111023180885472 = some 233606649172911160 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 4 2 229111023180885472 233606649172911160 233606649172911160 endpoint_12_46_p4 endpoint_12_46_w4
private theorem endpoint_12_46_w6 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 6 2 233606649172911160 = some 233606649172911160 := by decide +kernel
private theorem endpoint_12_46_p8 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 8 229111023180885472 = some 233606649172911160 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 6 2 229111023180885472 233606649172911160 233606649172911160 endpoint_12_46_p6 endpoint_12_46_w6
private theorem endpoint_12_46_w8 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 8 2 233606649172911160 = some 233606649172911160 := by decide +kernel
private theorem endpoint_12_46_p10 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 10 229111023180885472 = some 233606649172911160 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 8 2 229111023180885472 233606649172911160 233606649172911160 endpoint_12_46_p8 endpoint_12_46_w8
private theorem endpoint_12_46_w10 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 10 1 233606649172911160 = some 233606649172911160 := by decide +kernel
private theorem endpoint_12_46_p11 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 11 229111023180885472 = some 233606649172911160 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 10 1 229111023180885472 233606649172911160 233606649172911160 endpoint_12_46_p10 endpoint_12_46_w10
def endpoint_12_46 : CertifiedEndpoint :=
  ⟨⟨12, 46, 3443⟩, 233606649172911160, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_46_flag endpoint_12_46_sources 11 229111023180885472 233606649172911160 rfl endpoint_12_46_base endpoint_12_46_p11) (by decide)⟩
private def endpoint_12_47_flag : Flag := ⟨12, 47, 3413⟩
private def endpoint_12_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_47_base : receiptBase endpoint_12_47_flag endpoint_12_47_sources = some 231370269940525702 := by decide +kernel
private theorem endpoint_12_47_w0 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 2 231370269940525702 = some 238480785850032609 := by decide +kernel
private theorem endpoint_12_47_w2 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 2 2 238480785850032609 = some 238480785850032609 := by decide +kernel
private theorem endpoint_12_47_p4 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 4 231370269940525702 = some 238480785850032609 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 2 2 231370269940525702 238480785850032609 238480785850032609 endpoint_12_47_w0 endpoint_12_47_w2
private theorem endpoint_12_47_w4 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 4 2 238480785850032609 = some 238480785850032609 := by decide +kernel
private theorem endpoint_12_47_p6 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 6 231370269940525702 = some 238480785850032609 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 4 2 231370269940525702 238480785850032609 238480785850032609 endpoint_12_47_p4 endpoint_12_47_w4
private theorem endpoint_12_47_w6 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 6 2 238480785850032609 = some 238480785850032609 := by decide +kernel
private theorem endpoint_12_47_p8 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 8 231370269940525702 = some 238480785850032609 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 6 2 231370269940525702 238480785850032609 238480785850032609 endpoint_12_47_p6 endpoint_12_47_w6
private theorem endpoint_12_47_w8 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 8 2 238480785850032609 = some 238480785850032609 := by decide +kernel
private theorem endpoint_12_47_p10 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 10 231370269940525702 = some 238480785850032609 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 8 2 231370269940525702 238480785850032609 238480785850032609 endpoint_12_47_p8 endpoint_12_47_w8
private theorem endpoint_12_47_w10 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 10 1 238480785850032609 = some 238480785850032609 := by decide +kernel
private theorem endpoint_12_47_p11 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 11 231370269940525702 = some 238480785850032609 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 10 1 231370269940525702 238480785850032609 238480785850032609 endpoint_12_47_p10 endpoint_12_47_w10
def endpoint_12_47 : CertifiedEndpoint :=
  ⟨⟨12, 47, 3413⟩, 238480785850032609, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_47_flag endpoint_12_47_sources 11 231370269940525702 238480785850032609 rfl endpoint_12_47_base endpoint_12_47_p11) (by decide)⟩
private def endpoint_12_48_flag : Flag := ⟨12, 48, 3382⟩
private def endpoint_12_48_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_48_base : receiptBase endpoint_12_48_flag endpoint_12_48_sources = some 234027486460604994 := by decide +kernel
private theorem endpoint_12_48_w0 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 2 234027486460604994 = some 235178233183757760 := by decide +kernel
private theorem endpoint_12_48_w2 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 2 2 235178233183757760 = some 235178233183757760 := by decide +kernel
private theorem endpoint_12_48_p4 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 4 234027486460604994 = some 235178233183757760 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 2 2 234027486460604994 235178233183757760 235178233183757760 endpoint_12_48_w0 endpoint_12_48_w2
private theorem endpoint_12_48_w4 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 4 2 235178233183757760 = some 235178233183757760 := by decide +kernel
private theorem endpoint_12_48_p6 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 6 234027486460604994 = some 235178233183757760 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 4 2 234027486460604994 235178233183757760 235178233183757760 endpoint_12_48_p4 endpoint_12_48_w4
private theorem endpoint_12_48_w6 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 6 2 235178233183757760 = some 235178233183757760 := by decide +kernel
private theorem endpoint_12_48_p8 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 8 234027486460604994 = some 235178233183757760 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 6 2 234027486460604994 235178233183757760 235178233183757760 endpoint_12_48_p6 endpoint_12_48_w6
private theorem endpoint_12_48_w8 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 8 2 235178233183757760 = some 235178233183757760 := by decide +kernel
private theorem endpoint_12_48_p10 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 10 234027486460604994 = some 235178233183757760 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 8 2 234027486460604994 235178233183757760 235178233183757760 endpoint_12_48_p8 endpoint_12_48_w8
private theorem endpoint_12_48_w10 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 10 1 235178233183757760 = some 235178233183757760 := by decide +kernel
private theorem endpoint_12_48_p11 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 11 234027486460604994 = some 235178233183757760 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 10 1 234027486460604994 235178233183757760 235178233183757760 endpoint_12_48_p10 endpoint_12_48_w10
def endpoint_12_48 : CertifiedEndpoint :=
  ⟨⟨12, 48, 3382⟩, 235178233183757760, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_48_flag endpoint_12_48_sources 11 234027486460604994 235178233183757760 rfl endpoint_12_48_base endpoint_12_48_p11) (by decide)⟩
private def endpoint_12_49_flag : Flag := ⟨12, 49, 3350⟩
private def endpoint_12_49_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_49_base : receiptBase endpoint_12_49_flag endpoint_12_49_sources = some 236008304633726827 := by decide +kernel
private theorem endpoint_12_49_w0 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 2 236008304633726827 = some 239670176853623751 := by decide +kernel
private theorem endpoint_12_49_w2 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 2 2 239670176853623751 = some 239670176853623751 := by decide +kernel
private theorem endpoint_12_49_p4 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 4 236008304633726827 = some 239670176853623751 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 2 2 236008304633726827 239670176853623751 239670176853623751 endpoint_12_49_w0 endpoint_12_49_w2
private theorem endpoint_12_49_w4 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 4 2 239670176853623751 = some 239670176853623751 := by decide +kernel
private theorem endpoint_12_49_p6 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 6 236008304633726827 = some 239670176853623751 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 4 2 236008304633726827 239670176853623751 239670176853623751 endpoint_12_49_p4 endpoint_12_49_w4
private theorem endpoint_12_49_w6 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 6 2 239670176853623751 = some 239670176853623751 := by decide +kernel
private theorem endpoint_12_49_p8 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 8 236008304633726827 = some 239670176853623751 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 6 2 236008304633726827 239670176853623751 239670176853623751 endpoint_12_49_p6 endpoint_12_49_w6
private theorem endpoint_12_49_w8 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 8 2 239670176853623751 = some 239670176853623751 := by decide +kernel
private theorem endpoint_12_49_p10 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 10 236008304633726827 = some 239670176853623751 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 8 2 236008304633726827 239670176853623751 239670176853623751 endpoint_12_49_p8 endpoint_12_49_w8
private theorem endpoint_12_49_w10 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 10 1 239670176853623751 = some 239670176853623751 := by decide +kernel
private theorem endpoint_12_49_p11 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 11 236008304633726827 = some 239670176853623751 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 10 1 236008304633726827 239670176853623751 239670176853623751 endpoint_12_49_p10 endpoint_12_49_w10
def endpoint_12_49 : CertifiedEndpoint :=
  ⟨⟨12, 49, 3350⟩, 239670176853623751, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_49_flag endpoint_12_49_sources 11 236008304633726827 239670176853623751 rfl endpoint_12_49_base endpoint_12_49_p11) (by decide)⟩
private def endpoint_12_50_flag : Flag := ⟨12, 50, 3318⟩
private def endpoint_12_50_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_50_base : receiptBase endpoint_12_50_flag endpoint_12_50_sources = some 237909742551055732 := by decide +kernel
private theorem endpoint_12_50_w0 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 2 237909742551055732 = some 244102779748646524 := by decide +kernel
private theorem endpoint_12_50_w2 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 2 2 244102779748646524 = some 244102779748646524 := by decide +kernel
private theorem endpoint_12_50_p4 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 4 237909742551055732 = some 244102779748646524 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 2 2 237909742551055732 244102779748646524 244102779748646524 endpoint_12_50_w0 endpoint_12_50_w2
private theorem endpoint_12_50_w4 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 4 2 244102779748646524 = some 244102779748646524 := by decide +kernel
private theorem endpoint_12_50_p6 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 6 237909742551055732 = some 244102779748646524 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 4 2 237909742551055732 244102779748646524 244102779748646524 endpoint_12_50_p4 endpoint_12_50_w4
private theorem endpoint_12_50_w6 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 6 2 244102779748646524 = some 244102779748646524 := by decide +kernel
private theorem endpoint_12_50_p8 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 8 237909742551055732 = some 244102779748646524 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 6 2 237909742551055732 244102779748646524 244102779748646524 endpoint_12_50_p6 endpoint_12_50_w6
private theorem endpoint_12_50_w8 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 8 2 244102779748646524 = some 244102779748646524 := by decide +kernel
private theorem endpoint_12_50_p10 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 10 237909742551055732 = some 244102779748646524 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 8 2 237909742551055732 244102779748646524 244102779748646524 endpoint_12_50_p8 endpoint_12_50_w8
private theorem endpoint_12_50_w10 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 10 1 244102779748646524 = some 244102779748646524 := by decide +kernel
private theorem endpoint_12_50_p11 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 11 237909742551055732 = some 244102779748646524 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 10 1 237909742551055732 244102779748646524 244102779748646524 endpoint_12_50_p10 endpoint_12_50_w10
def endpoint_12_50 : CertifiedEndpoint :=
  ⟨⟨12, 50, 3318⟩, 244102779748646524, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_50_flag endpoint_12_50_sources 11 237909742551055732 244102779748646524 rfl endpoint_12_50_base endpoint_12_50_p11) (by decide)⟩
private def endpoint_12_51_flag : Flag := ⟨12, 51, 3285⟩
private def endpoint_12_51_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_51_base : receiptBase endpoint_12_51_flag endpoint_12_51_sources = some 239660047797746881 := by decide +kernel
private theorem endpoint_12_51_w0 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 2 239660047797746881 = some 248437308854910534 := by decide +kernel
private theorem endpoint_12_51_w2 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 2 2 248437308854910534 = some 248437308854910534 := by decide +kernel
private theorem endpoint_12_51_p4 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 4 239660047797746881 = some 248437308854910534 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 2 2 239660047797746881 248437308854910534 248437308854910534 endpoint_12_51_w0 endpoint_12_51_w2
private theorem endpoint_12_51_w4 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 4 2 248437308854910534 = some 248437308854910534 := by decide +kernel
private theorem endpoint_12_51_p6 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 6 239660047797746881 = some 248437308854910534 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 4 2 239660047797746881 248437308854910534 248437308854910534 endpoint_12_51_p4 endpoint_12_51_w4
private theorem endpoint_12_51_w6 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 6 2 248437308854910534 = some 248437308854910534 := by decide +kernel
private theorem endpoint_12_51_p8 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 8 239660047797746881 = some 248437308854910534 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 6 2 239660047797746881 248437308854910534 248437308854910534 endpoint_12_51_p6 endpoint_12_51_w6
private theorem endpoint_12_51_w8 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 8 2 248437308854910534 = some 248437308854910534 := by decide +kernel
private theorem endpoint_12_51_p10 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 10 239660047797746881 = some 248437308854910534 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 8 2 239660047797746881 248437308854910534 248437308854910534 endpoint_12_51_p8 endpoint_12_51_w8
private theorem endpoint_12_51_w10 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 10 1 248437308854910534 = some 248437308854910534 := by decide +kernel
private theorem endpoint_12_51_p11 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 11 239660047797746881 = some 248437308854910534 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 10 1 239660047797746881 248437308854910534 248437308854910534 endpoint_12_51_p10 endpoint_12_51_w10
def endpoint_12_51 : CertifiedEndpoint :=
  ⟨⟨12, 51, 3285⟩, 248437308854910534, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_51_flag endpoint_12_51_sources 11 239660047797746881 248437308854910534 rfl endpoint_12_51_base endpoint_12_51_p11) (by decide)⟩
private def endpoint_12_52_flag : Flag := ⟨12, 52, 3251⟩
private def endpoint_12_52_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_12_52_base : receiptBase endpoint_12_52_flag endpoint_12_52_sources = some 242153592515196219 := by decide +kernel
private theorem endpoint_12_52_w0 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 2 242153592515196219 = some 248610099105142900 := by decide +kernel
private theorem endpoint_12_52_w2 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 2 2 248610099105142900 = some 248610099105142900 := by decide +kernel
private theorem endpoint_12_52_p4 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 4 242153592515196219 = some 248610099105142900 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 2 2 242153592515196219 248610099105142900 248610099105142900 endpoint_12_52_w0 endpoint_12_52_w2
private theorem endpoint_12_52_w4 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 4 2 248610099105142900 = some 248610099105142900 := by decide +kernel
private theorem endpoint_12_52_p6 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 6 242153592515196219 = some 248610099105142900 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 4 2 242153592515196219 248610099105142900 248610099105142900 endpoint_12_52_p4 endpoint_12_52_w4
private theorem endpoint_12_52_w6 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 6 2 248610099105142900 = some 248610099105142900 := by decide +kernel
private theorem endpoint_12_52_p8 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 8 242153592515196219 = some 248610099105142900 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 6 2 242153592515196219 248610099105142900 248610099105142900 endpoint_12_52_p6 endpoint_12_52_w6
private theorem endpoint_12_52_w8 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 8 2 248610099105142900 = some 248610099105142900 := by decide +kernel
private theorem endpoint_12_52_p10 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 10 242153592515196219 = some 248610099105142900 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 8 2 242153592515196219 248610099105142900 248610099105142900 endpoint_12_52_p8 endpoint_12_52_w8
private theorem endpoint_12_52_w10 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 10 1 248610099105142900 = some 248610099105142900 := by decide +kernel
private theorem endpoint_12_52_p11 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 11 242153592515196219 = some 248610099105142900 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 10 1 242153592515196219 248610099105142900 248610099105142900 endpoint_12_52_p10 endpoint_12_52_w10
def endpoint_12_52 : CertifiedEndpoint :=
  ⟨⟨12, 52, 3251⟩, 248610099105142900, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_12_52_flag endpoint_12_52_sources 11 242153592515196219 248610099105142900 rfl endpoint_12_52_base endpoint_12_52_p11) (by decide)⟩
private def endpoint_12_53_flag : Flag := ⟨12, 53, 3217⟩
private def endpoint_12_53_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_53_base : receiptBase endpoint_12_53_flag endpoint_12_53_sources = some 245452655593216844 := by decide +kernel
private theorem endpoint_12_53_w0 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 2 245452655593216844 = some 245660644658112592 := by decide +kernel
private theorem endpoint_12_53_w2 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 2 2 245660644658112592 = some 245660644658112592 := by decide +kernel
private theorem endpoint_12_53_p4 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 4 245452655593216844 = some 245660644658112592 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 2 2 245452655593216844 245660644658112592 245660644658112592 endpoint_12_53_w0 endpoint_12_53_w2
private theorem endpoint_12_53_w4 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 4 2 245660644658112592 = some 245660644658112592 := by decide +kernel
private theorem endpoint_12_53_p6 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 6 245452655593216844 = some 245660644658112592 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 4 2 245452655593216844 245660644658112592 245660644658112592 endpoint_12_53_p4 endpoint_12_53_w4
private theorem endpoint_12_53_w6 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 6 2 245660644658112592 = some 245660644658112592 := by decide +kernel
private theorem endpoint_12_53_p8 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 8 245452655593216844 = some 245660644658112592 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 6 2 245452655593216844 245660644658112592 245660644658112592 endpoint_12_53_p6 endpoint_12_53_w6
private theorem endpoint_12_53_w8 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 8 2 245660644658112592 = some 245660644658112592 := by decide +kernel
private theorem endpoint_12_53_p10 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 10 245452655593216844 = some 245660644658112592 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 8 2 245452655593216844 245660644658112592 245660644658112592 endpoint_12_53_p8 endpoint_12_53_w8
private theorem endpoint_12_53_w10 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 10 1 245660644658112592 = some 245660644658112592 := by decide +kernel
private theorem endpoint_12_53_p11 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 11 245452655593216844 = some 245660644658112592 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 10 1 245452655593216844 245660644658112592 245660644658112592 endpoint_12_53_p10 endpoint_12_53_w10
def endpoint_12_53 : CertifiedEndpoint :=
  ⟨⟨12, 53, 3217⟩, 245660644658112592, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_53_flag endpoint_12_53_sources 11 245452655593216844 245660644658112592 rfl endpoint_12_53_base endpoint_12_53_p11) (by decide)⟩
private def endpoint_12_54_flag : Flag := ⟨12, 54, 3181⟩
private def endpoint_12_54_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_54_base : receiptBase endpoint_12_54_flag endpoint_12_54_sources = some 246688231166302357 := by decide +kernel
private theorem endpoint_12_54_w0 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 2 246688231166302357 = some 249444390427190454 := by decide +kernel
private theorem endpoint_12_54_w2 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 2 2 249444390427190454 = some 249444390427190454 := by decide +kernel
private theorem endpoint_12_54_p4 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 4 246688231166302357 = some 249444390427190454 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 2 2 246688231166302357 249444390427190454 249444390427190454 endpoint_12_54_w0 endpoint_12_54_w2
private theorem endpoint_12_54_w4 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 4 2 249444390427190454 = some 249444390427190454 := by decide +kernel
private theorem endpoint_12_54_p6 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 6 246688231166302357 = some 249444390427190454 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 4 2 246688231166302357 249444390427190454 249444390427190454 endpoint_12_54_p4 endpoint_12_54_w4
private theorem endpoint_12_54_w6 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 6 2 249444390427190454 = some 249444390427190454 := by decide +kernel
private theorem endpoint_12_54_p8 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 8 246688231166302357 = some 249444390427190454 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 6 2 246688231166302357 249444390427190454 249444390427190454 endpoint_12_54_p6 endpoint_12_54_w6
private theorem endpoint_12_54_w8 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 8 2 249444390427190454 = some 249444390427190454 := by decide +kernel
private theorem endpoint_12_54_p10 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 10 246688231166302357 = some 249444390427190454 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 8 2 246688231166302357 249444390427190454 249444390427190454 endpoint_12_54_p8 endpoint_12_54_w8
private theorem endpoint_12_54_w10 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 10 1 249444390427190454 = some 249444390427190454 := by decide +kernel
private theorem endpoint_12_54_p11 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 11 246688231166302357 = some 249444390427190454 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 10 1 246688231166302357 249444390427190454 249444390427190454 endpoint_12_54_p10 endpoint_12_54_w10
def endpoint_12_54 : CertifiedEndpoint :=
  ⟨⟨12, 54, 3181⟩, 249444390427190454, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_54_flag endpoint_12_54_sources 11 246688231166302357 249444390427190454 rfl endpoint_12_54_base endpoint_12_54_p11) (by decide)⟩
private def endpoint_12_55_flag : Flag := ⟨12, 55, 3144⟩
private def endpoint_12_55_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_55_base : receiptBase endpoint_12_55_flag endpoint_12_55_sources = some 247756611904423683 := by decide +kernel
private theorem endpoint_12_55_w0 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 2 247756611904423683 = some 253119444978606045 := by decide +kernel
private theorem endpoint_12_55_w2 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 2 2 253119444978606045 = some 253119444978606045 := by decide +kernel
private theorem endpoint_12_55_p4 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 4 247756611904423683 = some 253119444978606045 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 2 2 247756611904423683 253119444978606045 253119444978606045 endpoint_12_55_w0 endpoint_12_55_w2
private theorem endpoint_12_55_w4 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 4 2 253119444978606045 = some 253119444978606045 := by decide +kernel
private theorem endpoint_12_55_p6 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 6 247756611904423683 = some 253119444978606045 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 4 2 247756611904423683 253119444978606045 253119444978606045 endpoint_12_55_p4 endpoint_12_55_w4
private theorem endpoint_12_55_w6 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 6 2 253119444978606045 = some 253119444978606045 := by decide +kernel
private theorem endpoint_12_55_p8 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 8 247756611904423683 = some 253119444978606045 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 6 2 247756611904423683 253119444978606045 253119444978606045 endpoint_12_55_p6 endpoint_12_55_w6
private theorem endpoint_12_55_w8 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 8 2 253119444978606045 = some 253119444978606045 := by decide +kernel
private theorem endpoint_12_55_p10 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 10 247756611904423683 = some 253119444978606045 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 8 2 247756611904423683 253119444978606045 253119444978606045 endpoint_12_55_p8 endpoint_12_55_w8
private theorem endpoint_12_55_w10 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 10 1 253119444978606045 = some 253119444978606045 := by decide +kernel
private theorem endpoint_12_55_p11 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 11 247756611904423683 = some 253119444978606045 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 10 1 247756611904423683 253119444978606045 253119444978606045 endpoint_12_55_p10 endpoint_12_55_w10
def endpoint_12_55 : CertifiedEndpoint :=
  ⟨⟨12, 55, 3144⟩, 253119444978606045, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_55_flag endpoint_12_55_sources 11 247756611904423683 253119444978606045 rfl endpoint_12_55_base endpoint_12_55_p11) (by decide)⟩
private def endpoint_12_56_flag : Flag := ⟨12, 56, 3107⟩
private def endpoint_12_56_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_56_base : receiptBase endpoint_12_56_flag endpoint_12_56_sources = some 248733068102956565 := by decide +kernel
private theorem endpoint_12_56_w0 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 2 248733068102956565 = some 256726310897758828 := by decide +kernel
private theorem endpoint_12_56_w2 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 2 2 256726310897758828 = some 256726310897758828 := by decide +kernel
private theorem endpoint_12_56_p4 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 4 248733068102956565 = some 256726310897758828 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 2 2 248733068102956565 256726310897758828 256726310897758828 endpoint_12_56_w0 endpoint_12_56_w2
private theorem endpoint_12_56_w4 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 4 2 256726310897758828 = some 256726310897758828 := by decide +kernel
private theorem endpoint_12_56_p6 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 6 248733068102956565 = some 256726310897758828 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 4 2 248733068102956565 256726310897758828 256726310897758828 endpoint_12_56_p4 endpoint_12_56_w4
private theorem endpoint_12_56_w6 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 6 2 256726310897758828 = some 256726310897758828 := by decide +kernel
private theorem endpoint_12_56_p8 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 8 248733068102956565 = some 256726310897758828 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 6 2 248733068102956565 256726310897758828 256726310897758828 endpoint_12_56_p6 endpoint_12_56_w6
private theorem endpoint_12_56_w8 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 8 2 256726310897758828 = some 256726310897758828 := by decide +kernel
private theorem endpoint_12_56_p10 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 10 248733068102956565 = some 256726310897758828 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 8 2 248733068102956565 256726310897758828 256726310897758828 endpoint_12_56_p8 endpoint_12_56_w8
private theorem endpoint_12_56_w10 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 10 1 256726310897758828 = some 256726310897758828 := by decide +kernel
private theorem endpoint_12_56_p11 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 11 248733068102956565 = some 256726310897758828 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 10 1 248733068102956565 256726310897758828 256726310897758828 endpoint_12_56_p10 endpoint_12_56_w10
def endpoint_12_56 : CertifiedEndpoint :=
  ⟨⟨12, 56, 3107⟩, 256726310897758828, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_56_flag endpoint_12_56_sources 11 248733068102956565 256726310897758828 rfl endpoint_12_56_base endpoint_12_56_p11) (by decide)⟩
private def endpoint_12_57_flag : Flag := ⟨12, 57, 3068⟩
private def endpoint_12_57_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_12_57_base : receiptBase endpoint_12_57_flag endpoint_12_57_sources = some 250477433996142459 := by decide +kernel
private theorem endpoint_12_57_w0 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 2 250477433996142459 = some 252538723681120692 := by decide +kernel
private theorem endpoint_12_57_w2 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 2 2 252538723681120692 = some 252538723681120692 := by decide +kernel
private theorem endpoint_12_57_p4 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 4 250477433996142459 = some 252538723681120692 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 2 2 250477433996142459 252538723681120692 252538723681120692 endpoint_12_57_w0 endpoint_12_57_w2
private theorem endpoint_12_57_w4 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 4 2 252538723681120692 = some 252538723681120692 := by decide +kernel
private theorem endpoint_12_57_p6 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 6 250477433996142459 = some 252538723681120692 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 4 2 250477433996142459 252538723681120692 252538723681120692 endpoint_12_57_p4 endpoint_12_57_w4
private theorem endpoint_12_57_w6 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 6 2 252538723681120692 = some 252538723681120692 := by decide +kernel
private theorem endpoint_12_57_p8 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 8 250477433996142459 = some 252538723681120692 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 6 2 250477433996142459 252538723681120692 252538723681120692 endpoint_12_57_p6 endpoint_12_57_w6
private theorem endpoint_12_57_w8 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 8 2 252538723681120692 = some 252538723681120692 := by decide +kernel
private theorem endpoint_12_57_p10 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 10 250477433996142459 = some 252538723681120692 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 8 2 250477433996142459 252538723681120692 252538723681120692 endpoint_12_57_p8 endpoint_12_57_w8
private theorem endpoint_12_57_w10 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 10 1 252538723681120692 = some 252538723681120692 := by decide +kernel
private theorem endpoint_12_57_p11 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 11 250477433996142459 = some 252538723681120692 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 10 1 250477433996142459 252538723681120692 252538723681120692 endpoint_12_57_p10 endpoint_12_57_w10
def endpoint_12_57 : CertifiedEndpoint :=
  ⟨⟨12, 57, 3068⟩, 252538723681120692, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_12_57_flag endpoint_12_57_sources 11 250477433996142459 252538723681120692 rfl endpoint_12_57_base endpoint_12_57_p11) (by decide)⟩
private def endpoint_12_58_flag : Flag := ⟨12, 58, 3028⟩
private def endpoint_12_58_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_12_58_base : receiptBase endpoint_12_58_flag endpoint_12_58_sources = some 251029577191651927 := by decide +kernel
private theorem endpoint_12_58_w0 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 2 251029577191651927 = some 255720797987817878 := by decide +kernel
private theorem endpoint_12_58_w2 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 2 2 255720797987817878 = some 255720797987817878 := by decide +kernel
private theorem endpoint_12_58_p4 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 4 251029577191651927 = some 255720797987817878 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 2 2 251029577191651927 255720797987817878 255720797987817878 endpoint_12_58_w0 endpoint_12_58_w2
private theorem endpoint_12_58_w4 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 4 2 255720797987817878 = some 255720797987817878 := by decide +kernel
private theorem endpoint_12_58_p6 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 6 251029577191651927 = some 255720797987817878 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 4 2 251029577191651927 255720797987817878 255720797987817878 endpoint_12_58_p4 endpoint_12_58_w4
private theorem endpoint_12_58_w6 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 6 2 255720797987817878 = some 255720797987817878 := by decide +kernel
private theorem endpoint_12_58_p8 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 8 251029577191651927 = some 255720797987817878 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 6 2 251029577191651927 255720797987817878 255720797987817878 endpoint_12_58_p6 endpoint_12_58_w6
private theorem endpoint_12_58_w8 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 8 2 255720797987817878 = some 255720797987817878 := by decide +kernel
private theorem endpoint_12_58_p10 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 10 251029577191651927 = some 255720797987817878 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 8 2 251029577191651927 255720797987817878 255720797987817878 endpoint_12_58_p8 endpoint_12_58_w8
private theorem endpoint_12_58_w10 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 10 1 255720797987817878 = some 255720797987817878 := by decide +kernel
private theorem endpoint_12_58_p11 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 11 251029577191651927 = some 255720797987817878 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 10 1 251029577191651927 255720797987817878 255720797987817878 endpoint_12_58_p10 endpoint_12_58_w10
def endpoint_12_58 : CertifiedEndpoint :=
  ⟨⟨12, 58, 3028⟩, 255720797987817878, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_12_58_flag endpoint_12_58_sources 11 251029577191651927 255720797987817878 rfl endpoint_12_58_base endpoint_12_58_p11) (by decide)⟩
private def endpoint_12_59_flag : Flag := ⟨12, 59, 2986⟩
private def endpoint_12_59_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_12_59_base : receiptBase endpoint_12_59_flag endpoint_12_59_sources = some 251315624784452297 := by decide +kernel
private theorem endpoint_12_59_w0 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 2 251315624784452297 = some 258737752348098068 := by decide +kernel
private theorem endpoint_12_59_w2 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 2 2 258737752348098068 = some 258737752348098068 := by decide +kernel
private theorem endpoint_12_59_p4 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 4 251315624784452297 = some 258737752348098068 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 2 2 251315624784452297 258737752348098068 258737752348098068 endpoint_12_59_w0 endpoint_12_59_w2
private theorem endpoint_12_59_w4 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 4 2 258737752348098068 = some 258737752348098068 := by decide +kernel
private theorem endpoint_12_59_p6 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 6 251315624784452297 = some 258737752348098068 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 4 2 251315624784452297 258737752348098068 258737752348098068 endpoint_12_59_p4 endpoint_12_59_w4
private theorem endpoint_12_59_w6 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 6 2 258737752348098068 = some 258737752348098068 := by decide +kernel
private theorem endpoint_12_59_p8 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 8 251315624784452297 = some 258737752348098068 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 6 2 251315624784452297 258737752348098068 258737752348098068 endpoint_12_59_p6 endpoint_12_59_w6
private theorem endpoint_12_59_w8 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 8 2 258737752348098068 = some 258737752348098068 := by decide +kernel
private theorem endpoint_12_59_p10 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 10 251315624784452297 = some 258737752348098068 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 8 2 251315624784452297 258737752348098068 258737752348098068 endpoint_12_59_p8 endpoint_12_59_w8
private theorem endpoint_12_59_w10 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 10 1 258737752348098068 = some 258737752348098068 := by decide +kernel
private theorem endpoint_12_59_p11 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 11 251315624784452297 = some 258737752348098068 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 10 1 251315624784452297 258737752348098068 258737752348098068 endpoint_12_59_p10 endpoint_12_59_w10
def endpoint_12_59 : CertifiedEndpoint :=
  ⟨⟨12, 59, 2986⟩, 258737752348098068, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_12_59_flag endpoint_12_59_sources 11 251315624784452297 258737752348098068 rfl endpoint_12_59_base endpoint_12_59_p11) (by decide)⟩
private def endpoint_12_60_flag : Flag := ⟨12, 60, 2943⟩
private def endpoint_12_60_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_12_60_base : receiptBase endpoint_12_60_flag endpoint_12_60_sources = some 252508128812296744 := by decide +kernel
private theorem endpoint_12_60_w0 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 2 252508128812296744 = some 255877566564430944 := by decide +kernel
private theorem endpoint_12_60_w2 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 2 2 255877566564430944 = some 255877566564430944 := by decide +kernel
private theorem endpoint_12_60_p4 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 4 252508128812296744 = some 255877566564430944 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 2 2 252508128812296744 255877566564430944 255877566564430944 endpoint_12_60_w0 endpoint_12_60_w2
private theorem endpoint_12_60_w4 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 4 2 255877566564430944 = some 255877566564430944 := by decide +kernel
private theorem endpoint_12_60_p6 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 6 252508128812296744 = some 255877566564430944 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 4 2 252508128812296744 255877566564430944 255877566564430944 endpoint_12_60_p4 endpoint_12_60_w4
private theorem endpoint_12_60_w6 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 6 2 255877566564430944 = some 255877566564430944 := by decide +kernel
private theorem endpoint_12_60_p8 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 8 252508128812296744 = some 255877566564430944 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 6 2 252508128812296744 255877566564430944 255877566564430944 endpoint_12_60_p6 endpoint_12_60_w6
private theorem endpoint_12_60_w8 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 8 2 255877566564430944 = some 255877566564430944 := by decide +kernel
private theorem endpoint_12_60_p10 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 10 252508128812296744 = some 255877566564430944 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 8 2 252508128812296744 255877566564430944 255877566564430944 endpoint_12_60_p8 endpoint_12_60_w8
private theorem endpoint_12_60_w10 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 10 1 255877566564430944 = some 255877566564430944 := by decide +kernel
private theorem endpoint_12_60_p11 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 11 252508128812296744 = some 255877566564430944 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 10 1 252508128812296744 255877566564430944 255877566564430944 endpoint_12_60_p10 endpoint_12_60_w10
def endpoint_12_60 : CertifiedEndpoint :=
  ⟨⟨12, 60, 2943⟩, 255877566564430944, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_12_60_flag endpoint_12_60_sources 11 252508128812296744 255877566564430944 rfl endpoint_12_60_base endpoint_12_60_p11) (by decide)⟩
private def endpoint_12_61_flag : Flag := ⟨12, 61, 2898⟩
private def endpoint_12_61_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_12_61_base : receiptBase endpoint_12_61_flag endpoint_12_61_sources = some 252329567800387523 := by decide +kernel
private theorem endpoint_12_61_w0 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 2 252329567800387523 = some 258488868150261877 := by decide +kernel
private theorem endpoint_12_61_w2 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 2 2 258488868150261877 = some 258488868150261877 := by decide +kernel
private theorem endpoint_12_61_p4 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 4 252329567800387523 = some 258488868150261877 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 2 2 252329567800387523 258488868150261877 258488868150261877 endpoint_12_61_w0 endpoint_12_61_w2
private theorem endpoint_12_61_w4 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 4 2 258488868150261877 = some 258488868150261877 := by decide +kernel
private theorem endpoint_12_61_p6 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 6 252329567800387523 = some 258488868150261877 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 4 2 252329567800387523 258488868150261877 258488868150261877 endpoint_12_61_p4 endpoint_12_61_w4
private theorem endpoint_12_61_w6 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 6 2 258488868150261877 = some 258488868150261877 := by decide +kernel
private theorem endpoint_12_61_p8 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 8 252329567800387523 = some 258488868150261877 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 6 2 252329567800387523 258488868150261877 258488868150261877 endpoint_12_61_p6 endpoint_12_61_w6
private theorem endpoint_12_61_w8 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 8 2 258488868150261877 = some 258488868150261877 := by decide +kernel
private theorem endpoint_12_61_p10 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 10 252329567800387523 = some 258488868150261877 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 8 2 252329567800387523 258488868150261877 258488868150261877 endpoint_12_61_p8 endpoint_12_61_w8
private theorem endpoint_12_61_w10 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 10 1 258488868150261877 = some 258488868150261877 := by decide +kernel
private theorem endpoint_12_61_p11 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 11 252329567800387523 = some 258488868150261877 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 10 1 252329567800387523 258488868150261877 258488868150261877 endpoint_12_61_p10 endpoint_12_61_w10
def endpoint_12_61 : CertifiedEndpoint :=
  ⟨⟨12, 61, 2898⟩, 258488868150261877, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_12_61_flag endpoint_12_61_sources 11 252329567800387523 258488868150261877 rfl endpoint_12_61_base endpoint_12_61_p11) (by decide)⟩
private def endpoint_12_62_flag : Flag := ⟨12, 62, 2851⟩
private def endpoint_12_62_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_12_62_base : receiptBase endpoint_12_62_flag endpoint_12_62_sources = some 253014097638258524 := by decide +kernel
private theorem endpoint_12_62_w0 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 2 253014097638258524 = some 256873901787739430 := by decide +kernel
private theorem endpoint_12_62_w2 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 2 2 256873901787739430 = some 256873901787739430 := by decide +kernel
private theorem endpoint_12_62_p4 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 4 253014097638258524 = some 256873901787739430 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 2 2 253014097638258524 256873901787739430 256873901787739430 endpoint_12_62_w0 endpoint_12_62_w2
private theorem endpoint_12_62_w4 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 4 2 256873901787739430 = some 256873901787739430 := by decide +kernel
private theorem endpoint_12_62_p6 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 6 253014097638258524 = some 256873901787739430 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 4 2 253014097638258524 256873901787739430 256873901787739430 endpoint_12_62_p4 endpoint_12_62_w4
private theorem endpoint_12_62_w6 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 6 2 256873901787739430 = some 256873901787739430 := by decide +kernel
private theorem endpoint_12_62_p8 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 8 253014097638258524 = some 256873901787739430 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 6 2 253014097638258524 256873901787739430 256873901787739430 endpoint_12_62_p6 endpoint_12_62_w6
private theorem endpoint_12_62_w8 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 8 2 256873901787739430 = some 256873901787739430 := by decide +kernel
private theorem endpoint_12_62_p10 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 10 253014097638258524 = some 256873901787739430 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 8 2 253014097638258524 256873901787739430 256873901787739430 endpoint_12_62_p8 endpoint_12_62_w8
private theorem endpoint_12_62_w10 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 10 1 256873901787739430 = some 256873901787739430 := by decide +kernel
private theorem endpoint_12_62_p11 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 11 253014097638258524 = some 256873901787739430 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 10 1 253014097638258524 256873901787739430 256873901787739430 endpoint_12_62_p10 endpoint_12_62_w10
def endpoint_12_62 : CertifiedEndpoint :=
  ⟨⟨12, 62, 2851⟩, 256873901787739430, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_12_62_flag endpoint_12_62_sources 11 253014097638258524 256873901787739430 rfl endpoint_12_62_base endpoint_12_62_p11) (by decide)⟩
private def endpoint_12_63_flag : Flag := ⟨12, 63, 2803⟩
private def endpoint_12_63_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_12_63_base : receiptBase endpoint_12_63_flag endpoint_12_63_sources = some 253534895998978403 := by decide +kernel
private theorem endpoint_12_63_w0 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 2 253534895998978403 = some 256522391816537937 := by decide +kernel
private theorem endpoint_12_63_w2 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 2 2 256522391816537937 = some 256522391816537937 := by decide +kernel
private theorem endpoint_12_63_p4 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 4 253534895998978403 = some 256522391816537937 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 2 2 253534895998978403 256522391816537937 256522391816537937 endpoint_12_63_w0 endpoint_12_63_w2
private theorem endpoint_12_63_w4 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 4 2 256522391816537937 = some 256522391816537937 := by decide +kernel
private theorem endpoint_12_63_p6 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 6 253534895998978403 = some 256522391816537937 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 4 2 253534895998978403 256522391816537937 256522391816537937 endpoint_12_63_p4 endpoint_12_63_w4
private theorem endpoint_12_63_w6 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 6 2 256522391816537937 = some 256522391816537937 := by decide +kernel
private theorem endpoint_12_63_p8 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 8 253534895998978403 = some 256522391816537937 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 6 2 253534895998978403 256522391816537937 256522391816537937 endpoint_12_63_p6 endpoint_12_63_w6
private theorem endpoint_12_63_w8 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 8 2 256522391816537937 = some 256522391816537937 := by decide +kernel
private theorem endpoint_12_63_p10 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 10 253534895998978403 = some 256522391816537937 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 8 2 253534895998978403 256522391816537937 256522391816537937 endpoint_12_63_p8 endpoint_12_63_w8
private theorem endpoint_12_63_w10 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 10 1 256522391816537937 = some 256522391816537937 := by decide +kernel
private theorem endpoint_12_63_p11 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 11 253534895998978403 = some 256522391816537937 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 10 1 253534895998978403 256522391816537937 256522391816537937 endpoint_12_63_p10 endpoint_12_63_w10
def endpoint_12_63 : CertifiedEndpoint :=
  ⟨⟨12, 63, 2803⟩, 256522391816537937, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_12_63_flag endpoint_12_63_sources 11 253534895998978403 256522391816537937 rfl endpoint_12_63_base endpoint_12_63_p11) (by decide)⟩
private def endpoint_12_64_flag : Flag := ⟨12, 64, 2752⟩
private def endpoint_12_64_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_64_base : receiptBase endpoint_12_64_flag endpoint_12_64_sources = some 253543388810074633 := by decide +kernel
private theorem endpoint_12_64_w0 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 2 253543388810074633 = some 253543388810074633 := by decide +kernel
private theorem endpoint_12_64_w2 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 2 2 253543388810074633 = some 253543388810074633 := by decide +kernel
private theorem endpoint_12_64_p4 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 4 253543388810074633 = some 253543388810074633 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 2 2 253543388810074633 253543388810074633 253543388810074633 endpoint_12_64_w0 endpoint_12_64_w2
private theorem endpoint_12_64_w4 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 4 2 253543388810074633 = some 253543388810074633 := by decide +kernel
private theorem endpoint_12_64_p6 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 6 253543388810074633 = some 253543388810074633 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 4 2 253543388810074633 253543388810074633 253543388810074633 endpoint_12_64_p4 endpoint_12_64_w4
private theorem endpoint_12_64_w6 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 6 2 253543388810074633 = some 253543388810074633 := by decide +kernel
private theorem endpoint_12_64_p8 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 8 253543388810074633 = some 253543388810074633 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 6 2 253543388810074633 253543388810074633 253543388810074633 endpoint_12_64_p6 endpoint_12_64_w6
private theorem endpoint_12_64_w8 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 8 2 253543388810074633 = some 253543388810074633 := by decide +kernel
private theorem endpoint_12_64_p10 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 10 253543388810074633 = some 253543388810074633 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 8 2 253543388810074633 253543388810074633 253543388810074633 endpoint_12_64_p8 endpoint_12_64_w8
private theorem endpoint_12_64_w10 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 10 1 253543388810074633 = some 253543388810074633 := by decide +kernel
private theorem endpoint_12_64_p11 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 11 253543388810074633 = some 253543388810074633 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 10 1 253543388810074633 253543388810074633 253543388810074633 endpoint_12_64_p10 endpoint_12_64_w10
def endpoint_12_64 : CertifiedEndpoint :=
  ⟨⟨12, 64, 2752⟩, 253543388810074633, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_64_flag endpoint_12_64_sources 11 253543388810074633 253543388810074633 rfl endpoint_12_64_base endpoint_12_64_p11) (by decide)⟩
private def endpoint_12_65_flag : Flag := ⟨12, 65, 2698⟩
private def endpoint_12_65_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_65_base : receiptBase endpoint_12_65_flag endpoint_12_65_sources = some 252068758785686768 := by decide +kernel
private theorem endpoint_12_65_w0 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 2 252068758785686768 = some 252795260825881819 := by decide +kernel
private theorem endpoint_12_65_w2 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 2 2 252795260825881819 = some 252795260825881819 := by decide +kernel
private theorem endpoint_12_65_p4 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 4 252068758785686768 = some 252795260825881819 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 2 2 252068758785686768 252795260825881819 252795260825881819 endpoint_12_65_w0 endpoint_12_65_w2
private theorem endpoint_12_65_w4 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 4 2 252795260825881819 = some 252795260825881819 := by decide +kernel
private theorem endpoint_12_65_p6 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 6 252068758785686768 = some 252795260825881819 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 4 2 252068758785686768 252795260825881819 252795260825881819 endpoint_12_65_p4 endpoint_12_65_w4
private theorem endpoint_12_65_w6 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 6 2 252795260825881819 = some 252795260825881819 := by decide +kernel
private theorem endpoint_12_65_p8 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 8 252068758785686768 = some 252795260825881819 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 6 2 252068758785686768 252795260825881819 252795260825881819 endpoint_12_65_p6 endpoint_12_65_w6
private theorem endpoint_12_65_w8 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 8 2 252795260825881819 = some 252795260825881819 := by decide +kernel
private theorem endpoint_12_65_p10 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 10 252068758785686768 = some 252795260825881819 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 8 2 252068758785686768 252795260825881819 252795260825881819 endpoint_12_65_p8 endpoint_12_65_w8
private theorem endpoint_12_65_w10 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 10 1 252795260825881819 = some 252795260825881819 := by decide +kernel
private theorem endpoint_12_65_p11 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 11 252068758785686768 = some 252795260825881819 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 10 1 252068758785686768 252795260825881819 252795260825881819 endpoint_12_65_p10 endpoint_12_65_w10
def endpoint_12_65 : CertifiedEndpoint :=
  ⟨⟨12, 65, 2698⟩, 252795260825881819, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_65_flag endpoint_12_65_sources 11 252068758785686768 252795260825881819 rfl endpoint_12_65_base endpoint_12_65_p11) (by decide)⟩
private def endpoint_12_66_flag : Flag := ⟨12, 66, 2643⟩
private def endpoint_12_66_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_66_base : receiptBase endpoint_12_66_flag endpoint_12_66_sources = some 250362009161808622 := by decide +kernel
private theorem endpoint_12_66_w0 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 2 250362009161808622 = some 254211912659225190 := by decide +kernel
private theorem endpoint_12_66_w2 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 2 2 254211912659225190 = some 254211912659225190 := by decide +kernel
private theorem endpoint_12_66_p4 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 4 250362009161808622 = some 254211912659225190 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 2 2 250362009161808622 254211912659225190 254211912659225190 endpoint_12_66_w0 endpoint_12_66_w2
private theorem endpoint_12_66_w4 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 4 2 254211912659225190 = some 254211912659225190 := by decide +kernel
private theorem endpoint_12_66_p6 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 6 250362009161808622 = some 254211912659225190 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 4 2 250362009161808622 254211912659225190 254211912659225190 endpoint_12_66_p4 endpoint_12_66_w4
private theorem endpoint_12_66_w6 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 6 2 254211912659225190 = some 254211912659225190 := by decide +kernel
private theorem endpoint_12_66_p8 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 8 250362009161808622 = some 254211912659225190 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 6 2 250362009161808622 254211912659225190 254211912659225190 endpoint_12_66_p6 endpoint_12_66_w6
private theorem endpoint_12_66_w8 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 8 2 254211912659225190 = some 254211912659225190 := by decide +kernel
private theorem endpoint_12_66_p10 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 10 250362009161808622 = some 254211912659225190 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 8 2 250362009161808622 254211912659225190 254211912659225190 endpoint_12_66_p8 endpoint_12_66_w8
private theorem endpoint_12_66_w10 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 10 1 254211912659225190 = some 254211912659225190 := by decide +kernel
private theorem endpoint_12_66_p11 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 11 250362009161808622 = some 254211912659225190 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 10 1 250362009161808622 254211912659225190 254211912659225190 endpoint_12_66_p10 endpoint_12_66_w10
def endpoint_12_66 : CertifiedEndpoint :=
  ⟨⟨12, 66, 2643⟩, 254211912659225190, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_66_flag endpoint_12_66_sources 11 250362009161808622 254211912659225190 rfl endpoint_12_66_base endpoint_12_66_p11) (by decide)⟩
private def endpoint_12_67_flag : Flag := ⟨12, 67, 2585⟩
private def endpoint_12_67_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_67_base : receiptBase endpoint_12_67_flag endpoint_12_67_sources = some 248229551561214400 := by decide +kernel
private theorem endpoint_12_67_w0 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 2 248229551561214400 = some 255369854816234562 := by decide +kernel
private theorem endpoint_12_67_w2 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 2 2 255369854816234562 = some 255369854816234562 := by decide +kernel
private theorem endpoint_12_67_p4 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 4 248229551561214400 = some 255369854816234562 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 2 2 248229551561214400 255369854816234562 255369854816234562 endpoint_12_67_w0 endpoint_12_67_w2
private theorem endpoint_12_67_w4 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 4 2 255369854816234562 = some 255369854816234562 := by decide +kernel
private theorem endpoint_12_67_p6 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 6 248229551561214400 = some 255369854816234562 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 4 2 248229551561214400 255369854816234562 255369854816234562 endpoint_12_67_p4 endpoint_12_67_w4
private theorem endpoint_12_67_w6 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 6 2 255369854816234562 = some 255369854816234562 := by decide +kernel
private theorem endpoint_12_67_p8 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 8 248229551561214400 = some 255369854816234562 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 6 2 248229551561214400 255369854816234562 255369854816234562 endpoint_12_67_p6 endpoint_12_67_w6
private theorem endpoint_12_67_w8 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 8 2 255369854816234562 = some 255369854816234562 := by decide +kernel
private theorem endpoint_12_67_p10 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 10 248229551561214400 = some 255369854816234562 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 8 2 248229551561214400 255369854816234562 255369854816234562 endpoint_12_67_p8 endpoint_12_67_w8
private theorem endpoint_12_67_w10 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 10 1 255369854816234562 = some 255369854816234562 := by decide +kernel
private theorem endpoint_12_67_p11 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 11 248229551561214400 = some 255369854816234562 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 10 1 248229551561214400 255369854816234562 255369854816234562 endpoint_12_67_p10 endpoint_12_67_w10
def endpoint_12_67 : CertifiedEndpoint :=
  ⟨⟨12, 67, 2585⟩, 255369854816234562, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_67_flag endpoint_12_67_sources 11 248229551561214400 255369854816234562 rfl endpoint_12_67_base endpoint_12_67_p11) (by decide)⟩
private def endpoint_12_68_flag : Flag := ⟨12, 68, 2525⟩
private def endpoint_12_68_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_12_68_base : receiptBase endpoint_12_68_flag endpoint_12_68_sources = some 251315387631250174 := by decide +kernel
private theorem endpoint_12_68_w0 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 2 251315387631250174 = some 251315387631250174 := by decide +kernel
private theorem endpoint_12_68_w2 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 2 2 251315387631250174 = some 251315387631250174 := by decide +kernel
private theorem endpoint_12_68_p4 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 4 251315387631250174 = some 251315387631250174 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 2 2 251315387631250174 251315387631250174 251315387631250174 endpoint_12_68_w0 endpoint_12_68_w2
private theorem endpoint_12_68_w4 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 4 2 251315387631250174 = some 251315387631250174 := by decide +kernel
private theorem endpoint_12_68_p6 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 6 251315387631250174 = some 251315387631250174 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 4 2 251315387631250174 251315387631250174 251315387631250174 endpoint_12_68_p4 endpoint_12_68_w4
private theorem endpoint_12_68_w6 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 6 2 251315387631250174 = some 251315387631250174 := by decide +kernel
private theorem endpoint_12_68_p8 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 8 251315387631250174 = some 251315387631250174 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 6 2 251315387631250174 251315387631250174 251315387631250174 endpoint_12_68_p6 endpoint_12_68_w6
private theorem endpoint_12_68_w8 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 8 2 251315387631250174 = some 251315387631250174 := by decide +kernel
private theorem endpoint_12_68_p10 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 10 251315387631250174 = some 251315387631250174 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 8 2 251315387631250174 251315387631250174 251315387631250174 endpoint_12_68_p8 endpoint_12_68_w8
private theorem endpoint_12_68_w10 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 10 1 251315387631250174 = some 251315387631250174 := by decide +kernel
private theorem endpoint_12_68_p11 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 11 251315387631250174 = some 251315387631250174 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 10 1 251315387631250174 251315387631250174 251315387631250174 endpoint_12_68_p10 endpoint_12_68_w10
def endpoint_12_68 : CertifiedEndpoint :=
  ⟨⟨12, 68, 2525⟩, 251315387631250174, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_12_68_flag endpoint_12_68_sources 11 251315387631250174 251315387631250174 rfl endpoint_12_68_base endpoint_12_68_p11) (by decide)⟩
private def endpoint_12_69_flag : Flag := ⟨12, 69, 2462⟩
private def endpoint_12_69_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_12_69_base : receiptBase endpoint_12_69_flag endpoint_12_69_sources = some 248367065548305848 := by decide +kernel
private theorem endpoint_12_69_w0 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 2 248367065548305848 = some 248367065548305848 := by decide +kernel
private theorem endpoint_12_69_w2 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 2 2 248367065548305848 = some 248367065548305848 := by decide +kernel
private theorem endpoint_12_69_p4 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 4 248367065548305848 = some 248367065548305848 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 2 2 248367065548305848 248367065548305848 248367065548305848 endpoint_12_69_w0 endpoint_12_69_w2
private theorem endpoint_12_69_w4 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 4 2 248367065548305848 = some 248367065548305848 := by decide +kernel
private theorem endpoint_12_69_p6 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 6 248367065548305848 = some 248367065548305848 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 4 2 248367065548305848 248367065548305848 248367065548305848 endpoint_12_69_p4 endpoint_12_69_w4
private theorem endpoint_12_69_w6 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 6 2 248367065548305848 = some 248367065548305848 := by decide +kernel
private theorem endpoint_12_69_p8 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 8 248367065548305848 = some 248367065548305848 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 6 2 248367065548305848 248367065548305848 248367065548305848 endpoint_12_69_p6 endpoint_12_69_w6
private theorem endpoint_12_69_w8 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 8 2 248367065548305848 = some 248367065548305848 := by decide +kernel
private theorem endpoint_12_69_p10 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 10 248367065548305848 = some 248367065548305848 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 8 2 248367065548305848 248367065548305848 248367065548305848 endpoint_12_69_p8 endpoint_12_69_w8
private theorem endpoint_12_69_w10 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 10 1 248367065548305848 = some 248367065548305848 := by decide +kernel
private theorem endpoint_12_69_p11 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 11 248367065548305848 = some 248367065548305848 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 10 1 248367065548305848 248367065548305848 248367065548305848 endpoint_12_69_p10 endpoint_12_69_w10
def endpoint_12_69 : CertifiedEndpoint :=
  ⟨⟨12, 69, 2462⟩, 248367065548305848, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_12_69_flag endpoint_12_69_sources 11 248367065548305848 248367065548305848 rfl endpoint_12_69_base endpoint_12_69_p11) (by decide)⟩
private def endpoint_12_70_flag : Flag := ⟨12, 70, 2397⟩
private def endpoint_12_70_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_12_70_base : receiptBase endpoint_12_70_flag endpoint_12_70_sources = some 245057235057070246 := by decide +kernel
private theorem endpoint_12_70_w0 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 2 245057235057070246 = some 245057235057070246 := by decide +kernel
private theorem endpoint_12_70_w2 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 2 2 245057235057070246 = some 245057235057070246 := by decide +kernel
private theorem endpoint_12_70_p4 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 4 245057235057070246 = some 245057235057070246 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 2 2 245057235057070246 245057235057070246 245057235057070246 endpoint_12_70_w0 endpoint_12_70_w2
private theorem endpoint_12_70_w4 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 4 2 245057235057070246 = some 245057235057070246 := by decide +kernel
private theorem endpoint_12_70_p6 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 6 245057235057070246 = some 245057235057070246 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 4 2 245057235057070246 245057235057070246 245057235057070246 endpoint_12_70_p4 endpoint_12_70_w4
private theorem endpoint_12_70_w6 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 6 2 245057235057070246 = some 245057235057070246 := by decide +kernel
private theorem endpoint_12_70_p8 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 8 245057235057070246 = some 245057235057070246 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 6 2 245057235057070246 245057235057070246 245057235057070246 endpoint_12_70_p6 endpoint_12_70_w6
private theorem endpoint_12_70_w8 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 8 2 245057235057070246 = some 245057235057070246 := by decide +kernel
private theorem endpoint_12_70_p10 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 10 245057235057070246 = some 245057235057070246 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 8 2 245057235057070246 245057235057070246 245057235057070246 endpoint_12_70_p8 endpoint_12_70_w8
private theorem endpoint_12_70_w10 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 10 1 245057235057070246 = some 245057235057070246 := by decide +kernel
private theorem endpoint_12_70_p11 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 11 245057235057070246 = some 245057235057070246 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 10 1 245057235057070246 245057235057070246 245057235057070246 endpoint_12_70_p10 endpoint_12_70_w10
def endpoint_12_70 : CertifiedEndpoint :=
  ⟨⟨12, 70, 2397⟩, 245057235057070246, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_12_70_flag endpoint_12_70_sources 11 245057235057070246 245057235057070246 rfl endpoint_12_70_base endpoint_12_70_p11) (by decide)⟩
private def endpoint_12_71_flag : Flag := ⟨12, 71, 2329⟩
private def endpoint_12_71_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_12_71_base : receiptBase endpoint_12_71_flag endpoint_12_71_sources = some 242822202747856003 := by decide +kernel
private theorem endpoint_12_71_w0 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 2 242822202747856003 = some 242822202747856003 := by decide +kernel
private theorem endpoint_12_71_w2 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 2 2 242822202747856003 = some 242822202747856003 := by decide +kernel
private theorem endpoint_12_71_p4 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 4 242822202747856003 = some 242822202747856003 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 2 2 242822202747856003 242822202747856003 242822202747856003 endpoint_12_71_w0 endpoint_12_71_w2
private theorem endpoint_12_71_w4 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 4 2 242822202747856003 = some 242822202747856003 := by decide +kernel
private theorem endpoint_12_71_p6 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 6 242822202747856003 = some 242822202747856003 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 4 2 242822202747856003 242822202747856003 242822202747856003 endpoint_12_71_p4 endpoint_12_71_w4
private theorem endpoint_12_71_w6 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 6 2 242822202747856003 = some 242822202747856003 := by decide +kernel
private theorem endpoint_12_71_p8 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 8 242822202747856003 = some 242822202747856003 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 6 2 242822202747856003 242822202747856003 242822202747856003 endpoint_12_71_p6 endpoint_12_71_w6
private theorem endpoint_12_71_w8 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 8 2 242822202747856003 = some 242822202747856003 := by decide +kernel
private theorem endpoint_12_71_p10 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 10 242822202747856003 = some 242822202747856003 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 8 2 242822202747856003 242822202747856003 242822202747856003 endpoint_12_71_p8 endpoint_12_71_w8
private theorem endpoint_12_71_w10 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 10 1 242822202747856003 = some 242822202747856003 := by decide +kernel
private theorem endpoint_12_71_p11 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 11 242822202747856003 = some 242822202747856003 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 10 1 242822202747856003 242822202747856003 242822202747856003 endpoint_12_71_p10 endpoint_12_71_w10
def endpoint_12_71 : CertifiedEndpoint :=
  ⟨⟨12, 71, 2329⟩, 242822202747856003, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_12_71_flag endpoint_12_71_sources 11 242822202747856003 242822202747856003 rfl endpoint_12_71_base endpoint_12_71_p11) (by decide)⟩
private def endpoint_12_72_flag : Flag := ⟨12, 72, 2259⟩
private def endpoint_12_72_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_12_72_base : receiptBase endpoint_12_72_flag endpoint_12_72_sources = some 238719972678383930 := by decide +kernel
private theorem endpoint_12_72_w0 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 2 238719972678383930 = some 238719972678383930 := by decide +kernel
private theorem endpoint_12_72_w2 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 2 2 238719972678383930 = some 238719972678383930 := by decide +kernel
private theorem endpoint_12_72_p4 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 4 238719972678383930 = some 238719972678383930 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 2 2 238719972678383930 238719972678383930 238719972678383930 endpoint_12_72_w0 endpoint_12_72_w2
private theorem endpoint_12_72_w4 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 4 2 238719972678383930 = some 238719972678383930 := by decide +kernel
private theorem endpoint_12_72_p6 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 6 238719972678383930 = some 238719972678383930 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 4 2 238719972678383930 238719972678383930 238719972678383930 endpoint_12_72_p4 endpoint_12_72_w4
private theorem endpoint_12_72_w6 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 6 2 238719972678383930 = some 238719972678383930 := by decide +kernel
private theorem endpoint_12_72_p8 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 8 238719972678383930 = some 238719972678383930 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 6 2 238719972678383930 238719972678383930 238719972678383930 endpoint_12_72_p6 endpoint_12_72_w6
private theorem endpoint_12_72_w8 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 8 2 238719972678383930 = some 238719972678383930 := by decide +kernel
private theorem endpoint_12_72_p10 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 10 238719972678383930 = some 238719972678383930 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 8 2 238719972678383930 238719972678383930 238719972678383930 endpoint_12_72_p8 endpoint_12_72_w8
private theorem endpoint_12_72_w10 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 10 1 238719972678383930 = some 238719972678383930 := by decide +kernel
private theorem endpoint_12_72_p11 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 11 238719972678383930 = some 238719972678383930 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 10 1 238719972678383930 238719972678383930 238719972678383930 endpoint_12_72_p10 endpoint_12_72_w10
def endpoint_12_72 : CertifiedEndpoint :=
  ⟨⟨12, 72, 2259⟩, 238719972678383930, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_12_72_flag endpoint_12_72_sources 11 238719972678383930 238719972678383930 rfl endpoint_12_72_base endpoint_12_72_p11) (by decide)⟩
private def endpoint_12_73_flag : Flag := ⟨12, 73, 2187⟩
private def endpoint_12_73_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_12_73_base : receiptBase endpoint_12_73_flag endpoint_12_73_sources = some 235812841216679521 := by decide +kernel
private theorem endpoint_12_73_w0 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 2 235812841216679521 = some 235812841216679521 := by decide +kernel
private theorem endpoint_12_73_w2 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 2 2 235812841216679521 = some 235812841216679521 := by decide +kernel
private theorem endpoint_12_73_p4 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 4 235812841216679521 = some 235812841216679521 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 2 2 235812841216679521 235812841216679521 235812841216679521 endpoint_12_73_w0 endpoint_12_73_w2
private theorem endpoint_12_73_w4 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 4 2 235812841216679521 = some 235812841216679521 := by decide +kernel
private theorem endpoint_12_73_p6 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 6 235812841216679521 = some 235812841216679521 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 4 2 235812841216679521 235812841216679521 235812841216679521 endpoint_12_73_p4 endpoint_12_73_w4
private theorem endpoint_12_73_w6 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 6 2 235812841216679521 = some 235812841216679521 := by decide +kernel
private theorem endpoint_12_73_p8 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 8 235812841216679521 = some 235812841216679521 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 6 2 235812841216679521 235812841216679521 235812841216679521 endpoint_12_73_p6 endpoint_12_73_w6
private theorem endpoint_12_73_w8 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 8 2 235812841216679521 = some 235812841216679521 := by decide +kernel
private theorem endpoint_12_73_p10 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 10 235812841216679521 = some 235812841216679521 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 8 2 235812841216679521 235812841216679521 235812841216679521 endpoint_12_73_p8 endpoint_12_73_w8
private theorem endpoint_12_73_w10 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 10 1 235812841216679521 = some 235812841216679521 := by decide +kernel
private theorem endpoint_12_73_p11 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 11 235812841216679521 = some 235812841216679521 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 10 1 235812841216679521 235812841216679521 235812841216679521 endpoint_12_73_p10 endpoint_12_73_w10
def endpoint_12_73 : CertifiedEndpoint :=
  ⟨⟨12, 73, 2187⟩, 235812841216679521, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_12_73_flag endpoint_12_73_sources 11 235812841216679521 235812841216679521 rfl endpoint_12_73_base endpoint_12_73_p11) (by decide)⟩
private def endpoint_12_74_flag : Flag := ⟨12, 74, 2112⟩
private def endpoint_12_74_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_12_74_base : receiptBase endpoint_12_74_flag endpoint_12_74_sources = some 230596990219857009 := by decide +kernel
private theorem endpoint_12_74_w0 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 2 230596990219857009 = some 230596990219857009 := by decide +kernel
private theorem endpoint_12_74_w2 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 2 2 230596990219857009 = some 230596990219857009 := by decide +kernel
private theorem endpoint_12_74_p4 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 4 230596990219857009 = some 230596990219857009 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 2 2 230596990219857009 230596990219857009 230596990219857009 endpoint_12_74_w0 endpoint_12_74_w2
private theorem endpoint_12_74_w4 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 4 2 230596990219857009 = some 230596990219857009 := by decide +kernel
private theorem endpoint_12_74_p6 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 6 230596990219857009 = some 230596990219857009 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 4 2 230596990219857009 230596990219857009 230596990219857009 endpoint_12_74_p4 endpoint_12_74_w4
private theorem endpoint_12_74_w6 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 6 2 230596990219857009 = some 230596990219857009 := by decide +kernel
private theorem endpoint_12_74_p8 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 8 230596990219857009 = some 230596990219857009 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 6 2 230596990219857009 230596990219857009 230596990219857009 endpoint_12_74_p6 endpoint_12_74_w6
private theorem endpoint_12_74_w8 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 8 2 230596990219857009 = some 230596990219857009 := by decide +kernel
private theorem endpoint_12_74_p10 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 10 230596990219857009 = some 230596990219857009 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 8 2 230596990219857009 230596990219857009 230596990219857009 endpoint_12_74_p8 endpoint_12_74_w8
private theorem endpoint_12_74_w10 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 10 1 230596990219857009 = some 230596990219857009 := by decide +kernel
private theorem endpoint_12_74_p11 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 11 230596990219857009 = some 230596990219857009 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 10 1 230596990219857009 230596990219857009 230596990219857009 endpoint_12_74_p10 endpoint_12_74_w10
def endpoint_12_74 : CertifiedEndpoint :=
  ⟨⟨12, 74, 2112⟩, 230596990219857009, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_12_74_flag endpoint_12_74_sources 11 230596990219857009 230596990219857009 rfl endpoint_12_74_base endpoint_12_74_p11) (by decide)⟩
private def endpoint_12_75_flag : Flag := ⟨12, 75, 2034⟩
private def endpoint_12_75_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_12_75_base : receiptBase endpoint_12_75_flag endpoint_12_75_sources = some 226699311593044602 := by decide +kernel
private theorem endpoint_12_75_w0 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 2 226699311593044602 = some 226699311593044602 := by decide +kernel
private theorem endpoint_12_75_w2 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 2 2 226699311593044602 = some 226699311593044602 := by decide +kernel
private theorem endpoint_12_75_p4 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 4 226699311593044602 = some 226699311593044602 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 2 2 226699311593044602 226699311593044602 226699311593044602 endpoint_12_75_w0 endpoint_12_75_w2
private theorem endpoint_12_75_w4 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 4 2 226699311593044602 = some 226699311593044602 := by decide +kernel
private theorem endpoint_12_75_p6 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 6 226699311593044602 = some 226699311593044602 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 4 2 226699311593044602 226699311593044602 226699311593044602 endpoint_12_75_p4 endpoint_12_75_w4
private theorem endpoint_12_75_w6 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 6 2 226699311593044602 = some 226699311593044602 := by decide +kernel
private theorem endpoint_12_75_p8 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 8 226699311593044602 = some 226699311593044602 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 6 2 226699311593044602 226699311593044602 226699311593044602 endpoint_12_75_p6 endpoint_12_75_w6
private theorem endpoint_12_75_w8 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 8 2 226699311593044602 = some 226699311593044602 := by decide +kernel
private theorem endpoint_12_75_p10 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 10 226699311593044602 = some 226699311593044602 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 8 2 226699311593044602 226699311593044602 226699311593044602 endpoint_12_75_p8 endpoint_12_75_w8
private theorem endpoint_12_75_w10 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 10 1 226699311593044602 = some 226699311593044602 := by decide +kernel
private theorem endpoint_12_75_p11 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 11 226699311593044602 = some 226699311593044602 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 10 1 226699311593044602 226699311593044602 226699311593044602 endpoint_12_75_p10 endpoint_12_75_w10
def endpoint_12_75 : CertifiedEndpoint :=
  ⟨⟨12, 75, 2034⟩, 226699311593044602, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_12_75_flag endpoint_12_75_sources 11 226699311593044602 226699311593044602 rfl endpoint_12_75_base endpoint_12_75_p11) (by decide)⟩
private def endpoint_12_76_flag : Flag := ⟨12, 76, 1954⟩
private def endpoint_12_76_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_12_76_base : receiptBase endpoint_12_76_flag endpoint_12_76_sources = some 220450966281757677 := by decide +kernel
private theorem endpoint_12_76_w0 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 2 220450966281757677 = some 220450966281757677 := by decide +kernel
private theorem endpoint_12_76_w2 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 2 2 220450966281757677 = some 220450966281757677 := by decide +kernel
private theorem endpoint_12_76_p4 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 4 220450966281757677 = some 220450966281757677 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 2 2 220450966281757677 220450966281757677 220450966281757677 endpoint_12_76_w0 endpoint_12_76_w2
private theorem endpoint_12_76_w4 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 4 2 220450966281757677 = some 220450966281757677 := by decide +kernel
private theorem endpoint_12_76_p6 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 6 220450966281757677 = some 220450966281757677 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 4 2 220450966281757677 220450966281757677 220450966281757677 endpoint_12_76_p4 endpoint_12_76_w4
private theorem endpoint_12_76_w6 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 6 2 220450966281757677 = some 220450966281757677 := by decide +kernel
private theorem endpoint_12_76_p8 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 8 220450966281757677 = some 220450966281757677 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 6 2 220450966281757677 220450966281757677 220450966281757677 endpoint_12_76_p6 endpoint_12_76_w6
private theorem endpoint_12_76_w8 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 8 2 220450966281757677 = some 220450966281757677 := by decide +kernel
private theorem endpoint_12_76_p10 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 10 220450966281757677 = some 220450966281757677 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 8 2 220450966281757677 220450966281757677 220450966281757677 endpoint_12_76_p8 endpoint_12_76_w8
private theorem endpoint_12_76_w10 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 10 1 220450966281757677 = some 220450966281757677 := by decide +kernel
private theorem endpoint_12_76_p11 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 11 220450966281757677 = some 220450966281757677 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 10 1 220450966281757677 220450966281757677 220450966281757677 endpoint_12_76_p10 endpoint_12_76_w10
def endpoint_12_76 : CertifiedEndpoint :=
  ⟨⟨12, 76, 1954⟩, 220450966281757677, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_12_76_flag endpoint_12_76_sources 11 220450966281757677 220450966281757677 rfl endpoint_12_76_base endpoint_12_76_p11) (by decide)⟩
private def endpoint_12_77_flag : Flag := ⟨12, 77, 1872⟩
private def endpoint_12_77_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_12_77_base : receiptBase endpoint_12_77_flag endpoint_12_77_sources = some 213764273633086795 := by decide +kernel
private theorem endpoint_12_77_w0 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 2 213764273633086795 = some 213764273633086795 := by decide +kernel
private theorem endpoint_12_77_w2 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 2 2 213764273633086795 = some 213764273633086795 := by decide +kernel
private theorem endpoint_12_77_p4 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 4 213764273633086795 = some 213764273633086795 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 2 2 213764273633086795 213764273633086795 213764273633086795 endpoint_12_77_w0 endpoint_12_77_w2
private theorem endpoint_12_77_w4 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 4 2 213764273633086795 = some 213764273633086795 := by decide +kernel
private theorem endpoint_12_77_p6 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 6 213764273633086795 = some 213764273633086795 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 4 2 213764273633086795 213764273633086795 213764273633086795 endpoint_12_77_p4 endpoint_12_77_w4
private theorem endpoint_12_77_w6 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 6 2 213764273633086795 = some 213764273633086795 := by decide +kernel
private theorem endpoint_12_77_p8 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 8 213764273633086795 = some 213764273633086795 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 6 2 213764273633086795 213764273633086795 213764273633086795 endpoint_12_77_p6 endpoint_12_77_w6
private theorem endpoint_12_77_w8 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 8 2 213764273633086795 = some 213764273633086795 := by decide +kernel
private theorem endpoint_12_77_p10 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 10 213764273633086795 = some 213764273633086795 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 8 2 213764273633086795 213764273633086795 213764273633086795 endpoint_12_77_p8 endpoint_12_77_w8
private theorem endpoint_12_77_w10 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 10 1 213764273633086795 = some 213764273633086795 := by decide +kernel
private theorem endpoint_12_77_p11 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 11 213764273633086795 = some 213764273633086795 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 10 1 213764273633086795 213764273633086795 213764273633086795 endpoint_12_77_p10 endpoint_12_77_w10
def endpoint_12_77 : CertifiedEndpoint :=
  ⟨⟨12, 77, 1872⟩, 213764273633086795, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_12_77_flag endpoint_12_77_sources 11 213764273633086795 213764273633086795 rfl endpoint_12_77_base endpoint_12_77_p11) (by decide)⟩
private def endpoint_12_78_flag : Flag := ⟨12, 78, 1787⟩
private def endpoint_12_78_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_12_78_base : receiptBase endpoint_12_78_flag endpoint_12_78_sources = some 210099344805005416 := by decide +kernel
private theorem endpoint_12_78_w0 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 2 210099344805005416 = some 210099344805005416 := by decide +kernel
private theorem endpoint_12_78_w2 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 2 2 210099344805005416 = some 210099344805005416 := by decide +kernel
private theorem endpoint_12_78_p4 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 4 210099344805005416 = some 210099344805005416 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 2 2 210099344805005416 210099344805005416 210099344805005416 endpoint_12_78_w0 endpoint_12_78_w2
private theorem endpoint_12_78_w4 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 4 2 210099344805005416 = some 210099344805005416 := by decide +kernel
private theorem endpoint_12_78_p6 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 6 210099344805005416 = some 210099344805005416 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 4 2 210099344805005416 210099344805005416 210099344805005416 endpoint_12_78_p4 endpoint_12_78_w4
private theorem endpoint_12_78_w6 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 6 2 210099344805005416 = some 210099344805005416 := by decide +kernel
private theorem endpoint_12_78_p8 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 8 210099344805005416 = some 210099344805005416 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 6 2 210099344805005416 210099344805005416 210099344805005416 endpoint_12_78_p6 endpoint_12_78_w6
private theorem endpoint_12_78_w8 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 8 2 210099344805005416 = some 210099344805005416 := by decide +kernel
private theorem endpoint_12_78_p10 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 10 210099344805005416 = some 210099344805005416 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 8 2 210099344805005416 210099344805005416 210099344805005416 endpoint_12_78_p8 endpoint_12_78_w8
private theorem endpoint_12_78_w10 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 10 1 210099344805005416 = some 210099344805005416 := by decide +kernel
private theorem endpoint_12_78_p11 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 11 210099344805005416 = some 210099344805005416 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 10 1 210099344805005416 210099344805005416 210099344805005416 endpoint_12_78_p10 endpoint_12_78_w10
def endpoint_12_78 : CertifiedEndpoint :=
  ⟨⟨12, 78, 1787⟩, 210099344805005416, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_12_78_flag endpoint_12_78_sources 11 210099344805005416 210099344805005416 rfl endpoint_12_78_base endpoint_12_78_p11) (by decide)⟩
private def endpoint_12_79_flag : Flag := ⟨12, 79, 1699⟩
private def endpoint_12_79_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_12_79_base : receiptBase endpoint_12_79_flag endpoint_12_79_sources = some 202094165173306076 := by decide +kernel
private theorem endpoint_12_79_w0 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 2 202094165173306076 = some 202094165173306076 := by decide +kernel
private theorem endpoint_12_79_w2 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 2 2 202094165173306076 = some 202094165173306076 := by decide +kernel
private theorem endpoint_12_79_p4 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 4 202094165173306076 = some 202094165173306076 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 2 2 202094165173306076 202094165173306076 202094165173306076 endpoint_12_79_w0 endpoint_12_79_w2
private theorem endpoint_12_79_w4 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 4 2 202094165173306076 = some 202094165173306076 := by decide +kernel
private theorem endpoint_12_79_p6 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 6 202094165173306076 = some 202094165173306076 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 4 2 202094165173306076 202094165173306076 202094165173306076 endpoint_12_79_p4 endpoint_12_79_w4
private theorem endpoint_12_79_w6 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 6 2 202094165173306076 = some 202094165173306076 := by decide +kernel
private theorem endpoint_12_79_p8 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 8 202094165173306076 = some 202094165173306076 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 6 2 202094165173306076 202094165173306076 202094165173306076 endpoint_12_79_p6 endpoint_12_79_w6
private theorem endpoint_12_79_w8 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 8 2 202094165173306076 = some 202094165173306076 := by decide +kernel
private theorem endpoint_12_79_p10 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 10 202094165173306076 = some 202094165173306076 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 8 2 202094165173306076 202094165173306076 202094165173306076 endpoint_12_79_p8 endpoint_12_79_w8
private theorem endpoint_12_79_w10 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 10 1 202094165173306076 = some 202094165173306076 := by decide +kernel
private theorem endpoint_12_79_p11 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 11 202094165173306076 = some 202094165173306076 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 10 1 202094165173306076 202094165173306076 202094165173306076 endpoint_12_79_p10 endpoint_12_79_w10
def endpoint_12_79 : CertifiedEndpoint :=
  ⟨⟨12, 79, 1699⟩, 202094165173306076, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_12_79_flag endpoint_12_79_sources 11 202094165173306076 202094165173306076 rfl endpoint_12_79_base endpoint_12_79_p11) (by decide)⟩
private def endpoint_12_80_flag : Flag := ⟨12, 80, 1609⟩
private def endpoint_12_80_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_12_80_base : receiptBase endpoint_12_80_flag endpoint_12_80_sources = some 193922087052803993 := by decide +kernel
private theorem endpoint_12_80_w0 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 2 193922087052803993 = some 193922087052803993 := by decide +kernel
private theorem endpoint_12_80_w2 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 2 2 193922087052803993 = some 193922087052803993 := by decide +kernel
private theorem endpoint_12_80_p4 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 4 193922087052803993 = some 193922087052803993 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 2 2 193922087052803993 193922087052803993 193922087052803993 endpoint_12_80_w0 endpoint_12_80_w2
private theorem endpoint_12_80_w4 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 4 2 193922087052803993 = some 193922087052803993 := by decide +kernel
private theorem endpoint_12_80_p6 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 6 193922087052803993 = some 193922087052803993 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 4 2 193922087052803993 193922087052803993 193922087052803993 endpoint_12_80_p4 endpoint_12_80_w4
private theorem endpoint_12_80_w6 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 6 2 193922087052803993 = some 193922087052803993 := by decide +kernel
private theorem endpoint_12_80_p8 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 8 193922087052803993 = some 193922087052803993 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 6 2 193922087052803993 193922087052803993 193922087052803993 endpoint_12_80_p6 endpoint_12_80_w6
private theorem endpoint_12_80_w8 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 8 2 193922087052803993 = some 193922087052803993 := by decide +kernel
private theorem endpoint_12_80_p10 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 10 193922087052803993 = some 193922087052803993 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 8 2 193922087052803993 193922087052803993 193922087052803993 endpoint_12_80_p8 endpoint_12_80_w8
private theorem endpoint_12_80_w10 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 10 1 193922087052803993 = some 193922087052803993 := by decide +kernel
private theorem endpoint_12_80_p11 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 11 193922087052803993 = some 193922087052803993 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 10 1 193922087052803993 193922087052803993 193922087052803993 endpoint_12_80_p10 endpoint_12_80_w10
def endpoint_12_80 : CertifiedEndpoint :=
  ⟨⟨12, 80, 1609⟩, 193922087052803993, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_12_80_flag endpoint_12_80_sources 11 193922087052803993 193922087052803993 rfl endpoint_12_80_base endpoint_12_80_p11) (by decide)⟩
private def endpoint_12_81_flag : Flag := ⟨12, 81, 1516⟩
private def endpoint_12_81_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_12_81_base : receiptBase endpoint_12_81_flag endpoint_12_81_sources = some 185883765635086493 := by decide +kernel
private theorem endpoint_12_81_w0 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 2 185883765635086493 = some 185883765635086493 := by decide +kernel
private theorem endpoint_12_81_w2 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 2 2 185883765635086493 = some 185883765635086493 := by decide +kernel
private theorem endpoint_12_81_p4 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 4 185883765635086493 = some 185883765635086493 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 2 2 185883765635086493 185883765635086493 185883765635086493 endpoint_12_81_w0 endpoint_12_81_w2
private theorem endpoint_12_81_w4 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 4 2 185883765635086493 = some 185883765635086493 := by decide +kernel
private theorem endpoint_12_81_p6 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 6 185883765635086493 = some 185883765635086493 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 4 2 185883765635086493 185883765635086493 185883765635086493 endpoint_12_81_p4 endpoint_12_81_w4
private theorem endpoint_12_81_w6 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 6 2 185883765635086493 = some 185883765635086493 := by decide +kernel
private theorem endpoint_12_81_p8 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 8 185883765635086493 = some 185883765635086493 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 6 2 185883765635086493 185883765635086493 185883765635086493 endpoint_12_81_p6 endpoint_12_81_w6
private theorem endpoint_12_81_w8 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 8 2 185883765635086493 = some 185883765635086493 := by decide +kernel
private theorem endpoint_12_81_p10 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 10 185883765635086493 = some 185883765635086493 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 8 2 185883765635086493 185883765635086493 185883765635086493 endpoint_12_81_p8 endpoint_12_81_w8
private theorem endpoint_12_81_w10 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 10 1 185883765635086493 = some 185883765635086493 := by decide +kernel
private theorem endpoint_12_81_p11 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 11 185883765635086493 = some 185883765635086493 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 10 1 185883765635086493 185883765635086493 185883765635086493 endpoint_12_81_p10 endpoint_12_81_w10
def endpoint_12_81 : CertifiedEndpoint :=
  ⟨⟨12, 81, 1516⟩, 185883765635086493, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_12_81_flag endpoint_12_81_sources 11 185883765635086493 185883765635086493 rfl endpoint_12_81_base endpoint_12_81_p11) (by decide)⟩
private def endpoint_12_82_flag : Flag := ⟨12, 82, 1420⟩
private def endpoint_12_82_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_12_82_base : receiptBase endpoint_12_82_flag endpoint_12_82_sources = some 176134610982570594 := by decide +kernel
private theorem endpoint_12_82_w0 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 2 176134610982570594 = some 176134610982570594 := by decide +kernel
private theorem endpoint_12_82_w2 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 2 2 176134610982570594 = some 176134610982570594 := by decide +kernel
private theorem endpoint_12_82_p4 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 4 176134610982570594 = some 176134610982570594 :=
  join_receipt_window endpoint_12_82_flag endpoint_12_82_sources 0 2 2 176134610982570594 176134610982570594 176134610982570594 endpoint_12_82_w0 endpoint_12_82_w2
private theorem endpoint_12_82_w4 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 4 2 176134610982570594 = some 176134610982570594 := by decide +kernel
private theorem endpoint_12_82_p6 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 6 176134610982570594 = some 176134610982570594 :=
  join_receipt_window endpoint_12_82_flag endpoint_12_82_sources 0 4 2 176134610982570594 176134610982570594 176134610982570594 endpoint_12_82_p4 endpoint_12_82_w4
private theorem endpoint_12_82_w6 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 6 2 176134610982570594 = some 176134610982570594 := by decide +kernel
private theorem endpoint_12_82_p8 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 8 176134610982570594 = some 176134610982570594 :=
  join_receipt_window endpoint_12_82_flag endpoint_12_82_sources 0 6 2 176134610982570594 176134610982570594 176134610982570594 endpoint_12_82_p6 endpoint_12_82_w6
private theorem endpoint_12_82_w8 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 8 2 176134610982570594 = some 176134610982570594 := by decide +kernel
private theorem endpoint_12_82_p10 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 10 176134610982570594 = some 176134610982570594 :=
  join_receipt_window endpoint_12_82_flag endpoint_12_82_sources 0 8 2 176134610982570594 176134610982570594 176134610982570594 endpoint_12_82_p8 endpoint_12_82_w8
private theorem endpoint_12_82_w10 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 10 1 176134610982570594 = some 176134610982570594 := by decide +kernel
private theorem endpoint_12_82_p11 : receiptWindow endpoint_12_82_flag endpoint_12_82_sources 0 11 176134610982570594 = some 176134610982570594 :=
  join_receipt_window endpoint_12_82_flag endpoint_12_82_sources 0 10 1 176134610982570594 176134610982570594 176134610982570594 endpoint_12_82_p10 endpoint_12_82_w10
def endpoint_12_82 : CertifiedEndpoint :=
  ⟨⟨12, 82, 1420⟩, 176134610982570594, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_12_82_flag endpoint_12_82_sources 11 176134610982570594 176134610982570594 rfl endpoint_12_82_base endpoint_12_82_p11) (by decide)⟩
private def endpoint_12_83_flag : Flag := ⟨12, 83, 1322⟩
private def endpoint_12_83_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_12_83_base : receiptBase endpoint_12_83_flag endpoint_12_83_sources = some 165876557637328258 := by decide +kernel
private theorem endpoint_12_83_w0 : receiptWindow endpoint_12_83_flag endpoint_12_83_sources 0 2 165876557637328258 = some 165876557637328258 := by decide +kernel
private theorem endpoint_12_83_w2 : receiptWindow endpoint_12_83_flag endpoint_12_83_sources 2 2 165876557637328258 = some 165876557637328258 := by decide +kernel
private theorem endpoint_12_83_p4 : receiptWindow endpoint_12_83_flag endpoint_12_83_sources 0 4 165876557637328258 = some 165876557637328258 :=
  join_receipt_window endpoint_12_83_flag endpoint_12_83_sources 0 2 2 165876557637328258 165876557637328258 165876557637328258 endpoint_12_83_w0 endpoint_12_83_w2
private theorem endpoint_12_83_w4 : receiptWindow endpoint_12_83_flag endpoint_12_83_sources 4 2 165876557637328258 = some 165876557637328258 := by decide +kernel
private theorem endpoint_12_83_p6 : receiptWindow endpoint_12_83_flag endpoint_12_83_sources 0 6 165876557637328258 = some 165876557637328258 :=
  join_receipt_window endpoint_12_83_flag endpoint_12_83_sources 0 4 2 165876557637328258 165876557637328258 165876557637328258 endpoint_12_83_p4 endpoint_12_83_w4
private theorem endpoint_12_83_w6 : receiptWindow endpoint_12_83_flag endpoint_12_83_sources 6 2 165876557637328258 = some 165876557637328258 := by decide +kernel
private theorem endpoint_12_83_p8 : receiptWindow endpoint_12_83_flag endpoint_12_83_sources 0 8 165876557637328258 = some 165876557637328258 :=
  join_receipt_window endpoint_12_83_flag endpoint_12_83_sources 0 6 2 165876557637328258 165876557637328258 165876557637328258 endpoint_12_83_p6 endpoint_12_83_w6
private theorem endpoint_12_83_w8 : receiptWindow endpoint_12_83_flag endpoint_12_83_sources 8 2 165876557637328258 = some 165876557637328258 := by decide +kernel
private theorem endpoint_12_83_p10 : receiptWindow endpoint_12_83_flag endpoint_12_83_sources 0 10 165876557637328258 = some 165876557637328258 :=
  join_receipt_window endpoint_12_83_flag endpoint_12_83_sources 0 8 2 165876557637328258 165876557637328258 165876557637328258 endpoint_12_83_p8 endpoint_12_83_w8
private theorem endpoint_12_83_w10 : receiptWindow endpoint_12_83_flag endpoint_12_83_sources 10 1 165876557637328258 = some 165876557637328258 := by decide +kernel
private theorem endpoint_12_83_p11 : receiptWindow endpoint_12_83_flag endpoint_12_83_sources 0 11 165876557637328258 = some 165876557637328258 :=
  join_receipt_window endpoint_12_83_flag endpoint_12_83_sources 0 10 1 165876557637328258 165876557637328258 165876557637328258 endpoint_12_83_p10 endpoint_12_83_w10
def endpoint_12_83 : CertifiedEndpoint :=
  ⟨⟨12, 83, 1322⟩, 165876557637328258, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_12_83_flag endpoint_12_83_sources 11 165876557637328258 165876557637328258 rfl endpoint_12_83_base endpoint_12_83_p11) (by decide)⟩
private def endpoint_12_84_flag : Flag := ⟨12, 84, 1222⟩
private def endpoint_12_84_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_12_84_base : receiptBase endpoint_12_84_flag endpoint_12_84_sources = some 155101496071665364 := by decide +kernel
private theorem endpoint_12_84_w0 : receiptWindow endpoint_12_84_flag endpoint_12_84_sources 0 2 155101496071665364 = some 155101496071665364 := by decide +kernel
private theorem endpoint_12_84_w2 : receiptWindow endpoint_12_84_flag endpoint_12_84_sources 2 2 155101496071665364 = some 155101496071665364 := by decide +kernel
private theorem endpoint_12_84_p4 : receiptWindow endpoint_12_84_flag endpoint_12_84_sources 0 4 155101496071665364 = some 155101496071665364 :=
  join_receipt_window endpoint_12_84_flag endpoint_12_84_sources 0 2 2 155101496071665364 155101496071665364 155101496071665364 endpoint_12_84_w0 endpoint_12_84_w2
private theorem endpoint_12_84_w4 : receiptWindow endpoint_12_84_flag endpoint_12_84_sources 4 2 155101496071665364 = some 155101496071665364 := by decide +kernel
private theorem endpoint_12_84_p6 : receiptWindow endpoint_12_84_flag endpoint_12_84_sources 0 6 155101496071665364 = some 155101496071665364 :=
  join_receipt_window endpoint_12_84_flag endpoint_12_84_sources 0 4 2 155101496071665364 155101496071665364 155101496071665364 endpoint_12_84_p4 endpoint_12_84_w4
private theorem endpoint_12_84_w6 : receiptWindow endpoint_12_84_flag endpoint_12_84_sources 6 2 155101496071665364 = some 155101496071665364 := by decide +kernel
private theorem endpoint_12_84_p8 : receiptWindow endpoint_12_84_flag endpoint_12_84_sources 0 8 155101496071665364 = some 155101496071665364 :=
  join_receipt_window endpoint_12_84_flag endpoint_12_84_sources 0 6 2 155101496071665364 155101496071665364 155101496071665364 endpoint_12_84_p6 endpoint_12_84_w6
private theorem endpoint_12_84_w8 : receiptWindow endpoint_12_84_flag endpoint_12_84_sources 8 2 155101496071665364 = some 155101496071665364 := by decide +kernel
private theorem endpoint_12_84_p10 : receiptWindow endpoint_12_84_flag endpoint_12_84_sources 0 10 155101496071665364 = some 155101496071665364 :=
  join_receipt_window endpoint_12_84_flag endpoint_12_84_sources 0 8 2 155101496071665364 155101496071665364 155101496071665364 endpoint_12_84_p8 endpoint_12_84_w8
private theorem endpoint_12_84_w10 : receiptWindow endpoint_12_84_flag endpoint_12_84_sources 10 1 155101496071665364 = some 155101496071665364 := by decide +kernel
private theorem endpoint_12_84_p11 : receiptWindow endpoint_12_84_flag endpoint_12_84_sources 0 11 155101496071665364 = some 155101496071665364 :=
  join_receipt_window endpoint_12_84_flag endpoint_12_84_sources 0 10 1 155101496071665364 155101496071665364 155101496071665364 endpoint_12_84_p10 endpoint_12_84_w10
def endpoint_12_84 : CertifiedEndpoint :=
  ⟨⟨12, 84, 1222⟩, 155101496071665364, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_12_84_flag endpoint_12_84_sources 11 155101496071665364 155101496071665364 rfl endpoint_12_84_base endpoint_12_84_p11) (by decide)⟩
def endpoint_12_85 : CertifiedEndpoint :=
  ⟨⟨12, 85, 1118⟩, 250200224254567691, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_86 : CertifiedEndpoint :=
  ⟨⟨12, 86, 1013⟩, 228457736597096271, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_87 : CertifiedEndpoint :=
  ⟨⟨12, 87, 904⟩, 205131036276446461, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_88 : CertifiedEndpoint :=
  ⟨⟨12, 88, 793⟩, 180668941484348099, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_89 : CertifiedEndpoint :=
  ⟨⟨12, 89, 679⟩, 154808404633004044, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_90 : CertifiedEndpoint :=
  ⟨⟨12, 90, 563⟩, 127770862626592121, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_91 : CertifiedEndpoint :=
  ⟨⟨12, 91, 444⟩, 99287323493941001, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_92 : CertifiedEndpoint :=
  ⟨⟨12, 92, 322⟩, 69331037509866838, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_93 : CertifiedEndpoint :=
  ⟨⟨12, 93, 198⟩, 38132358153608739, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_13 : CertifiedEndpoint :=
  ⟨⟨13, 13, 4123⟩, 97626330505172216, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_14 : CertifiedEndpoint :=
  ⟨⟨13, 14, 4103⟩, 101470972473317212, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_15 : CertifiedEndpoint :=
  ⟨⟨13, 15, 4083⟩, 105273350896337128, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_16 : CertifiedEndpoint :=
  ⟨⟨13, 16, 4063⟩, 117829399133734303, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_17 : CertifiedEndpoint :=
  ⟨⟨13, 17, 4043⟩, 130253021634461292, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_18 : CertifiedEndpoint :=
  ⟨⟨13, 18, 4022⟩, 142508680916030894, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_19 : CertifiedEndpoint :=
  ⟨⟨13, 19, 4001⟩, 154625454668897618, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_20 : CertifiedEndpoint :=
  ⟨⟨13, 20, 3980⟩, 166603342893061464, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_21 : CertifiedEndpoint :=
  ⟨⟨13, 21, 3958⟩, 178397118417986193, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_22 : CertifiedEndpoint :=
  ⟨⟨13, 22, 3937⟩, 190094005688727937, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_23 : CertifiedEndpoint :=
  ⟨⟨13, 23, 3915⟩, 201600320468197872, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_24 : CertifiedEndpoint :=
  ⟨⟨13, 24, 3893⟩, 212961289926932237, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_25 : CertifiedEndpoint :=
  ⟨⟨13, 25, 3870⟩, 224118767310329409, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_26 : CertifiedEndpoint :=
  ⟨⟨13, 26, 3848⟩, 235185816231576288, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_27 : CertifiedEndpoint :=
  ⟨⟨13, 27, 3825⟩, 246042913285453282, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_28 : CertifiedEndpoint :=
  ⟨⟨13, 28, 3802⟩, 256748205226562014, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_13_29_flag : Flag := ⟨13, 29, 3778⟩
private def endpoint_13_29_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_29_base : receiptBase endpoint_13_29_flag endpoint_13_29_sources = some 179551575797115890 := by decide +kernel
private theorem endpoint_13_29_w0 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 2 179551575797115890 = some 179551575797115890 := by decide +kernel
private theorem endpoint_13_29_w2 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 2 2 179551575797115890 = some 179551575797115890 := by decide +kernel
private theorem endpoint_13_29_p4 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 4 179551575797115890 = some 179551575797115890 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 2 2 179551575797115890 179551575797115890 179551575797115890 endpoint_13_29_w0 endpoint_13_29_w2
private theorem endpoint_13_29_w4 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 4 2 179551575797115890 = some 179551575797115890 := by decide +kernel
private theorem endpoint_13_29_p6 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 6 179551575797115890 = some 179551575797115890 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 4 2 179551575797115890 179551575797115890 179551575797115890 endpoint_13_29_p4 endpoint_13_29_w4
private theorem endpoint_13_29_w6 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 6 2 179551575797115890 = some 179551575797115890 := by decide +kernel
private theorem endpoint_13_29_p8 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 8 179551575797115890 = some 179551575797115890 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 6 2 179551575797115890 179551575797115890 179551575797115890 endpoint_13_29_p6 endpoint_13_29_w6
private theorem endpoint_13_29_w8 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 8 2 179551575797115890 = some 179551575797115890 := by decide +kernel
private theorem endpoint_13_29_p10 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 10 179551575797115890 = some 179551575797115890 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 8 2 179551575797115890 179551575797115890 179551575797115890 endpoint_13_29_p8 endpoint_13_29_w8
private theorem endpoint_13_29_w10 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 10 2 179551575797115890 = some 179551575797115890 := by decide +kernel
private theorem endpoint_13_29_p12 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 12 179551575797115890 = some 179551575797115890 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 10 2 179551575797115890 179551575797115890 179551575797115890 endpoint_13_29_p10 endpoint_13_29_w10
def endpoint_13_29 : CertifiedEndpoint :=
  ⟨⟨13, 29, 3778⟩, 179551575797115890, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_29_flag endpoint_13_29_sources 12 179551575797115890 179551575797115890 rfl endpoint_13_29_base endpoint_13_29_p12) (by decide)⟩
private def endpoint_13_30_flag : Flag := ⟨13, 30, 3755⟩
private def endpoint_13_30_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_30_base : receiptBase endpoint_13_30_flag endpoint_13_30_sources = some 183487485415032722 := by decide +kernel
private theorem endpoint_13_30_w0 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 2 183487485415032722 = some 183487485415032722 := by decide +kernel
private theorem endpoint_13_30_w2 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 2 2 183487485415032722 = some 183487485415032722 := by decide +kernel
private theorem endpoint_13_30_p4 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 4 183487485415032722 = some 183487485415032722 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 2 2 183487485415032722 183487485415032722 183487485415032722 endpoint_13_30_w0 endpoint_13_30_w2
private theorem endpoint_13_30_w4 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 4 2 183487485415032722 = some 183487485415032722 := by decide +kernel
private theorem endpoint_13_30_p6 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 6 183487485415032722 = some 183487485415032722 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 4 2 183487485415032722 183487485415032722 183487485415032722 endpoint_13_30_p4 endpoint_13_30_w4
private theorem endpoint_13_30_w6 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 6 2 183487485415032722 = some 183487485415032722 := by decide +kernel
private theorem endpoint_13_30_p8 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 8 183487485415032722 = some 183487485415032722 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 6 2 183487485415032722 183487485415032722 183487485415032722 endpoint_13_30_p6 endpoint_13_30_w6
private theorem endpoint_13_30_w8 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 8 2 183487485415032722 = some 183487485415032722 := by decide +kernel
private theorem endpoint_13_30_p10 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 10 183487485415032722 = some 183487485415032722 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 8 2 183487485415032722 183487485415032722 183487485415032722 endpoint_13_30_p8 endpoint_13_30_w8
private theorem endpoint_13_30_w10 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 10 2 183487485415032722 = some 183487485415032722 := by decide +kernel
private theorem endpoint_13_30_p12 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 12 183487485415032722 = some 183487485415032722 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 10 2 183487485415032722 183487485415032722 183487485415032722 endpoint_13_30_p10 endpoint_13_30_w10
def endpoint_13_30 : CertifiedEndpoint :=
  ⟨⟨13, 30, 3755⟩, 183487485415032722, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_30_flag endpoint_13_30_sources 12 183487485415032722 183487485415032722 rfl endpoint_13_30_base endpoint_13_30_p12) (by decide)⟩
private def endpoint_13_31_flag : Flag := ⟨13, 31, 3730⟩
private def endpoint_13_31_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_31_base : receiptBase endpoint_13_31_flag endpoint_13_31_sources = some 187263123745959629 := by decide +kernel
private theorem endpoint_13_31_w0 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 2 187263123745959629 = some 187263123745959629 := by decide +kernel
private theorem endpoint_13_31_w2 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 2 2 187263123745959629 = some 187263123745959629 := by decide +kernel
private theorem endpoint_13_31_p4 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 4 187263123745959629 = some 187263123745959629 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 2 2 187263123745959629 187263123745959629 187263123745959629 endpoint_13_31_w0 endpoint_13_31_w2
private theorem endpoint_13_31_w4 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 4 2 187263123745959629 = some 187263123745959629 := by decide +kernel
private theorem endpoint_13_31_p6 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 6 187263123745959629 = some 187263123745959629 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 4 2 187263123745959629 187263123745959629 187263123745959629 endpoint_13_31_p4 endpoint_13_31_w4
private theorem endpoint_13_31_w6 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 6 2 187263123745959629 = some 187263123745959629 := by decide +kernel
private theorem endpoint_13_31_p8 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 8 187263123745959629 = some 187263123745959629 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 6 2 187263123745959629 187263123745959629 187263123745959629 endpoint_13_31_p6 endpoint_13_31_w6
private theorem endpoint_13_31_w8 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 8 2 187263123745959629 = some 187263123745959629 := by decide +kernel
private theorem endpoint_13_31_p10 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 10 187263123745959629 = some 187263123745959629 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 8 2 187263123745959629 187263123745959629 187263123745959629 endpoint_13_31_p8 endpoint_13_31_w8
private theorem endpoint_13_31_w10 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 10 2 187263123745959629 = some 187263123745959629 := by decide +kernel
private theorem endpoint_13_31_p12 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 12 187263123745959629 = some 187263123745959629 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 10 2 187263123745959629 187263123745959629 187263123745959629 endpoint_13_31_p10 endpoint_13_31_w10
def endpoint_13_31 : CertifiedEndpoint :=
  ⟨⟨13, 31, 3730⟩, 187263123745959629, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_31_flag endpoint_13_31_sources 12 187263123745959629 187263123745959629 rfl endpoint_13_31_base endpoint_13_31_p12) (by decide)⟩
private def endpoint_13_32_flag : Flag := ⟨13, 32, 3706⟩
private def endpoint_13_32_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_32_base : receiptBase endpoint_13_32_flag endpoint_13_32_sources = some 191022902868341909 := by decide +kernel
private theorem endpoint_13_32_w0 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 2 191022902868341909 = some 191022902868341909 := by decide +kernel
private theorem endpoint_13_32_w2 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 2 2 191022902868341909 = some 191022902868341909 := by decide +kernel
private theorem endpoint_13_32_p4 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 4 191022902868341909 = some 191022902868341909 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 2 2 191022902868341909 191022902868341909 191022902868341909 endpoint_13_32_w0 endpoint_13_32_w2
private theorem endpoint_13_32_w4 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 4 2 191022902868341909 = some 191022902868341909 := by decide +kernel
private theorem endpoint_13_32_p6 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 6 191022902868341909 = some 191022902868341909 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 4 2 191022902868341909 191022902868341909 191022902868341909 endpoint_13_32_p4 endpoint_13_32_w4
private theorem endpoint_13_32_w6 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 6 2 191022902868341909 = some 191022902868341909 := by decide +kernel
private theorem endpoint_13_32_p8 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 8 191022902868341909 = some 191022902868341909 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 6 2 191022902868341909 191022902868341909 191022902868341909 endpoint_13_32_p6 endpoint_13_32_w6
private theorem endpoint_13_32_w8 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 8 2 191022902868341909 = some 191022902868341909 := by decide +kernel
private theorem endpoint_13_32_p10 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 10 191022902868341909 = some 191022902868341909 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 8 2 191022902868341909 191022902868341909 191022902868341909 endpoint_13_32_p8 endpoint_13_32_w8
private theorem endpoint_13_32_w10 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 10 2 191022902868341909 = some 191022902868341909 := by decide +kernel
private theorem endpoint_13_32_p12 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 12 191022902868341909 = some 191022902868341909 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 10 2 191022902868341909 191022902868341909 191022902868341909 endpoint_13_32_p10 endpoint_13_32_w10
def endpoint_13_32 : CertifiedEndpoint :=
  ⟨⟨13, 32, 3706⟩, 191022902868341909, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_32_flag endpoint_13_32_sources 12 191022902868341909 191022902868341909 rfl endpoint_13_32_base endpoint_13_32_p12) (by decide)⟩
private def endpoint_13_33_flag : Flag := ⟨13, 33, 3681⟩
private def endpoint_13_33_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_33_base : receiptBase endpoint_13_33_flag endpoint_13_33_sources = some 194666631145677022 := by decide +kernel
private theorem endpoint_13_33_w0 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 2 194666631145677022 = some 194666631145677022 := by decide +kernel
private theorem endpoint_13_33_w2 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 2 2 194666631145677022 = some 194666631145677022 := by decide +kernel
private theorem endpoint_13_33_p4 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 4 194666631145677022 = some 194666631145677022 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 2 2 194666631145677022 194666631145677022 194666631145677022 endpoint_13_33_w0 endpoint_13_33_w2
private theorem endpoint_13_33_w4 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 4 2 194666631145677022 = some 194666631145677022 := by decide +kernel
private theorem endpoint_13_33_p6 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 6 194666631145677022 = some 194666631145677022 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 4 2 194666631145677022 194666631145677022 194666631145677022 endpoint_13_33_p4 endpoint_13_33_w4
private theorem endpoint_13_33_w6 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 6 2 194666631145677022 = some 194666631145677022 := by decide +kernel
private theorem endpoint_13_33_p8 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 8 194666631145677022 = some 194666631145677022 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 6 2 194666631145677022 194666631145677022 194666631145677022 endpoint_13_33_p6 endpoint_13_33_w6
private theorem endpoint_13_33_w8 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 8 2 194666631145677022 = some 194666631145677022 := by decide +kernel
private theorem endpoint_13_33_p10 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 10 194666631145677022 = some 194666631145677022 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 8 2 194666631145677022 194666631145677022 194666631145677022 endpoint_13_33_p8 endpoint_13_33_w8
private theorem endpoint_13_33_w10 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 10 2 194666631145677022 = some 194666631145677022 := by decide +kernel
private theorem endpoint_13_33_p12 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 12 194666631145677022 = some 194666631145677022 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 10 2 194666631145677022 194666631145677022 194666631145677022 endpoint_13_33_p10 endpoint_13_33_w10
def endpoint_13_33 : CertifiedEndpoint :=
  ⟨⟨13, 33, 3681⟩, 194666631145677022, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_33_flag endpoint_13_33_sources 12 194666631145677022 194666631145677022 rfl endpoint_13_33_base endpoint_13_33_p12) (by decide)⟩
private def endpoint_13_34_flag : Flag := ⟨13, 34, 3656⟩
private def endpoint_13_34_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_34_base : receiptBase endpoint_13_34_flag endpoint_13_34_sources = some 198243751576626402 := by decide +kernel
private theorem endpoint_13_34_w0 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 2 198243751576626402 = some 198243751576626402 := by decide +kernel
private theorem endpoint_13_34_w2 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 2 2 198243751576626402 = some 198243751576626402 := by decide +kernel
private theorem endpoint_13_34_p4 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 4 198243751576626402 = some 198243751576626402 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 2 2 198243751576626402 198243751576626402 198243751576626402 endpoint_13_34_w0 endpoint_13_34_w2
private theorem endpoint_13_34_w4 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 4 2 198243751576626402 = some 198243751576626402 := by decide +kernel
private theorem endpoint_13_34_p6 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 6 198243751576626402 = some 198243751576626402 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 4 2 198243751576626402 198243751576626402 198243751576626402 endpoint_13_34_p4 endpoint_13_34_w4
private theorem endpoint_13_34_w6 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 6 2 198243751576626402 = some 198243751576626402 := by decide +kernel
private theorem endpoint_13_34_p8 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 8 198243751576626402 = some 198243751576626402 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 6 2 198243751576626402 198243751576626402 198243751576626402 endpoint_13_34_p6 endpoint_13_34_w6
private theorem endpoint_13_34_w8 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 8 2 198243751576626402 = some 198243751576626402 := by decide +kernel
private theorem endpoint_13_34_p10 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 10 198243751576626402 = some 198243751576626402 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 8 2 198243751576626402 198243751576626402 198243751576626402 endpoint_13_34_p8 endpoint_13_34_w8
private theorem endpoint_13_34_w10 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 10 2 198243751576626402 = some 198243751576626402 := by decide +kernel
private theorem endpoint_13_34_p12 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 12 198243751576626402 = some 198243751576626402 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 10 2 198243751576626402 198243751576626402 198243751576626402 endpoint_13_34_p10 endpoint_13_34_w10
def endpoint_13_34 : CertifiedEndpoint :=
  ⟨⟨13, 34, 3656⟩, 198243751576626402, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_34_flag endpoint_13_34_sources 12 198243751576626402 198243751576626402 rfl endpoint_13_34_base endpoint_13_34_p12) (by decide)⟩
private def endpoint_13_35_flag : Flag := ⟨13, 35, 3631⟩
private def endpoint_13_35_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_35_base : receiptBase endpoint_13_35_flag endpoint_13_35_sources = some 202358973302651392 := by decide +kernel
private theorem endpoint_13_35_w0 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 2 202358973302651392 = some 202358973302651392 := by decide +kernel
private theorem endpoint_13_35_w2 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 2 2 202358973302651392 = some 202358973302651392 := by decide +kernel
private theorem endpoint_13_35_p4 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 4 202358973302651392 = some 202358973302651392 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 2 2 202358973302651392 202358973302651392 202358973302651392 endpoint_13_35_w0 endpoint_13_35_w2
private theorem endpoint_13_35_w4 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 4 2 202358973302651392 = some 202358973302651392 := by decide +kernel
private theorem endpoint_13_35_p6 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 6 202358973302651392 = some 202358973302651392 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 4 2 202358973302651392 202358973302651392 202358973302651392 endpoint_13_35_p4 endpoint_13_35_w4
private theorem endpoint_13_35_w6 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 6 2 202358973302651392 = some 202358973302651392 := by decide +kernel
private theorem endpoint_13_35_p8 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 8 202358973302651392 = some 202358973302651392 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 6 2 202358973302651392 202358973302651392 202358973302651392 endpoint_13_35_p6 endpoint_13_35_w6
private theorem endpoint_13_35_w8 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 8 2 202358973302651392 = some 202358973302651392 := by decide +kernel
private theorem endpoint_13_35_p10 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 10 202358973302651392 = some 202358973302651392 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 8 2 202358973302651392 202358973302651392 202358973302651392 endpoint_13_35_p8 endpoint_13_35_w8
private theorem endpoint_13_35_w10 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 10 2 202358973302651392 = some 202358973302651392 := by decide +kernel
private theorem endpoint_13_35_p12 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 12 202358973302651392 = some 202358973302651392 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 10 2 202358973302651392 202358973302651392 202358973302651392 endpoint_13_35_p10 endpoint_13_35_w10
def endpoint_13_35 : CertifiedEndpoint :=
  ⟨⟨13, 35, 3631⟩, 202358973302651392, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_35_flag endpoint_13_35_sources 12 202358973302651392 202358973302651392 rfl endpoint_13_35_base endpoint_13_35_p12) (by decide)⟩
private def endpoint_13_36_flag : Flag := ⟨13, 36, 3605⟩
private def endpoint_13_36_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_36_base : receiptBase endpoint_13_36_flag endpoint_13_36_sources = some 205658241376514413 := by decide +kernel
private theorem endpoint_13_36_w0 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 2 205658241376514413 = some 205658241376514413 := by decide +kernel
private theorem endpoint_13_36_w2 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 2 2 205658241376514413 = some 205658241376514413 := by decide +kernel
private theorem endpoint_13_36_p4 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 4 205658241376514413 = some 205658241376514413 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 2 2 205658241376514413 205658241376514413 205658241376514413 endpoint_13_36_w0 endpoint_13_36_w2
private theorem endpoint_13_36_w4 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 4 2 205658241376514413 = some 205658241376514413 := by decide +kernel
private theorem endpoint_13_36_p6 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 6 205658241376514413 = some 205658241376514413 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 4 2 205658241376514413 205658241376514413 205658241376514413 endpoint_13_36_p4 endpoint_13_36_w4
private theorem endpoint_13_36_w6 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 6 2 205658241376514413 = some 205658241376514413 := by decide +kernel
private theorem endpoint_13_36_p8 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 8 205658241376514413 = some 205658241376514413 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 6 2 205658241376514413 205658241376514413 205658241376514413 endpoint_13_36_p6 endpoint_13_36_w6
private theorem endpoint_13_36_w8 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 8 2 205658241376514413 = some 205658241376514413 := by decide +kernel
private theorem endpoint_13_36_p10 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 10 205658241376514413 = some 205658241376514413 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 8 2 205658241376514413 205658241376514413 205658241376514413 endpoint_13_36_p8 endpoint_13_36_w8
private theorem endpoint_13_36_w10 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 10 2 205658241376514413 = some 205658241376514413 := by decide +kernel
private theorem endpoint_13_36_p12 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 12 205658241376514413 = some 205658241376514413 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 10 2 205658241376514413 205658241376514413 205658241376514413 endpoint_13_36_p10 endpoint_13_36_w10
def endpoint_13_36 : CertifiedEndpoint :=
  ⟨⟨13, 36, 3605⟩, 205658241376514413, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_36_flag endpoint_13_36_sources 12 205658241376514413 205658241376514413 rfl endpoint_13_36_base endpoint_13_36_p12) (by decide)⟩
private def endpoint_13_37_flag : Flag := ⟨13, 37, 3579⟩
private def endpoint_13_37_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_37_base : receiptBase endpoint_13_37_flag endpoint_13_37_sources = some 208889384011425014 := by decide +kernel
private theorem endpoint_13_37_w0 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 2 208889384011425014 = some 208889384011425014 := by decide +kernel
private theorem endpoint_13_37_w2 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 2 2 208889384011425014 = some 208889384011425014 := by decide +kernel
private theorem endpoint_13_37_p4 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 4 208889384011425014 = some 208889384011425014 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 2 2 208889384011425014 208889384011425014 208889384011425014 endpoint_13_37_w0 endpoint_13_37_w2
private theorem endpoint_13_37_w4 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 4 2 208889384011425014 = some 208889384011425014 := by decide +kernel
private theorem endpoint_13_37_p6 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 6 208889384011425014 = some 208889384011425014 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 4 2 208889384011425014 208889384011425014 208889384011425014 endpoint_13_37_p4 endpoint_13_37_w4
private theorem endpoint_13_37_w6 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 6 2 208889384011425014 = some 208889384011425014 := by decide +kernel
private theorem endpoint_13_37_p8 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 8 208889384011425014 = some 208889384011425014 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 6 2 208889384011425014 208889384011425014 208889384011425014 endpoint_13_37_p6 endpoint_13_37_w6
private theorem endpoint_13_37_w8 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 8 2 208889384011425014 = some 208889384011425014 := by decide +kernel
private theorem endpoint_13_37_p10 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 10 208889384011425014 = some 208889384011425014 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 8 2 208889384011425014 208889384011425014 208889384011425014 endpoint_13_37_p8 endpoint_13_37_w8
private theorem endpoint_13_37_w10 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 10 2 208889384011425014 = some 208889384011425014 := by decide +kernel
private theorem endpoint_13_37_p12 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 12 208889384011425014 = some 208889384011425014 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 10 2 208889384011425014 208889384011425014 208889384011425014 endpoint_13_37_p10 endpoint_13_37_w10
def endpoint_13_37 : CertifiedEndpoint :=
  ⟨⟨13, 37, 3579⟩, 208889384011425014, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_37_flag endpoint_13_37_sources 12 208889384011425014 208889384011425014 rfl endpoint_13_37_base endpoint_13_37_p12) (by decide)⟩
private def endpoint_13_38_flag : Flag := ⟨13, 38, 3552⟩
private def endpoint_13_38_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_38_base : receiptBase endpoint_13_38_flag endpoint_13_38_sources = some 211993620078219888 := by decide +kernel
private theorem endpoint_13_38_w0 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 2 211993620078219888 = some 211993620078219888 := by decide +kernel
private theorem endpoint_13_38_w2 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 2 2 211993620078219888 = some 211993620078219888 := by decide +kernel
private theorem endpoint_13_38_p4 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 4 211993620078219888 = some 211993620078219888 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 2 2 211993620078219888 211993620078219888 211993620078219888 endpoint_13_38_w0 endpoint_13_38_w2
private theorem endpoint_13_38_w4 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 4 2 211993620078219888 = some 211993620078219888 := by decide +kernel
private theorem endpoint_13_38_p6 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 6 211993620078219888 = some 211993620078219888 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 4 2 211993620078219888 211993620078219888 211993620078219888 endpoint_13_38_p4 endpoint_13_38_w4
private theorem endpoint_13_38_w6 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 6 2 211993620078219888 = some 211993620078219888 := by decide +kernel
private theorem endpoint_13_38_p8 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 8 211993620078219888 = some 211993620078219888 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 6 2 211993620078219888 211993620078219888 211993620078219888 endpoint_13_38_p6 endpoint_13_38_w6
private theorem endpoint_13_38_w8 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 8 2 211993620078219888 = some 211993620078219888 := by decide +kernel
private theorem endpoint_13_38_p10 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 10 211993620078219888 = some 211993620078219888 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 8 2 211993620078219888 211993620078219888 211993620078219888 endpoint_13_38_p8 endpoint_13_38_w8
private theorem endpoint_13_38_w10 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 10 2 211993620078219888 = some 211993620078219888 := by decide +kernel
private theorem endpoint_13_38_p12 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 12 211993620078219888 = some 211993620078219888 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 10 2 211993620078219888 211993620078219888 211993620078219888 endpoint_13_38_p10 endpoint_13_38_w10
def endpoint_13_38 : CertifiedEndpoint :=
  ⟨⟨13, 38, 3552⟩, 211993620078219888, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_38_flag endpoint_13_38_sources 12 211993620078219888 211993620078219888 rfl endpoint_13_38_base endpoint_13_38_p12) (by decide)⟩
private def endpoint_13_39_flag : Flag := ⟨13, 39, 3525⟩
private def endpoint_13_39_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_39_base : receiptBase endpoint_13_39_flag endpoint_13_39_sources = some 215027159934781118 := by decide +kernel
private theorem endpoint_13_39_w0 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 2 215027159934781118 = some 215027159934781118 := by decide +kernel
private theorem endpoint_13_39_w2 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 2 2 215027159934781118 = some 215027159934781118 := by decide +kernel
private theorem endpoint_13_39_p4 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 4 215027159934781118 = some 215027159934781118 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 2 2 215027159934781118 215027159934781118 215027159934781118 endpoint_13_39_w0 endpoint_13_39_w2
private theorem endpoint_13_39_w4 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 4 2 215027159934781118 = some 215027159934781118 := by decide +kernel
private theorem endpoint_13_39_p6 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 6 215027159934781118 = some 215027159934781118 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 4 2 215027159934781118 215027159934781118 215027159934781118 endpoint_13_39_p4 endpoint_13_39_w4
private theorem endpoint_13_39_w6 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 6 2 215027159934781118 = some 215027159934781118 := by decide +kernel
private theorem endpoint_13_39_p8 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 8 215027159934781118 = some 215027159934781118 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 6 2 215027159934781118 215027159934781118 215027159934781118 endpoint_13_39_p6 endpoint_13_39_w6
private theorem endpoint_13_39_w8 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 8 2 215027159934781118 = some 215027159934781118 := by decide +kernel
private theorem endpoint_13_39_p10 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 10 215027159934781118 = some 215027159934781118 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 8 2 215027159934781118 215027159934781118 215027159934781118 endpoint_13_39_p8 endpoint_13_39_w8
private theorem endpoint_13_39_w10 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 10 2 215027159934781118 = some 215027159934781118 := by decide +kernel
private theorem endpoint_13_39_p12 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 12 215027159934781118 = some 215027159934781118 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 10 2 215027159934781118 215027159934781118 215027159934781118 endpoint_13_39_p10 endpoint_13_39_w10
def endpoint_13_39 : CertifiedEndpoint :=
  ⟨⟨13, 39, 3525⟩, 215027159934781118, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_39_flag endpoint_13_39_sources 12 215027159934781118 215027159934781118 rfl endpoint_13_39_base endpoint_13_39_p12) (by decide)⟩
private def endpoint_13_40_flag : Flag := ⟨13, 40, 3497⟩
private def endpoint_13_40_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_40_base : receiptBase endpoint_13_40_flag endpoint_13_40_sources = some 218348677716979196 := by decide +kernel
private theorem endpoint_13_40_w0 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 2 218348677716979196 = some 218348677716979196 := by decide +kernel
private theorem endpoint_13_40_w2 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 2 2 218348677716979196 = some 218348677716979196 := by decide +kernel
private theorem endpoint_13_40_p4 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 4 218348677716979196 = some 218348677716979196 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 2 2 218348677716979196 218348677716979196 218348677716979196 endpoint_13_40_w0 endpoint_13_40_w2
private theorem endpoint_13_40_w4 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 4 2 218348677716979196 = some 218348677716979196 := by decide +kernel
private theorem endpoint_13_40_p6 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 6 218348677716979196 = some 218348677716979196 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 4 2 218348677716979196 218348677716979196 218348677716979196 endpoint_13_40_p4 endpoint_13_40_w4
private theorem endpoint_13_40_w6 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 6 2 218348677716979196 = some 218348677716979196 := by decide +kernel
private theorem endpoint_13_40_p8 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 8 218348677716979196 = some 218348677716979196 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 6 2 218348677716979196 218348677716979196 218348677716979196 endpoint_13_40_p6 endpoint_13_40_w6
private theorem endpoint_13_40_w8 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 8 2 218348677716979196 = some 218348677716979196 := by decide +kernel
private theorem endpoint_13_40_p10 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 10 218348677716979196 = some 218348677716979196 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 8 2 218348677716979196 218348677716979196 218348677716979196 endpoint_13_40_p8 endpoint_13_40_w8
private theorem endpoint_13_40_w10 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 10 2 218348677716979196 = some 218348677716979196 := by decide +kernel
private theorem endpoint_13_40_p12 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 12 218348677716979196 = some 218348677716979196 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 10 2 218348677716979196 218348677716979196 218348677716979196 endpoint_13_40_p10 endpoint_13_40_w10
def endpoint_13_40 : CertifiedEndpoint :=
  ⟨⟨13, 40, 3497⟩, 218348677716979196, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_40_flag endpoint_13_40_sources 12 218348677716979196 218348677716979196 rfl endpoint_13_40_base endpoint_13_40_p12) (by decide)⟩
private def endpoint_13_41_flag : Flag := ⟨13, 41, 3469⟩
private def endpoint_13_41_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_41_base : receiptBase endpoint_13_41_flag endpoint_13_41_sources = some 221188804950627098 := by decide +kernel
private theorem endpoint_13_41_w0 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 2 221188804950627098 = some 221188804950627098 := by decide +kernel
private theorem endpoint_13_41_w2 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 2 2 221188804950627098 = some 221188804950627098 := by decide +kernel
private theorem endpoint_13_41_p4 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 4 221188804950627098 = some 221188804950627098 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 2 2 221188804950627098 221188804950627098 221188804950627098 endpoint_13_41_w0 endpoint_13_41_w2
private theorem endpoint_13_41_w4 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 4 2 221188804950627098 = some 221188804950627098 := by decide +kernel
private theorem endpoint_13_41_p6 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 6 221188804950627098 = some 221188804950627098 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 4 2 221188804950627098 221188804950627098 221188804950627098 endpoint_13_41_p4 endpoint_13_41_w4
private theorem endpoint_13_41_w6 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 6 2 221188804950627098 = some 221188804950627098 := by decide +kernel
private theorem endpoint_13_41_p8 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 8 221188804950627098 = some 221188804950627098 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 6 2 221188804950627098 221188804950627098 221188804950627098 endpoint_13_41_p6 endpoint_13_41_w6
private theorem endpoint_13_41_w8 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 8 2 221188804950627098 = some 221188804950627098 := by decide +kernel
private theorem endpoint_13_41_p10 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 10 221188804950627098 = some 221188804950627098 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 8 2 221188804950627098 221188804950627098 221188804950627098 endpoint_13_41_p8 endpoint_13_41_w8
private theorem endpoint_13_41_w10 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 10 2 221188804950627098 = some 221188804950627098 := by decide +kernel
private theorem endpoint_13_41_p12 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 12 221188804950627098 = some 221188804950627098 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 10 2 221188804950627098 221188804950627098 221188804950627098 endpoint_13_41_p10 endpoint_13_41_w10
def endpoint_13_41 : CertifiedEndpoint :=
  ⟨⟨13, 41, 3469⟩, 221188804950627098, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_41_flag endpoint_13_41_sources 12 221188804950627098 221188804950627098 rfl endpoint_13_41_base endpoint_13_41_p12) (by decide)⟩
private def endpoint_13_42_flag : Flag := ⟨13, 42, 3441⟩
private def endpoint_13_42_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_42_base : receiptBase endpoint_13_42_flag endpoint_13_42_sources = some 223955404182377801 := by decide +kernel
private theorem endpoint_13_42_w0 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 2 223955404182377801 = some 223955404182377801 := by decide +kernel
private theorem endpoint_13_42_w2 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 2 2 223955404182377801 = some 223955404182377801 := by decide +kernel
private theorem endpoint_13_42_p4 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 4 223955404182377801 = some 223955404182377801 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 2 2 223955404182377801 223955404182377801 223955404182377801 endpoint_13_42_w0 endpoint_13_42_w2
private theorem endpoint_13_42_w4 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 4 2 223955404182377801 = some 223955404182377801 := by decide +kernel
private theorem endpoint_13_42_p6 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 6 223955404182377801 = some 223955404182377801 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 4 2 223955404182377801 223955404182377801 223955404182377801 endpoint_13_42_p4 endpoint_13_42_w4
private theorem endpoint_13_42_w6 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 6 2 223955404182377801 = some 223955404182377801 := by decide +kernel
private theorem endpoint_13_42_p8 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 8 223955404182377801 = some 223955404182377801 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 6 2 223955404182377801 223955404182377801 223955404182377801 endpoint_13_42_p6 endpoint_13_42_w6
private theorem endpoint_13_42_w8 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 8 2 223955404182377801 = some 223955404182377801 := by decide +kernel
private theorem endpoint_13_42_p10 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 10 223955404182377801 = some 223955404182377801 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 8 2 223955404182377801 223955404182377801 223955404182377801 endpoint_13_42_p8 endpoint_13_42_w8
private theorem endpoint_13_42_w10 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 10 2 223955404182377801 = some 223955404182377801 := by decide +kernel
private theorem endpoint_13_42_p12 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 12 223955404182377801 = some 223955404182377801 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 10 2 223955404182377801 223955404182377801 223955404182377801 endpoint_13_42_p10 endpoint_13_42_w10
def endpoint_13_42 : CertifiedEndpoint :=
  ⟨⟨13, 42, 3441⟩, 223955404182377801, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_42_flag endpoint_13_42_sources 12 223955404182377801 223955404182377801 rfl endpoint_13_42_base endpoint_13_42_p12) (by decide)⟩
private def endpoint_13_43_flag : Flag := ⟨13, 43, 3412⟩
private def endpoint_13_43_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_43_base : receiptBase endpoint_13_43_flag endpoint_13_43_sources = some 226583132343929510 := by decide +kernel
private theorem endpoint_13_43_w0 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 2 226583132343929510 = some 226583132343929510 := by decide +kernel
private theorem endpoint_13_43_w2 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 2 2 226583132343929510 = some 226583132343929510 := by decide +kernel
private theorem endpoint_13_43_p4 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 4 226583132343929510 = some 226583132343929510 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 2 2 226583132343929510 226583132343929510 226583132343929510 endpoint_13_43_w0 endpoint_13_43_w2
private theorem endpoint_13_43_w4 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 4 2 226583132343929510 = some 226583132343929510 := by decide +kernel
private theorem endpoint_13_43_p6 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 6 226583132343929510 = some 226583132343929510 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 4 2 226583132343929510 226583132343929510 226583132343929510 endpoint_13_43_p4 endpoint_13_43_w4
private theorem endpoint_13_43_w6 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 6 2 226583132343929510 = some 226583132343929510 := by decide +kernel
private theorem endpoint_13_43_p8 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 8 226583132343929510 = some 226583132343929510 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 6 2 226583132343929510 226583132343929510 226583132343929510 endpoint_13_43_p6 endpoint_13_43_w6
private theorem endpoint_13_43_w8 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 8 2 226583132343929510 = some 226583132343929510 := by decide +kernel
private theorem endpoint_13_43_p10 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 10 226583132343929510 = some 226583132343929510 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 8 2 226583132343929510 226583132343929510 226583132343929510 endpoint_13_43_p8 endpoint_13_43_w8
private theorem endpoint_13_43_w10 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 10 2 226583132343929510 = some 226583132343929510 := by decide +kernel
private theorem endpoint_13_43_p12 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 12 226583132343929510 = some 226583132343929510 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 10 2 226583132343929510 226583132343929510 226583132343929510 endpoint_13_43_p10 endpoint_13_43_w10
def endpoint_13_43 : CertifiedEndpoint :=
  ⟨⟨13, 43, 3412⟩, 226583132343929510, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_43_flag endpoint_13_43_sources 12 226583132343929510 226583132343929510 rfl endpoint_13_43_base endpoint_13_43_p12) (by decide)⟩
private def endpoint_13_44_flag : Flag := ⟨13, 44, 3382⟩
private def endpoint_13_44_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_44_base : receiptBase endpoint_13_44_flag endpoint_13_44_sources = some 229068119777266846 := by decide +kernel
private theorem endpoint_13_44_w0 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 2 229068119777266846 = some 229529161681568048 := by decide +kernel
private theorem endpoint_13_44_w2 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 2 2 229529161681568048 = some 229529161681568048 := by decide +kernel
private theorem endpoint_13_44_p4 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 4 229068119777266846 = some 229529161681568048 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 2 2 229068119777266846 229529161681568048 229529161681568048 endpoint_13_44_w0 endpoint_13_44_w2
private theorem endpoint_13_44_w4 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 4 2 229529161681568048 = some 229529161681568048 := by decide +kernel
private theorem endpoint_13_44_p6 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 6 229068119777266846 = some 229529161681568048 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 4 2 229068119777266846 229529161681568048 229529161681568048 endpoint_13_44_p4 endpoint_13_44_w4
private theorem endpoint_13_44_w6 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 6 2 229529161681568048 = some 229529161681568048 := by decide +kernel
private theorem endpoint_13_44_p8 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 8 229068119777266846 = some 229529161681568048 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 6 2 229068119777266846 229529161681568048 229529161681568048 endpoint_13_44_p6 endpoint_13_44_w6
private theorem endpoint_13_44_w8 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 8 2 229529161681568048 = some 229529161681568048 := by decide +kernel
private theorem endpoint_13_44_p10 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 10 229068119777266846 = some 229529161681568048 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 8 2 229068119777266846 229529161681568048 229529161681568048 endpoint_13_44_p8 endpoint_13_44_w8
private theorem endpoint_13_44_w10 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 10 2 229529161681568048 = some 229529161681568048 := by decide +kernel
private theorem endpoint_13_44_p12 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 12 229068119777266846 = some 229529161681568048 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 10 2 229068119777266846 229529161681568048 229529161681568048 endpoint_13_44_p10 endpoint_13_44_w10
def endpoint_13_44 : CertifiedEndpoint :=
  ⟨⟨13, 44, 3382⟩, 229529161681568048, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_44_flag endpoint_13_44_sources 12 229068119777266846 229529161681568048 rfl endpoint_13_44_base endpoint_13_44_p12) (by decide)⟩
private def endpoint_13_45_flag : Flag := ⟨13, 45, 3352⟩
private def endpoint_13_45_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_45_base : receiptBase endpoint_13_45_flag endpoint_13_45_sources = some 231474419664686479 := by decide +kernel
private theorem endpoint_13_45_w0 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 2 231474419664686479 = some 234672625032760419 := by decide +kernel
private theorem endpoint_13_45_w2 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 2 2 234672625032760419 = some 234672625032760419 := by decide +kernel
private theorem endpoint_13_45_p4 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 4 231474419664686479 = some 234672625032760419 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 2 2 231474419664686479 234672625032760419 234672625032760419 endpoint_13_45_w0 endpoint_13_45_w2
private theorem endpoint_13_45_w4 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 4 2 234672625032760419 = some 234672625032760419 := by decide +kernel
private theorem endpoint_13_45_p6 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 6 231474419664686479 = some 234672625032760419 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 4 2 231474419664686479 234672625032760419 234672625032760419 endpoint_13_45_p4 endpoint_13_45_w4
private theorem endpoint_13_45_w6 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 6 2 234672625032760419 = some 234672625032760419 := by decide +kernel
private theorem endpoint_13_45_p8 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 8 231474419664686479 = some 234672625032760419 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 6 2 231474419664686479 234672625032760419 234672625032760419 endpoint_13_45_p6 endpoint_13_45_w6
private theorem endpoint_13_45_w8 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 8 2 234672625032760419 = some 234672625032760419 := by decide +kernel
private theorem endpoint_13_45_p10 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 10 231474419664686479 = some 234672625032760419 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 8 2 231474419664686479 234672625032760419 234672625032760419 endpoint_13_45_p8 endpoint_13_45_w8
private theorem endpoint_13_45_w10 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 10 2 234672625032760419 = some 234672625032760419 := by decide +kernel
private theorem endpoint_13_45_p12 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 12 231474419664686479 = some 234672625032760419 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 10 2 231474419664686479 234672625032760419 234672625032760419 endpoint_13_45_p10 endpoint_13_45_w10
def endpoint_13_45 : CertifiedEndpoint :=
  ⟨⟨13, 45, 3352⟩, 234672625032760419, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_45_flag endpoint_13_45_sources 12 231474419664686479 234672625032760419 rfl endpoint_13_45_base endpoint_13_45_p12) (by decide)⟩
private def endpoint_13_46_flag : Flag := ⟨13, 46, 3321⟩
private def endpoint_13_46_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_46_base : receiptBase endpoint_13_46_flag endpoint_13_46_sources = some 233732819279871236 := by decide +kernel
private theorem endpoint_13_46_w0 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 2 233732819279871236 = some 239717722537221346 := by decide +kernel
private theorem endpoint_13_46_w2 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 2 2 239717722537221346 = some 239717722537221346 := by decide +kernel
private theorem endpoint_13_46_p4 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 4 233732819279871236 = some 239717722537221346 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 2 2 233732819279871236 239717722537221346 239717722537221346 endpoint_13_46_w0 endpoint_13_46_w2
private theorem endpoint_13_46_w4 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 4 2 239717722537221346 = some 239717722537221346 := by decide +kernel
private theorem endpoint_13_46_p6 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 6 233732819279871236 = some 239717722537221346 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 4 2 233732819279871236 239717722537221346 239717722537221346 endpoint_13_46_p4 endpoint_13_46_w4
private theorem endpoint_13_46_w6 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 6 2 239717722537221346 = some 239717722537221346 := by decide +kernel
private theorem endpoint_13_46_p8 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 8 233732819279871236 = some 239717722537221346 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 6 2 233732819279871236 239717722537221346 239717722537221346 endpoint_13_46_p6 endpoint_13_46_w6
private theorem endpoint_13_46_w8 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 8 2 239717722537221346 = some 239717722537221346 := by decide +kernel
private theorem endpoint_13_46_p10 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 10 233732819279871236 = some 239717722537221346 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 8 2 233732819279871236 239717722537221346 239717722537221346 endpoint_13_46_p8 endpoint_13_46_w8
private theorem endpoint_13_46_w10 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 10 2 239717722537221346 = some 239717722537221346 := by decide +kernel
private theorem endpoint_13_46_p12 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 12 233732819279871236 = some 239717722537221346 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 10 2 233732819279871236 239717722537221346 239717722537221346 endpoint_13_46_p10 endpoint_13_46_w10
def endpoint_13_46 : CertifiedEndpoint :=
  ⟨⟨13, 46, 3321⟩, 239717722537221346, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_46_flag endpoint_13_46_sources 12 233732819279871236 239717722537221346 rfl endpoint_13_46_base endpoint_13_46_p12) (by decide)⟩

def endpointBlock08 : List CertifiedEndpoint := [
  endpoint_11_82, endpoint_11_83, endpoint_11_84, endpoint_11_85, endpoint_11_86, endpoint_11_87, endpoint_11_88,
  endpoint_11_89, endpoint_11_90, endpoint_11_91, endpoint_11_92, endpoint_11_93, endpoint_11_94, endpoint_11_95,
  endpoint_12_12, endpoint_12_13, endpoint_12_14, endpoint_12_15, endpoint_12_16, endpoint_12_17, endpoint_12_18,
  endpoint_12_19, endpoint_12_20, endpoint_12_21, endpoint_12_22, endpoint_12_23, endpoint_12_24, endpoint_12_25,
  endpoint_12_26, endpoint_12_27, endpoint_12_28, endpoint_12_29, endpoint_12_30, endpoint_12_31, endpoint_12_32,
  endpoint_12_33, endpoint_12_34, endpoint_12_35, endpoint_12_36, endpoint_12_37, endpoint_12_38, endpoint_12_39,
  endpoint_12_40, endpoint_12_41, endpoint_12_42, endpoint_12_43, endpoint_12_44, endpoint_12_45, endpoint_12_46,
  endpoint_12_47, endpoint_12_48, endpoint_12_49, endpoint_12_50, endpoint_12_51, endpoint_12_52, endpoint_12_53,
  endpoint_12_54, endpoint_12_55, endpoint_12_56, endpoint_12_57, endpoint_12_58, endpoint_12_59, endpoint_12_60,
  endpoint_12_61, endpoint_12_62, endpoint_12_63, endpoint_12_64, endpoint_12_65, endpoint_12_66, endpoint_12_67,
  endpoint_12_68, endpoint_12_69, endpoint_12_70, endpoint_12_71, endpoint_12_72, endpoint_12_73, endpoint_12_74,
  endpoint_12_75, endpoint_12_76, endpoint_12_77, endpoint_12_78, endpoint_12_79, endpoint_12_80, endpoint_12_81,
  endpoint_12_82, endpoint_12_83, endpoint_12_84, endpoint_12_85, endpoint_12_86, endpoint_12_87, endpoint_12_88,
  endpoint_12_89, endpoint_12_90, endpoint_12_91, endpoint_12_92, endpoint_12_93, endpoint_13_13, endpoint_13_14,
  endpoint_13_15, endpoint_13_16, endpoint_13_17, endpoint_13_18, endpoint_13_19, endpoint_13_20, endpoint_13_21,
  endpoint_13_22, endpoint_13_23, endpoint_13_24, endpoint_13_25, endpoint_13_26, endpoint_13_27, endpoint_13_28,
  endpoint_13_29, endpoint_13_30, endpoint_13_31, endpoint_13_32, endpoint_13_33, endpoint_13_34, endpoint_13_35,
  endpoint_13_36, endpoint_13_37, endpoint_13_38, endpoint_13_39, endpoint_13_40, endpoint_13_41, endpoint_13_42,
  endpoint_13_43, endpoint_13_44, endpoint_13_45, endpoint_13_46
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
