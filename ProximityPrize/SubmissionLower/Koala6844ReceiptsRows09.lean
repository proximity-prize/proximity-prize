import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


private def endpoint_13_78_flag : Flag := ⟨13, 78, 1307⟩
private def endpoint_13_78_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_13_78_base : receiptBase endpoint_13_78_flag endpoint_13_78_sources = some 162383748280926808 := by decide +kernel
private theorem endpoint_13_78_window_0 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 2 162383748280926808 = some 167198062088245782 := by decide +kernel
private theorem endpoint_13_78_window_2 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 2 2 167198062088245782 = some 167198062088245782 := by decide +kernel
private theorem endpoint_13_78_prefix_4 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 4 162383748280926808 = some 167198062088245782 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 2 2 162383748280926808 167198062088245782 167198062088245782 endpoint_13_78_window_0 endpoint_13_78_window_2
private theorem endpoint_13_78_window_4 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 4 2 167198062088245782 = some 167198062088245782 := by decide +kernel
private theorem endpoint_13_78_prefix_6 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 6 162383748280926808 = some 167198062088245782 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 4 2 162383748280926808 167198062088245782 167198062088245782 endpoint_13_78_prefix_4 endpoint_13_78_window_4
private theorem endpoint_13_78_window_6 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 6 2 167198062088245782 = some 167198062088245782 := by decide +kernel
private theorem endpoint_13_78_prefix_8 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 8 162383748280926808 = some 167198062088245782 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 6 2 162383748280926808 167198062088245782 167198062088245782 endpoint_13_78_prefix_6 endpoint_13_78_window_6
private theorem endpoint_13_78_window_8 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 8 2 167198062088245782 = some 167198062088245782 := by decide +kernel
private theorem endpoint_13_78_prefix_10 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 10 162383748280926808 = some 167198062088245782 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 8 2 162383748280926808 167198062088245782 167198062088245782 endpoint_13_78_prefix_8 endpoint_13_78_window_8
private theorem endpoint_13_78_window_10 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 10 2 167198062088245782 = some 167198062088245782 := by decide +kernel
private theorem endpoint_13_78_prefix_12 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 12 162383748280926808 = some 167198062088245782 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 10 2 162383748280926808 167198062088245782 167198062088245782 endpoint_13_78_prefix_10 endpoint_13_78_window_10

def endpoint_13_78 : CertifiedEndpoint :=
  ⟨⟨13, 78, 1307⟩, 167198062088245782, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_13_78_flag endpoint_13_78_sources 12 162383748280926808 167198062088245782 rfl endpoint_13_78_base endpoint_13_78_prefix_12) (by decide)⟩
private def endpoint_13_79_flag : Flag := ⟨13, 79, 1211⟩
private def endpoint_13_79_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_13_79_base : receiptBase endpoint_13_79_flag endpoint_13_79_sources = some 153186860703456603 := by decide +kernel
private theorem endpoint_13_79_window_0 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 2 153186860703456603 = some 155780745223612039 := by decide +kernel
private theorem endpoint_13_79_window_2 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 2 2 155780745223612039 = some 155780745223612039 := by decide +kernel
private theorem endpoint_13_79_prefix_4 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 4 153186860703456603 = some 155780745223612039 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 2 2 153186860703456603 155780745223612039 155780745223612039 endpoint_13_79_window_0 endpoint_13_79_window_2
private theorem endpoint_13_79_window_4 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 4 2 155780745223612039 = some 155780745223612039 := by decide +kernel
private theorem endpoint_13_79_prefix_6 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 6 153186860703456603 = some 155780745223612039 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 4 2 153186860703456603 155780745223612039 155780745223612039 endpoint_13_79_prefix_4 endpoint_13_79_window_4
private theorem endpoint_13_79_window_6 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 6 2 155780745223612039 = some 155780745223612039 := by decide +kernel
private theorem endpoint_13_79_prefix_8 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 8 153186860703456603 = some 155780745223612039 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 6 2 153186860703456603 155780745223612039 155780745223612039 endpoint_13_79_prefix_6 endpoint_13_79_window_6
private theorem endpoint_13_79_window_8 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 8 2 155780745223612039 = some 155780745223612039 := by decide +kernel
private theorem endpoint_13_79_prefix_10 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 10 153186860703456603 = some 155780745223612039 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 8 2 153186860703456603 155780745223612039 155780745223612039 endpoint_13_79_prefix_8 endpoint_13_79_window_8
private theorem endpoint_13_79_window_10 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 10 2 155780745223612039 = some 155780745223612039 := by decide +kernel
private theorem endpoint_13_79_prefix_12 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 12 153186860703456603 = some 155780745223612039 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 10 2 153186860703456603 155780745223612039 155780745223612039 endpoint_13_79_prefix_10 endpoint_13_79_window_10

def endpoint_13_79 : CertifiedEndpoint :=
  ⟨⟨13, 79, 1211⟩, 155780745223612039, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_13_79_flag endpoint_13_79_sources 12 153186860703456603 155780745223612039 rfl endpoint_13_79_base endpoint_13_79_prefix_12) (by decide)⟩
def endpoint_13_80 : CertifiedEndpoint :=
  ⟨⟨13, 80, 1113⟩, 252199924767076113, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_81 : CertifiedEndpoint :=
  ⟨⟨13, 81, 1013⟩, 231632699252253458, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_82 : CertifiedEndpoint :=
  ⟨⟨13, 82, 909⟩, 209447261328011877, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_83 : CertifiedEndpoint :=
  ⟨⟨13, 83, 803⟩, 186095813689254600, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_84 : CertifiedEndpoint :=
  ⟨⟨13, 84, 695⟩, 161558976959883551, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_85 : CertifiedEndpoint :=
  ⟨⟨13, 85, 583⟩, 135313490732635888, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_86 : CertifiedEndpoint :=
  ⟨⟨13, 86, 469⟩, 107830937078512917, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_87 : CertifiedEndpoint :=
  ⟨⟨13, 87, 353⟩, 79091936621416562, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_88 : CertifiedEndpoint :=
  ⟨⟨13, 88, 233⟩, 48553849577985905, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_89 : CertifiedEndpoint :=
  ⟨⟨13, 89, 111⟩, 16707637395320328, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_14 : CertifiedEndpoint :=
  ⟨⟨14, 14, 3844⟩, 104918298482045948, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_15 : CertifiedEndpoint :=
  ⟨⟨14, 15, 3823⟩, 108693024892813016, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_16 : CertifiedEndpoint :=
  ⟨⟨14, 16, 3802⟩, 112419766720589222, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_17 : CertifiedEndpoint :=
  ⟨⟨14, 17, 3781⟩, 124926120348268822, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_18 : CertifiedEndpoint :=
  ⟨⟨14, 18, 3759⟩, 137245878728333461, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_19 : CertifiedEndpoint :=
  ⟨⟨14, 19, 3737⟩, 149408695092846190, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_20 : CertifiedEndpoint :=
  ⟨⟨14, 20, 3715⟩, 161414569441807009, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_21 : CertifiedEndpoint :=
  ⟨⟨14, 21, 3693⟩, 173263501775215918, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_22 : CertifiedEndpoint :=
  ⟨⟨14, 22, 3670⟩, 184904913258936278, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_23 : CertifiedEndpoint :=
  ⟨⟨14, 23, 3647⟩, 196382407526413532, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_24 : CertifiedEndpoint :=
  ⟨⟨14, 24, 3624⟩, 207695984577647680, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_25 : CertifiedEndpoint :=
  ⟨⟨14, 25, 3600⟩, 218784602777465289, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_26 : CertifiedEndpoint :=
  ⟨⟨14, 26, 3576⟩, 229702328560348596, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_27 : CertifiedEndpoint :=
  ⟨⟨14, 27, 3552⟩, 240449161926297601, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_28 : CertifiedEndpoint :=
  ⟨⟨14, 28, 3527⟩, 250953598439102077, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_14_29_flag : Flag := ⟨14, 29, 3502⟩
private def endpoint_14_29_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_29_base : receiptBase endpoint_14_29_flag endpoint_14_29_sources = some 174632930686471590 := by decide +kernel
private theorem endpoint_14_29_window_0 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 2 174632930686471590 = some 174632930686471590 := by decide +kernel
private theorem endpoint_14_29_window_2 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 2 2 174632930686471590 = some 174632930686471590 := by decide +kernel
private theorem endpoint_14_29_prefix_4 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 4 174632930686471590 = some 174632930686471590 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 2 2 174632930686471590 174632930686471590 174632930686471590 endpoint_14_29_window_0 endpoint_14_29_window_2
private theorem endpoint_14_29_window_4 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 4 2 174632930686471590 = some 174632930686471590 := by decide +kernel
private theorem endpoint_14_29_prefix_6 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 6 174632930686471590 = some 174632930686471590 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 4 2 174632930686471590 174632930686471590 174632930686471590 endpoint_14_29_prefix_4 endpoint_14_29_window_4
private theorem endpoint_14_29_window_6 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 6 2 174632930686471590 = some 174632930686471590 := by decide +kernel
private theorem endpoint_14_29_prefix_8 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 8 174632930686471590 = some 174632930686471590 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 6 2 174632930686471590 174632930686471590 174632930686471590 endpoint_14_29_prefix_6 endpoint_14_29_window_6
private theorem endpoint_14_29_window_8 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 8 2 174632930686471590 = some 174632930686471590 := by decide +kernel
private theorem endpoint_14_29_prefix_10 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 10 174632930686471590 = some 174632930686471590 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 8 2 174632930686471590 174632930686471590 174632930686471590 endpoint_14_29_prefix_8 endpoint_14_29_window_8
private theorem endpoint_14_29_window_10 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 10 2 174632930686471590 = some 174632930686471590 := by decide +kernel
private theorem endpoint_14_29_prefix_12 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 12 174632930686471590 = some 174632930686471590 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 10 2 174632930686471590 174632930686471590 174632930686471590 endpoint_14_29_prefix_10 endpoint_14_29_window_10
private theorem endpoint_14_29_window_12 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 12 1 174632930686471590 = some 174632930686471590 := by decide +kernel
private theorem endpoint_14_29_prefix_13 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 13 174632930686471590 = some 174632930686471590 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 12 1 174632930686471590 174632930686471590 174632930686471590 endpoint_14_29_prefix_12 endpoint_14_29_window_12

def endpoint_14_29 : CertifiedEndpoint :=
  ⟨⟨14, 29, 3502⟩, 174632930686471590, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_29_flag endpoint_14_29_sources 13 174632930686471590 174632930686471590 rfl endpoint_14_29_base endpoint_14_29_prefix_13) (by decide)⟩
private def endpoint_14_30_flag : Flag := ⟨14, 30, 3477⟩
private def endpoint_14_30_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_30_base : receiptBase endpoint_14_30_flag endpoint_14_30_sources = some 178302716519835666 := by decide +kernel
private theorem endpoint_14_30_window_0 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 2 178302716519835666 = some 178302716519835666 := by decide +kernel
private theorem endpoint_14_30_window_2 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 2 2 178302716519835666 = some 178302716519835666 := by decide +kernel
private theorem endpoint_14_30_prefix_4 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 4 178302716519835666 = some 178302716519835666 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 2 2 178302716519835666 178302716519835666 178302716519835666 endpoint_14_30_window_0 endpoint_14_30_window_2
private theorem endpoint_14_30_window_4 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 4 2 178302716519835666 = some 178302716519835666 := by decide +kernel
private theorem endpoint_14_30_prefix_6 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 6 178302716519835666 = some 178302716519835666 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 4 2 178302716519835666 178302716519835666 178302716519835666 endpoint_14_30_prefix_4 endpoint_14_30_window_4
private theorem endpoint_14_30_window_6 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 6 2 178302716519835666 = some 178302716519835666 := by decide +kernel
private theorem endpoint_14_30_prefix_8 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 8 178302716519835666 = some 178302716519835666 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 6 2 178302716519835666 178302716519835666 178302716519835666 endpoint_14_30_prefix_6 endpoint_14_30_window_6
private theorem endpoint_14_30_window_8 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 8 2 178302716519835666 = some 178302716519835666 := by decide +kernel
private theorem endpoint_14_30_prefix_10 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 10 178302716519835666 = some 178302716519835666 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 8 2 178302716519835666 178302716519835666 178302716519835666 endpoint_14_30_prefix_8 endpoint_14_30_window_8
private theorem endpoint_14_30_window_10 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 10 2 178302716519835666 = some 178302716519835666 := by decide +kernel
private theorem endpoint_14_30_prefix_12 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 12 178302716519835666 = some 178302716519835666 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 10 2 178302716519835666 178302716519835666 178302716519835666 endpoint_14_30_prefix_10 endpoint_14_30_window_10
private theorem endpoint_14_30_window_12 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 12 1 178302716519835666 = some 178302716519835666 := by decide +kernel
private theorem endpoint_14_30_prefix_13 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 13 178302716519835666 = some 178302716519835666 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 12 1 178302716519835666 178302716519835666 178302716519835666 endpoint_14_30_prefix_12 endpoint_14_30_window_12

def endpoint_14_30 : CertifiedEndpoint :=
  ⟨⟨14, 30, 3477⟩, 178302716519835666, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_30_flag endpoint_14_30_sources 13 178302716519835666 178302716519835666 rfl endpoint_14_30_base endpoint_14_30_prefix_13) (by decide)⟩
private def endpoint_14_31_flag : Flag := ⟨14, 31, 3451⟩
private def endpoint_14_31_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_31_base : receiptBase endpoint_14_31_flag endpoint_14_31_sources = some 181850551015300192 := by decide +kernel
private theorem endpoint_14_31_window_0 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 2 181850551015300192 = some 181850551015300192 := by decide +kernel
private theorem endpoint_14_31_window_2 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 2 2 181850551015300192 = some 181850551015300192 := by decide +kernel
private theorem endpoint_14_31_prefix_4 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 4 181850551015300192 = some 181850551015300192 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 2 2 181850551015300192 181850551015300192 181850551015300192 endpoint_14_31_window_0 endpoint_14_31_window_2
private theorem endpoint_14_31_window_4 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 4 2 181850551015300192 = some 181850551015300192 := by decide +kernel
private theorem endpoint_14_31_prefix_6 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 6 181850551015300192 = some 181850551015300192 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 4 2 181850551015300192 181850551015300192 181850551015300192 endpoint_14_31_prefix_4 endpoint_14_31_window_4
private theorem endpoint_14_31_window_6 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 6 2 181850551015300192 = some 181850551015300192 := by decide +kernel
private theorem endpoint_14_31_prefix_8 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 8 181850551015300192 = some 181850551015300192 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 6 2 181850551015300192 181850551015300192 181850551015300192 endpoint_14_31_prefix_6 endpoint_14_31_window_6
private theorem endpoint_14_31_window_8 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 8 2 181850551015300192 = some 181850551015300192 := by decide +kernel
private theorem endpoint_14_31_prefix_10 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 10 181850551015300192 = some 181850551015300192 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 8 2 181850551015300192 181850551015300192 181850551015300192 endpoint_14_31_prefix_8 endpoint_14_31_window_8
private theorem endpoint_14_31_window_10 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 10 2 181850551015300192 = some 181850551015300192 := by decide +kernel
private theorem endpoint_14_31_prefix_12 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 12 181850551015300192 = some 181850551015300192 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 10 2 181850551015300192 181850551015300192 181850551015300192 endpoint_14_31_prefix_10 endpoint_14_31_window_10
private theorem endpoint_14_31_window_12 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 12 1 181850551015300192 = some 181850551015300192 := by decide +kernel
private theorem endpoint_14_31_prefix_13 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 13 181850551015300192 = some 181850551015300192 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 12 1 181850551015300192 181850551015300192 181850551015300192 endpoint_14_31_prefix_12 endpoint_14_31_window_12

def endpoint_14_31 : CertifiedEndpoint :=
  ⟨⟨14, 31, 3451⟩, 181850551015300192, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_31_flag endpoint_14_31_sources 13 181850551015300192 181850551015300192 rfl endpoint_14_31_base endpoint_14_31_prefix_13) (by decide)⟩
private def endpoint_14_32_flag : Flag := ⟨14, 32, 3425⟩
private def endpoint_14_32_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_32_base : receiptBase endpoint_14_32_flag endpoint_14_32_sources = some 185325524198264863 := by decide +kernel
private theorem endpoint_14_32_window_0 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 2 185325524198264863 = some 185325524198264863 := by decide +kernel
private theorem endpoint_14_32_window_2 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 2 2 185325524198264863 = some 185325524198264863 := by decide +kernel
private theorem endpoint_14_32_prefix_4 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 4 185325524198264863 = some 185325524198264863 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 2 2 185325524198264863 185325524198264863 185325524198264863 endpoint_14_32_window_0 endpoint_14_32_window_2
private theorem endpoint_14_32_window_4 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 4 2 185325524198264863 = some 185325524198264863 := by decide +kernel
private theorem endpoint_14_32_prefix_6 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 6 185325524198264863 = some 185325524198264863 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 4 2 185325524198264863 185325524198264863 185325524198264863 endpoint_14_32_prefix_4 endpoint_14_32_window_4
private theorem endpoint_14_32_window_6 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 6 2 185325524198264863 = some 185325524198264863 := by decide +kernel
private theorem endpoint_14_32_prefix_8 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 8 185325524198264863 = some 185325524198264863 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 6 2 185325524198264863 185325524198264863 185325524198264863 endpoint_14_32_prefix_6 endpoint_14_32_window_6
private theorem endpoint_14_32_window_8 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 8 2 185325524198264863 = some 185325524198264863 := by decide +kernel
private theorem endpoint_14_32_prefix_10 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 10 185325524198264863 = some 185325524198264863 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 8 2 185325524198264863 185325524198264863 185325524198264863 endpoint_14_32_prefix_8 endpoint_14_32_window_8
private theorem endpoint_14_32_window_10 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 10 2 185325524198264863 = some 185325524198264863 := by decide +kernel
private theorem endpoint_14_32_prefix_12 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 12 185325524198264863 = some 185325524198264863 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 10 2 185325524198264863 185325524198264863 185325524198264863 endpoint_14_32_prefix_10 endpoint_14_32_window_10
private theorem endpoint_14_32_window_12 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 12 1 185325524198264863 = some 185325524198264863 := by decide +kernel
private theorem endpoint_14_32_prefix_13 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 13 185325524198264863 = some 185325524198264863 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 12 1 185325524198264863 185325524198264863 185325524198264863 endpoint_14_32_prefix_12 endpoint_14_32_window_12

def endpoint_14_32 : CertifiedEndpoint :=
  ⟨⟨14, 32, 3425⟩, 185325524198264863, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_32_flag endpoint_14_32_sources 13 185325524198264863 185325524198264863 rfl endpoint_14_32_base endpoint_14_32_prefix_13) (by decide)⟩
private def endpoint_14_33_flag : Flag := ⟨14, 33, 3399⟩
private def endpoint_14_33_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_33_base : receiptBase endpoint_14_33_flag endpoint_14_33_sources = some 188727636068729679 := by decide +kernel
private theorem endpoint_14_33_window_0 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 2 188727636068729679 = some 188727636068729679 := by decide +kernel
private theorem endpoint_14_33_window_2 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 2 2 188727636068729679 = some 188727636068729679 := by decide +kernel
private theorem endpoint_14_33_prefix_4 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 4 188727636068729679 = some 188727636068729679 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 2 2 188727636068729679 188727636068729679 188727636068729679 endpoint_14_33_window_0 endpoint_14_33_window_2
private theorem endpoint_14_33_window_4 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 4 2 188727636068729679 = some 188727636068729679 := by decide +kernel
private theorem endpoint_14_33_prefix_6 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 6 188727636068729679 = some 188727636068729679 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 4 2 188727636068729679 188727636068729679 188727636068729679 endpoint_14_33_prefix_4 endpoint_14_33_window_4
private theorem endpoint_14_33_window_6 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 6 2 188727636068729679 = some 188727636068729679 := by decide +kernel
private theorem endpoint_14_33_prefix_8 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 8 188727636068729679 = some 188727636068729679 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 6 2 188727636068729679 188727636068729679 188727636068729679 endpoint_14_33_prefix_6 endpoint_14_33_window_6
private theorem endpoint_14_33_window_8 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 8 2 188727636068729679 = some 188727636068729679 := by decide +kernel
private theorem endpoint_14_33_prefix_10 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 10 188727636068729679 = some 188727636068729679 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 8 2 188727636068729679 188727636068729679 188727636068729679 endpoint_14_33_prefix_8 endpoint_14_33_window_8
private theorem endpoint_14_33_window_10 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 10 2 188727636068729679 = some 188727636068729679 := by decide +kernel
private theorem endpoint_14_33_prefix_12 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 12 188727636068729679 = some 188727636068729679 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 10 2 188727636068729679 188727636068729679 188727636068729679 endpoint_14_33_prefix_10 endpoint_14_33_window_10
private theorem endpoint_14_33_window_12 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 12 1 188727636068729679 = some 188727636068729679 := by decide +kernel
private theorem endpoint_14_33_prefix_13 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 13 188727636068729679 = some 188727636068729679 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 12 1 188727636068729679 188727636068729679 188727636068729679 endpoint_14_33_prefix_12 endpoint_14_33_window_12

def endpoint_14_33 : CertifiedEndpoint :=
  ⟨⟨14, 33, 3399⟩, 188727636068729679, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_33_flag endpoint_14_33_sources 13 188727636068729679 188727636068729679 rfl endpoint_14_33_base endpoint_14_33_prefix_13) (by decide)⟩
private def endpoint_14_34_flag : Flag := ⟨14, 34, 3372⟩
private def endpoint_14_34_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_34_base : receiptBase endpoint_14_34_flag endpoint_14_34_sources = some 193148805055706080 := by decide +kernel
private theorem endpoint_14_34_window_0 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 2 193148805055706080 = some 193148805055706080 := by decide +kernel
private theorem endpoint_14_34_window_2 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 2 2 193148805055706080 = some 193148805055706080 := by decide +kernel
private theorem endpoint_14_34_prefix_4 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 4 193148805055706080 = some 193148805055706080 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 2 2 193148805055706080 193148805055706080 193148805055706080 endpoint_14_34_window_0 endpoint_14_34_window_2
private theorem endpoint_14_34_window_4 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 4 2 193148805055706080 = some 193148805055706080 := by decide +kernel
private theorem endpoint_14_34_prefix_6 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 6 193148805055706080 = some 193148805055706080 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 4 2 193148805055706080 193148805055706080 193148805055706080 endpoint_14_34_prefix_4 endpoint_14_34_window_4
private theorem endpoint_14_34_window_6 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 6 2 193148805055706080 = some 193148805055706080 := by decide +kernel
private theorem endpoint_14_34_prefix_8 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 8 193148805055706080 = some 193148805055706080 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 6 2 193148805055706080 193148805055706080 193148805055706080 endpoint_14_34_prefix_6 endpoint_14_34_window_6
private theorem endpoint_14_34_window_8 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 8 2 193148805055706080 = some 193148805055706080 := by decide +kernel
private theorem endpoint_14_34_prefix_10 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 10 193148805055706080 = some 193148805055706080 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 8 2 193148805055706080 193148805055706080 193148805055706080 endpoint_14_34_prefix_8 endpoint_14_34_window_8
private theorem endpoint_14_34_window_10 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 10 2 193148805055706080 = some 193148805055706080 := by decide +kernel
private theorem endpoint_14_34_prefix_12 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 12 193148805055706080 = some 193148805055706080 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 10 2 193148805055706080 193148805055706080 193148805055706080 endpoint_14_34_prefix_10 endpoint_14_34_window_10
private theorem endpoint_14_34_window_12 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 12 1 193148805055706080 = some 193148805055706080 := by decide +kernel
private theorem endpoint_14_34_prefix_13 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 13 193148805055706080 = some 193148805055706080 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 12 1 193148805055706080 193148805055706080 193148805055706080 endpoint_14_34_prefix_12 endpoint_14_34_window_12

def endpoint_14_34 : CertifiedEndpoint :=
  ⟨⟨14, 34, 3372⟩, 193148805055706080, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_34_flag endpoint_14_34_sources 13 193148805055706080 193148805055706080 rfl endpoint_14_34_base endpoint_14_34_prefix_13) (by decide)⟩
private def endpoint_14_35_flag : Flag := ⟨14, 35, 3344⟩
private def endpoint_14_35_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_35_base : receiptBase endpoint_14_35_flag endpoint_14_35_sources = some 196214181804158618 := by decide +kernel
private theorem endpoint_14_35_window_0 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 2 196214181804158618 = some 196214181804158618 := by decide +kernel
private theorem endpoint_14_35_window_2 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 2 2 196214181804158618 = some 196214181804158618 := by decide +kernel
private theorem endpoint_14_35_prefix_4 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 4 196214181804158618 = some 196214181804158618 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 2 2 196214181804158618 196214181804158618 196214181804158618 endpoint_14_35_window_0 endpoint_14_35_window_2
private theorem endpoint_14_35_window_4 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 4 2 196214181804158618 = some 196214181804158618 := by decide +kernel
private theorem endpoint_14_35_prefix_6 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 6 196214181804158618 = some 196214181804158618 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 4 2 196214181804158618 196214181804158618 196214181804158618 endpoint_14_35_prefix_4 endpoint_14_35_window_4
private theorem endpoint_14_35_window_6 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 6 2 196214181804158618 = some 196214181804158618 := by decide +kernel
private theorem endpoint_14_35_prefix_8 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 8 196214181804158618 = some 196214181804158618 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 6 2 196214181804158618 196214181804158618 196214181804158618 endpoint_14_35_prefix_6 endpoint_14_35_window_6
private theorem endpoint_14_35_window_8 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 8 2 196214181804158618 = some 196214181804158618 := by decide +kernel
private theorem endpoint_14_35_prefix_10 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 10 196214181804158618 = some 196214181804158618 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 8 2 196214181804158618 196214181804158618 196214181804158618 endpoint_14_35_prefix_8 endpoint_14_35_window_8
private theorem endpoint_14_35_window_10 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 10 2 196214181804158618 = some 196214181804158618 := by decide +kernel
private theorem endpoint_14_35_prefix_12 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 12 196214181804158618 = some 196214181804158618 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 10 2 196214181804158618 196214181804158618 196214181804158618 endpoint_14_35_prefix_10 endpoint_14_35_window_10
private theorem endpoint_14_35_window_12 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 12 1 196214181804158618 = some 196214181804158618 := by decide +kernel
private theorem endpoint_14_35_prefix_13 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 13 196214181804158618 = some 196214181804158618 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 12 1 196214181804158618 196214181804158618 196214181804158618 endpoint_14_35_prefix_12 endpoint_14_35_window_12

def endpoint_14_35 : CertifiedEndpoint :=
  ⟨⟨14, 35, 3344⟩, 196214181804158618, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_35_flag endpoint_14_35_sources 13 196214181804158618 196214181804158618 rfl endpoint_14_35_base endpoint_14_35_prefix_13) (by decide)⟩
private def endpoint_14_36_flag : Flag := ⟨14, 36, 3317⟩
private def endpoint_14_36_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_36_base : receiptBase endpoint_14_36_flag endpoint_14_36_sources = some 199261237560115336 := by decide +kernel
private theorem endpoint_14_36_window_0 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 2 199261237560115336 = some 199261237560115336 := by decide +kernel
private theorem endpoint_14_36_window_2 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 2 2 199261237560115336 = some 199261237560115336 := by decide +kernel
private theorem endpoint_14_36_prefix_4 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 4 199261237560115336 = some 199261237560115336 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 2 2 199261237560115336 199261237560115336 199261237560115336 endpoint_14_36_window_0 endpoint_14_36_window_2
private theorem endpoint_14_36_window_4 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 4 2 199261237560115336 = some 199261237560115336 := by decide +kernel
private theorem endpoint_14_36_prefix_6 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 6 199261237560115336 = some 199261237560115336 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 4 2 199261237560115336 199261237560115336 199261237560115336 endpoint_14_36_prefix_4 endpoint_14_36_window_4
private theorem endpoint_14_36_window_6 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 6 2 199261237560115336 = some 199261237560115336 := by decide +kernel
private theorem endpoint_14_36_prefix_8 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 8 199261237560115336 = some 199261237560115336 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 6 2 199261237560115336 199261237560115336 199261237560115336 endpoint_14_36_prefix_6 endpoint_14_36_window_6
private theorem endpoint_14_36_window_8 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 8 2 199261237560115336 = some 199261237560115336 := by decide +kernel
private theorem endpoint_14_36_prefix_10 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 10 199261237560115336 = some 199261237560115336 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 8 2 199261237560115336 199261237560115336 199261237560115336 endpoint_14_36_prefix_8 endpoint_14_36_window_8
private theorem endpoint_14_36_window_10 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 10 2 199261237560115336 = some 199261237560115336 := by decide +kernel
private theorem endpoint_14_36_prefix_12 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 12 199261237560115336 = some 199261237560115336 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 10 2 199261237560115336 199261237560115336 199261237560115336 endpoint_14_36_prefix_10 endpoint_14_36_window_10
private theorem endpoint_14_36_window_12 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 12 1 199261237560115336 = some 199261237560115336 := by decide +kernel
private theorem endpoint_14_36_prefix_13 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 13 199261237560115336 = some 199261237560115336 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 12 1 199261237560115336 199261237560115336 199261237560115336 endpoint_14_36_prefix_12 endpoint_14_36_window_12

def endpoint_14_36 : CertifiedEndpoint :=
  ⟨⟨14, 36, 3317⟩, 199261237560115336, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_36_flag endpoint_14_36_sources 13 199261237560115336 199261237560115336 rfl endpoint_14_36_base endpoint_14_36_prefix_13) (by decide)⟩
private def endpoint_14_37_flag : Flag := ⟨14, 37, 3288⟩
private def endpoint_14_37_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_37_base : receiptBase endpoint_14_37_flag endpoint_14_37_sources = some 202112600085815032 := by decide +kernel
private theorem endpoint_14_37_window_0 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 2 202112600085815032 = some 202112600085815032 := by decide +kernel
private theorem endpoint_14_37_window_2 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 2 2 202112600085815032 = some 202112600085815032 := by decide +kernel
private theorem endpoint_14_37_prefix_4 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 4 202112600085815032 = some 202112600085815032 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 2 2 202112600085815032 202112600085815032 202112600085815032 endpoint_14_37_window_0 endpoint_14_37_window_2
private theorem endpoint_14_37_window_4 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 4 2 202112600085815032 = some 202112600085815032 := by decide +kernel
private theorem endpoint_14_37_prefix_6 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 6 202112600085815032 = some 202112600085815032 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 4 2 202112600085815032 202112600085815032 202112600085815032 endpoint_14_37_prefix_4 endpoint_14_37_window_4
private theorem endpoint_14_37_window_6 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 6 2 202112600085815032 = some 202112600085815032 := by decide +kernel
private theorem endpoint_14_37_prefix_8 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 8 202112600085815032 = some 202112600085815032 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 6 2 202112600085815032 202112600085815032 202112600085815032 endpoint_14_37_prefix_6 endpoint_14_37_window_6
private theorem endpoint_14_37_window_8 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 8 2 202112600085815032 = some 202112600085815032 := by decide +kernel
private theorem endpoint_14_37_prefix_10 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 10 202112600085815032 = some 202112600085815032 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 8 2 202112600085815032 202112600085815032 202112600085815032 endpoint_14_37_prefix_8 endpoint_14_37_window_8
private theorem endpoint_14_37_window_10 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 10 2 202112600085815032 = some 202112600085815032 := by decide +kernel
private theorem endpoint_14_37_prefix_12 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 12 202112600085815032 = some 202112600085815032 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 10 2 202112600085815032 202112600085815032 202112600085815032 endpoint_14_37_prefix_10 endpoint_14_37_window_10
private theorem endpoint_14_37_window_12 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 12 1 202112600085815032 = some 202112600085815032 := by decide +kernel
private theorem endpoint_14_37_prefix_13 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 13 202112600085815032 = some 202112600085815032 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 12 1 202112600085815032 202112600085815032 202112600085815032 endpoint_14_37_prefix_12 endpoint_14_37_window_12

def endpoint_14_37 : CertifiedEndpoint :=
  ⟨⟨14, 37, 3288⟩, 202112600085815032, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_37_flag endpoint_14_37_sources 13 202112600085815032 202112600085815032 rfl endpoint_14_37_base endpoint_14_37_prefix_13) (by decide)⟩
private def endpoint_14_38_flag : Flag := ⟨14, 38, 3259⟩
private def endpoint_14_38_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_38_base : receiptBase endpoint_14_38_flag endpoint_14_38_sources = some 204883800326707470 := by decide +kernel
private theorem endpoint_14_38_window_0 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 2 204883800326707470 = some 204883800326707470 := by decide +kernel
private theorem endpoint_14_38_window_2 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 2 2 204883800326707470 = some 204883800326707470 := by decide +kernel
private theorem endpoint_14_38_prefix_4 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 4 204883800326707470 = some 204883800326707470 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 2 2 204883800326707470 204883800326707470 204883800326707470 endpoint_14_38_window_0 endpoint_14_38_window_2
private theorem endpoint_14_38_window_4 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 4 2 204883800326707470 = some 204883800326707470 := by decide +kernel
private theorem endpoint_14_38_prefix_6 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 6 204883800326707470 = some 204883800326707470 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 4 2 204883800326707470 204883800326707470 204883800326707470 endpoint_14_38_prefix_4 endpoint_14_38_window_4
private theorem endpoint_14_38_window_6 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 6 2 204883800326707470 = some 204883800326707470 := by decide +kernel
private theorem endpoint_14_38_prefix_8 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 8 204883800326707470 = some 204883800326707470 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 6 2 204883800326707470 204883800326707470 204883800326707470 endpoint_14_38_prefix_6 endpoint_14_38_window_6
private theorem endpoint_14_38_window_8 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 8 2 204883800326707470 = some 204883800326707470 := by decide +kernel
private theorem endpoint_14_38_prefix_10 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 10 204883800326707470 = some 204883800326707470 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 8 2 204883800326707470 204883800326707470 204883800326707470 endpoint_14_38_prefix_8 endpoint_14_38_window_8
private theorem endpoint_14_38_window_10 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 10 2 204883800326707470 = some 204883800326707470 := by decide +kernel
private theorem endpoint_14_38_prefix_12 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 12 204883800326707470 = some 204883800326707470 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 10 2 204883800326707470 204883800326707470 204883800326707470 endpoint_14_38_prefix_10 endpoint_14_38_window_10
private theorem endpoint_14_38_window_12 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 12 1 204883800326707470 = some 204883800326707470 := by decide +kernel
private theorem endpoint_14_38_prefix_13 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 13 204883800326707470 = some 204883800326707470 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 12 1 204883800326707470 204883800326707470 204883800326707470 endpoint_14_38_prefix_12 endpoint_14_38_window_12

def endpoint_14_38 : CertifiedEndpoint :=
  ⟨⟨14, 38, 3259⟩, 204883800326707470, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_38_flag endpoint_14_38_sources 13 204883800326707470 204883800326707470 rfl endpoint_14_38_base endpoint_14_38_prefix_13) (by decide)⟩
private def endpoint_14_39_flag : Flag := ⟨14, 39, 3230⟩
private def endpoint_14_39_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_39_base : receiptBase endpoint_14_39_flag endpoint_14_39_sources = some 207574838282792651 := by decide +kernel
private theorem endpoint_14_39_window_0 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 2 207574838282792651 = some 207574838282792651 := by decide +kernel
private theorem endpoint_14_39_window_2 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 2 2 207574838282792651 = some 207574838282792651 := by decide +kernel
private theorem endpoint_14_39_prefix_4 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 4 207574838282792651 = some 207574838282792651 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 2 2 207574838282792651 207574838282792651 207574838282792651 endpoint_14_39_window_0 endpoint_14_39_window_2
private theorem endpoint_14_39_window_4 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 4 2 207574838282792651 = some 207574838282792651 := by decide +kernel
private theorem endpoint_14_39_prefix_6 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 6 207574838282792651 = some 207574838282792651 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 4 2 207574838282792651 207574838282792651 207574838282792651 endpoint_14_39_prefix_4 endpoint_14_39_window_4
private theorem endpoint_14_39_window_6 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 6 2 207574838282792651 = some 207574838282792651 := by decide +kernel
private theorem endpoint_14_39_prefix_8 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 8 207574838282792651 = some 207574838282792651 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 6 2 207574838282792651 207574838282792651 207574838282792651 endpoint_14_39_prefix_6 endpoint_14_39_window_6
private theorem endpoint_14_39_window_8 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 8 2 207574838282792651 = some 207574838282792651 := by decide +kernel
private theorem endpoint_14_39_prefix_10 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 10 207574838282792651 = some 207574838282792651 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 8 2 207574838282792651 207574838282792651 207574838282792651 endpoint_14_39_prefix_8 endpoint_14_39_window_8
private theorem endpoint_14_39_window_10 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 10 2 207574838282792651 = some 207574838282792651 := by decide +kernel
private theorem endpoint_14_39_prefix_12 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 12 207574838282792651 = some 207574838282792651 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 10 2 207574838282792651 207574838282792651 207574838282792651 endpoint_14_39_prefix_10 endpoint_14_39_window_10
private theorem endpoint_14_39_window_12 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 12 1 207574838282792651 = some 207574838282792651 := by decide +kernel
private theorem endpoint_14_39_prefix_13 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 13 207574838282792651 = some 207574838282792651 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 12 1 207574838282792651 207574838282792651 207574838282792651 endpoint_14_39_prefix_12 endpoint_14_39_window_12

def endpoint_14_39 : CertifiedEndpoint :=
  ⟨⟨14, 39, 3230⟩, 207574838282792651, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_39_flag endpoint_14_39_sources 13 207574838282792651 207574838282792651 rfl endpoint_14_39_base endpoint_14_39_prefix_13) (by decide)⟩
private def endpoint_14_40_flag : Flag := ⟨14, 40, 3200⟩
private def endpoint_14_40_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_40_base : receiptBase endpoint_14_40_flag endpoint_14_40_sources = some 210668532749168790 := by decide +kernel
private theorem endpoint_14_40_window_0 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 2 210668532749168790 = some 210668532749168790 := by decide +kernel
private theorem endpoint_14_40_window_2 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 2 2 210668532749168790 = some 210668532749168790 := by decide +kernel
private theorem endpoint_14_40_prefix_4 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 4 210668532749168790 = some 210668532749168790 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 2 2 210668532749168790 210668532749168790 210668532749168790 endpoint_14_40_window_0 endpoint_14_40_window_2
private theorem endpoint_14_40_window_4 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 4 2 210668532749168790 = some 210668532749168790 := by decide +kernel
private theorem endpoint_14_40_prefix_6 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 6 210668532749168790 = some 210668532749168790 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 4 2 210668532749168790 210668532749168790 210668532749168790 endpoint_14_40_prefix_4 endpoint_14_40_window_4
private theorem endpoint_14_40_window_6 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 6 2 210668532749168790 = some 210668532749168790 := by decide +kernel
private theorem endpoint_14_40_prefix_8 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 8 210668532749168790 = some 210668532749168790 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 6 2 210668532749168790 210668532749168790 210668532749168790 endpoint_14_40_prefix_6 endpoint_14_40_window_6
private theorem endpoint_14_40_window_8 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 8 2 210668532749168790 = some 210668532749168790 := by decide +kernel
private theorem endpoint_14_40_prefix_10 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 10 210668532749168790 = some 210668532749168790 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 8 2 210668532749168790 210668532749168790 210668532749168790 endpoint_14_40_prefix_8 endpoint_14_40_window_8
private theorem endpoint_14_40_window_10 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 10 2 210668532749168790 = some 210668532749168790 := by decide +kernel
private theorem endpoint_14_40_prefix_12 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 12 210668532749168790 = some 210668532749168790 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 10 2 210668532749168790 210668532749168790 210668532749168790 endpoint_14_40_prefix_10 endpoint_14_40_window_10
private theorem endpoint_14_40_window_12 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 12 1 210668532749168790 = some 210668532749168790 := by decide +kernel
private theorem endpoint_14_40_prefix_13 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 13 210668532749168790 = some 210668532749168790 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 12 1 210668532749168790 210668532749168790 210668532749168790 endpoint_14_40_prefix_12 endpoint_14_40_window_12

def endpoint_14_40 : CertifiedEndpoint :=
  ⟨⟨14, 40, 3200⟩, 210668532749168790, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_40_flag endpoint_14_40_sources 13 210668532749168790 210668532749168790 rfl endpoint_14_40_base endpoint_14_40_prefix_13) (by decide)⟩
private def endpoint_14_41_flag : Flag := ⟨14, 41, 3169⟩
private def endpoint_14_41_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_41_base : receiptBase endpoint_14_41_flag endpoint_14_41_sources = some 213079749686272511 := by decide +kernel
private theorem endpoint_14_41_window_0 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 2 213079749686272511 = some 213860683155363366 := by decide +kernel
private theorem endpoint_14_41_window_2 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 2 2 213860683155363366 = some 213860683155363366 := by decide +kernel
private theorem endpoint_14_41_prefix_4 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 4 213079749686272511 = some 213860683155363366 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 2 2 213079749686272511 213860683155363366 213860683155363366 endpoint_14_41_window_0 endpoint_14_41_window_2
private theorem endpoint_14_41_window_4 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 4 2 213860683155363366 = some 213860683155363366 := by decide +kernel
private theorem endpoint_14_41_prefix_6 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 6 213079749686272511 = some 213860683155363366 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 4 2 213079749686272511 213860683155363366 213860683155363366 endpoint_14_41_prefix_4 endpoint_14_41_window_4
private theorem endpoint_14_41_window_6 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 6 2 213860683155363366 = some 213860683155363366 := by decide +kernel
private theorem endpoint_14_41_prefix_8 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 8 213079749686272511 = some 213860683155363366 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 6 2 213079749686272511 213860683155363366 213860683155363366 endpoint_14_41_prefix_6 endpoint_14_41_window_6
private theorem endpoint_14_41_window_8 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 8 2 213860683155363366 = some 213860683155363366 := by decide +kernel
private theorem endpoint_14_41_prefix_10 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 10 213079749686272511 = some 213860683155363366 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 8 2 213079749686272511 213860683155363366 213860683155363366 endpoint_14_41_prefix_8 endpoint_14_41_window_8
private theorem endpoint_14_41_window_10 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 10 2 213860683155363366 = some 213860683155363366 := by decide +kernel
private theorem endpoint_14_41_prefix_12 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 12 213079749686272511 = some 213860683155363366 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 10 2 213079749686272511 213860683155363366 213860683155363366 endpoint_14_41_prefix_10 endpoint_14_41_window_10
private theorem endpoint_14_41_window_12 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 12 1 213860683155363366 = some 213860683155363366 := by decide +kernel
private theorem endpoint_14_41_prefix_13 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 13 213079749686272511 = some 213860683155363366 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 12 1 213079749686272511 213860683155363366 213860683155363366 endpoint_14_41_prefix_12 endpoint_14_41_window_12

def endpoint_14_41 : CertifiedEndpoint :=
  ⟨⟨14, 41, 3169⟩, 213860683155363366, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_41_flag endpoint_14_41_sources 13 213079749686272511 213860683155363366 rfl endpoint_14_41_base endpoint_14_41_prefix_13) (by decide)⟩
private def endpoint_14_42_flag : Flag := ⟨14, 42, 3138⟩
private def endpoint_14_42_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_42_base : receiptBase endpoint_14_42_flag endpoint_14_42_sources = some 215404802866525825 := by decide +kernel
private theorem endpoint_14_42_window_0 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 2 215404802866525825 = some 219176584829842576 := by decide +kernel
private theorem endpoint_14_42_window_2 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 2 2 219176584829842576 = some 219176584829842576 := by decide +kernel
private theorem endpoint_14_42_prefix_4 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 4 215404802866525825 = some 219176584829842576 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 2 2 215404802866525825 219176584829842576 219176584829842576 endpoint_14_42_window_0 endpoint_14_42_window_2
private theorem endpoint_14_42_window_4 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 4 2 219176584829842576 = some 219176584829842576 := by decide +kernel
private theorem endpoint_14_42_prefix_6 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 6 215404802866525825 = some 219176584829842576 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 4 2 215404802866525825 219176584829842576 219176584829842576 endpoint_14_42_prefix_4 endpoint_14_42_window_4
private theorem endpoint_14_42_window_6 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 6 2 219176584829842576 = some 219176584829842576 := by decide +kernel
private theorem endpoint_14_42_prefix_8 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 8 215404802866525825 = some 219176584829842576 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 6 2 215404802866525825 219176584829842576 219176584829842576 endpoint_14_42_prefix_6 endpoint_14_42_window_6
private theorem endpoint_14_42_window_8 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 8 2 219176584829842576 = some 219176584829842576 := by decide +kernel
private theorem endpoint_14_42_prefix_10 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 10 215404802866525825 = some 219176584829842576 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 8 2 215404802866525825 219176584829842576 219176584829842576 endpoint_14_42_prefix_8 endpoint_14_42_window_8
private theorem endpoint_14_42_window_10 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 10 2 219176584829842576 = some 219176584829842576 := by decide +kernel
private theorem endpoint_14_42_prefix_12 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 12 215404802866525825 = some 219176584829842576 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 10 2 215404802866525825 219176584829842576 219176584829842576 endpoint_14_42_prefix_10 endpoint_14_42_window_10
private theorem endpoint_14_42_window_12 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 12 1 219176584829842576 = some 219176584829842576 := by decide +kernel
private theorem endpoint_14_42_prefix_13 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 13 215404802866525825 = some 219176584829842576 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 12 1 215404802866525825 219176584829842576 219176584829842576 endpoint_14_42_prefix_12 endpoint_14_42_window_12

def endpoint_14_42 : CertifiedEndpoint :=
  ⟨⟨14, 42, 3138⟩, 219176584829842576, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_42_flag endpoint_14_42_sources 13 215404802866525825 219176584829842576 rfl endpoint_14_42_base endpoint_14_42_prefix_13) (by decide)⟩
private def endpoint_14_43_flag : Flag := ⟨14, 43, 3106⟩
private def endpoint_14_43_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_43_base : receiptBase endpoint_14_43_flag endpoint_14_43_sources = some 217574800216187726 := by decide +kernel
private theorem endpoint_14_43_window_0 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 2 217574800216187726 = some 224387008018011241 := by decide +kernel
private theorem endpoint_14_43_window_2 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 2 2 224387008018011241 = some 224387008018011241 := by decide +kernel
private theorem endpoint_14_43_prefix_4 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 4 217574800216187726 = some 224387008018011241 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 2 2 217574800216187726 224387008018011241 224387008018011241 endpoint_14_43_window_0 endpoint_14_43_window_2
private theorem endpoint_14_43_window_4 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 4 2 224387008018011241 = some 224387008018011241 := by decide +kernel
private theorem endpoint_14_43_prefix_6 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 6 217574800216187726 = some 224387008018011241 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 4 2 217574800216187726 224387008018011241 224387008018011241 endpoint_14_43_prefix_4 endpoint_14_43_window_4
private theorem endpoint_14_43_window_6 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 6 2 224387008018011241 = some 224387008018011241 := by decide +kernel
private theorem endpoint_14_43_prefix_8 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 8 217574800216187726 = some 224387008018011241 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 6 2 217574800216187726 224387008018011241 224387008018011241 endpoint_14_43_prefix_6 endpoint_14_43_window_6
private theorem endpoint_14_43_window_8 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 8 2 224387008018011241 = some 224387008018011241 := by decide +kernel
private theorem endpoint_14_43_prefix_10 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 10 217574800216187726 = some 224387008018011241 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 8 2 217574800216187726 224387008018011241 224387008018011241 endpoint_14_43_prefix_8 endpoint_14_43_window_8
private theorem endpoint_14_43_window_10 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 10 2 224387008018011241 = some 224387008018011241 := by decide +kernel
private theorem endpoint_14_43_prefix_12 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 12 217574800216187726 = some 224387008018011241 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 10 2 217574800216187726 224387008018011241 224387008018011241 endpoint_14_43_prefix_10 endpoint_14_43_window_10
private theorem endpoint_14_43_window_12 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 12 1 224387008018011241 = some 224387008018011241 := by decide +kernel
private theorem endpoint_14_43_prefix_13 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 13 217574800216187726 = some 224387008018011241 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 12 1 217574800216187726 224387008018011241 224387008018011241 endpoint_14_43_prefix_12 endpoint_14_43_window_12

def endpoint_14_43 : CertifiedEndpoint :=
  ⟨⟨14, 43, 3106⟩, 224387008018011241, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_43_flag endpoint_14_43_sources 13 217574800216187726 224387008018011241 rfl endpoint_14_43_base endpoint_14_43_prefix_13) (by decide)⟩
private def endpoint_14_44_flag : Flag := ⟨14, 44, 3073⟩
private def endpoint_14_44_sources : Sources := ⟨contact23, contact03, contact25⟩
private theorem endpoint_14_44_base : receiptBase endpoint_14_44_flag endpoint_14_44_sources = some 220800607005170370 := by decide +kernel
private theorem endpoint_14_44_window_0 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 2 220800607005170370 = some 227833495409720220 := by decide +kernel
private theorem endpoint_14_44_window_2 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 2 2 227833495409720220 = some 227833495409720220 := by decide +kernel
private theorem endpoint_14_44_prefix_4 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 4 220800607005170370 = some 227833495409720220 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 2 2 220800607005170370 227833495409720220 227833495409720220 endpoint_14_44_window_0 endpoint_14_44_window_2
private theorem endpoint_14_44_window_4 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 4 2 227833495409720220 = some 227833495409720220 := by decide +kernel
private theorem endpoint_14_44_prefix_6 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 6 220800607005170370 = some 227833495409720220 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 4 2 220800607005170370 227833495409720220 227833495409720220 endpoint_14_44_prefix_4 endpoint_14_44_window_4
private theorem endpoint_14_44_window_6 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 6 2 227833495409720220 = some 227833495409720220 := by decide +kernel
private theorem endpoint_14_44_prefix_8 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 8 220800607005170370 = some 227833495409720220 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 6 2 220800607005170370 227833495409720220 227833495409720220 endpoint_14_44_prefix_6 endpoint_14_44_window_6
private theorem endpoint_14_44_window_8 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 8 2 227833495409720220 = some 227833495409720220 := by decide +kernel
private theorem endpoint_14_44_prefix_10 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 10 220800607005170370 = some 227833495409720220 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 8 2 220800607005170370 227833495409720220 227833495409720220 endpoint_14_44_prefix_8 endpoint_14_44_window_8
private theorem endpoint_14_44_window_10 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 10 2 227833495409720220 = some 227833495409720220 := by decide +kernel
private theorem endpoint_14_44_prefix_12 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 12 220800607005170370 = some 227833495409720220 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 10 2 220800607005170370 227833495409720220 227833495409720220 endpoint_14_44_prefix_10 endpoint_14_44_window_10
private theorem endpoint_14_44_window_12 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 12 1 227833495409720220 = some 227833495409720220 := by decide +kernel
private theorem endpoint_14_44_prefix_13 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 13 220800607005170370 = some 227833495409720220 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 12 1 220800607005170370 227833495409720220 227833495409720220 endpoint_14_44_prefix_12 endpoint_14_44_window_12

def endpoint_14_44 : CertifiedEndpoint :=
  ⟨⟨14, 44, 3073⟩, 227833495409720220, .terminal ⟨contact23, contact03, contact25⟩ (finish_receipt_window endpoint_14_44_flag endpoint_14_44_sources 13 220800607005170370 227833495409720220 rfl endpoint_14_44_base endpoint_14_44_prefix_13) (by decide)⟩
private def endpoint_14_45_flag : Flag := ⟨14, 45, 3040⟩
private def endpoint_14_45_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_45_base : receiptBase endpoint_14_45_flag endpoint_14_45_sources = some 223771790783203229 := by decide +kernel
private theorem endpoint_14_45_window_0 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 2 223771790783203229 = some 227875878194380113 := by decide +kernel
private theorem endpoint_14_45_window_2 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 2 2 227875878194380113 = some 227875878194380113 := by decide +kernel
private theorem endpoint_14_45_prefix_4 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 4 223771790783203229 = some 227875878194380113 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 2 2 223771790783203229 227875878194380113 227875878194380113 endpoint_14_45_window_0 endpoint_14_45_window_2
private theorem endpoint_14_45_window_4 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 4 2 227875878194380113 = some 227875878194380113 := by decide +kernel
private theorem endpoint_14_45_prefix_6 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 6 223771790783203229 = some 227875878194380113 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 4 2 223771790783203229 227875878194380113 227875878194380113 endpoint_14_45_prefix_4 endpoint_14_45_window_4
private theorem endpoint_14_45_window_6 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 6 2 227875878194380113 = some 227875878194380113 := by decide +kernel
private theorem endpoint_14_45_prefix_8 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 8 223771790783203229 = some 227875878194380113 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 6 2 223771790783203229 227875878194380113 227875878194380113 endpoint_14_45_prefix_6 endpoint_14_45_window_6
private theorem endpoint_14_45_window_8 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 8 2 227875878194380113 = some 227875878194380113 := by decide +kernel
private theorem endpoint_14_45_prefix_10 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 10 223771790783203229 = some 227875878194380113 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 8 2 223771790783203229 227875878194380113 227875878194380113 endpoint_14_45_prefix_8 endpoint_14_45_window_8
private theorem endpoint_14_45_window_10 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 10 2 227875878194380113 = some 227875878194380113 := by decide +kernel
private theorem endpoint_14_45_prefix_12 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 12 223771790783203229 = some 227875878194380113 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 10 2 223771790783203229 227875878194380113 227875878194380113 endpoint_14_45_prefix_10 endpoint_14_45_window_10
private theorem endpoint_14_45_window_12 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 12 1 227875878194380113 = some 227875878194380113 := by decide +kernel
private theorem endpoint_14_45_prefix_13 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 13 223771790783203229 = some 227875878194380113 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 12 1 223771790783203229 227875878194380113 227875878194380113 endpoint_14_45_prefix_12 endpoint_14_45_window_12

def endpoint_14_45 : CertifiedEndpoint :=
  ⟨⟨14, 45, 3040⟩, 227875878194380113, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_45_flag endpoint_14_45_sources 13 223771790783203229 227875878194380113 rfl endpoint_14_45_base endpoint_14_45_prefix_13) (by decide)⟩
private def endpoint_14_46_flag : Flag := ⟨14, 46, 3006⟩
private def endpoint_14_46_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_46_base : receiptBase endpoint_14_46_flag endpoint_14_46_sources = some 225470982370642046 := by decide +kernel
private theorem endpoint_14_46_window_0 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 2 225470982370642046 = some 232613602572339732 := by decide +kernel
private theorem endpoint_14_46_window_2 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 2 2 232613602572339732 = some 232613602572339732 := by decide +kernel
private theorem endpoint_14_46_prefix_4 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 4 225470982370642046 = some 232613602572339732 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 2 2 225470982370642046 232613602572339732 232613602572339732 endpoint_14_46_window_0 endpoint_14_46_window_2
private theorem endpoint_14_46_window_4 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 4 2 232613602572339732 = some 232613602572339732 := by decide +kernel
private theorem endpoint_14_46_prefix_6 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 6 225470982370642046 = some 232613602572339732 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 4 2 225470982370642046 232613602572339732 232613602572339732 endpoint_14_46_prefix_4 endpoint_14_46_window_4
private theorem endpoint_14_46_window_6 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 6 2 232613602572339732 = some 232613602572339732 := by decide +kernel
private theorem endpoint_14_46_prefix_8 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 8 225470982370642046 = some 232613602572339732 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 6 2 225470982370642046 232613602572339732 232613602572339732 endpoint_14_46_prefix_6 endpoint_14_46_window_6
private theorem endpoint_14_46_window_8 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 8 2 232613602572339732 = some 232613602572339732 := by decide +kernel
private theorem endpoint_14_46_prefix_10 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 10 225470982370642046 = some 232613602572339732 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 8 2 225470982370642046 232613602572339732 232613602572339732 endpoint_14_46_prefix_8 endpoint_14_46_window_8
private theorem endpoint_14_46_window_10 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 10 2 232613602572339732 = some 232613602572339732 := by decide +kernel
private theorem endpoint_14_46_prefix_12 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 12 225470982370642046 = some 232613602572339732 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 10 2 225470982370642046 232613602572339732 232613602572339732 endpoint_14_46_prefix_10 endpoint_14_46_window_10
private theorem endpoint_14_46_window_12 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 12 1 232613602572339732 = some 232613602572339732 := by decide +kernel
private theorem endpoint_14_46_prefix_13 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 13 225470982370642046 = some 232613602572339732 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 12 1 225470982370642046 232613602572339732 232613602572339732 endpoint_14_46_prefix_12 endpoint_14_46_window_12

def endpoint_14_46 : CertifiedEndpoint :=
  ⟨⟨14, 46, 3006⟩, 232613602572339732, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_46_flag endpoint_14_46_sources 13 225470982370642046 232613602572339732 rfl endpoint_14_46_base endpoint_14_46_prefix_13) (by decide)⟩
private def endpoint_14_47_flag : Flag := ⟨14, 47, 2971⟩
private def endpoint_14_47_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_47_base : receiptBase endpoint_14_47_flag endpoint_14_47_sources = some 227000856386309491 := by decide +kernel
private theorem endpoint_14_47_window_0 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 2 227000856386309491 = some 237235282577707536 := by decide +kernel
private theorem endpoint_14_47_window_2 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 2 2 237235282577707536 = some 237235282577707536 := by decide +kernel
private theorem endpoint_14_47_prefix_4 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 4 227000856386309491 = some 237235282577707536 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 2 2 227000856386309491 237235282577707536 237235282577707536 endpoint_14_47_window_0 endpoint_14_47_window_2
private theorem endpoint_14_47_window_4 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 4 2 237235282577707536 = some 237235282577707536 := by decide +kernel
private theorem endpoint_14_47_prefix_6 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 6 227000856386309491 = some 237235282577707536 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 4 2 227000856386309491 237235282577707536 237235282577707536 endpoint_14_47_prefix_4 endpoint_14_47_window_4
private theorem endpoint_14_47_window_6 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 6 2 237235282577707536 = some 237235282577707536 := by decide +kernel
private theorem endpoint_14_47_prefix_8 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 8 227000856386309491 = some 237235282577707536 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 6 2 227000856386309491 237235282577707536 237235282577707536 endpoint_14_47_prefix_6 endpoint_14_47_window_6
private theorem endpoint_14_47_window_8 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 8 2 237235282577707536 = some 237235282577707536 := by decide +kernel
private theorem endpoint_14_47_prefix_10 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 10 227000856386309491 = some 237235282577707536 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 8 2 227000856386309491 237235282577707536 237235282577707536 endpoint_14_47_prefix_8 endpoint_14_47_window_8
private theorem endpoint_14_47_window_10 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 10 2 237235282577707536 = some 237235282577707536 := by decide +kernel
private theorem endpoint_14_47_prefix_12 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 12 227000856386309491 = some 237235282577707536 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 10 2 227000856386309491 237235282577707536 237235282577707536 endpoint_14_47_prefix_10 endpoint_14_47_window_10
private theorem endpoint_14_47_window_12 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 12 1 237235282577707536 = some 237235282577707536 := by decide +kernel
private theorem endpoint_14_47_prefix_13 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 13 227000856386309491 = some 237235282577707536 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 12 1 227000856386309491 237235282577707536 237235282577707536 endpoint_14_47_prefix_12 endpoint_14_47_window_12

def endpoint_14_47 : CertifiedEndpoint :=
  ⟨⟨14, 47, 2971⟩, 237235282577707536, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_47_flag endpoint_14_47_sources 13 227000856386309491 237235282577707536 rfl endpoint_14_47_base endpoint_14_47_prefix_13) (by decide)⟩
private def endpoint_14_48_flag : Flag := ⟨14, 48, 2935⟩
private def endpoint_14_48_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_48_base : receiptBase endpoint_14_48_flag endpoint_14_48_sources = some 229066617368972807 := by decide +kernel
private theorem endpoint_14_48_window_0 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 2 229066617368972807 = some 234648916322937828 := by decide +kernel
private theorem endpoint_14_48_window_2 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 2 2 234648916322937828 = some 234648916322937828 := by decide +kernel
private theorem endpoint_14_48_prefix_4 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 4 229066617368972807 = some 234648916322937828 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 2 2 229066617368972807 234648916322937828 234648916322937828 endpoint_14_48_window_0 endpoint_14_48_window_2
private theorem endpoint_14_48_window_4 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 4 2 234648916322937828 = some 234648916322937828 := by decide +kernel
private theorem endpoint_14_48_prefix_6 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 6 229066617368972807 = some 234648916322937828 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 4 2 229066617368972807 234648916322937828 234648916322937828 endpoint_14_48_prefix_4 endpoint_14_48_window_4
private theorem endpoint_14_48_window_6 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 6 2 234648916322937828 = some 234648916322937828 := by decide +kernel
private theorem endpoint_14_48_prefix_8 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 8 229066617368972807 = some 234648916322937828 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 6 2 229066617368972807 234648916322937828 234648916322937828 endpoint_14_48_prefix_6 endpoint_14_48_window_6
private theorem endpoint_14_48_window_8 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 8 2 234648916322937828 = some 234648916322937828 := by decide +kernel
private theorem endpoint_14_48_prefix_10 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 10 229066617368972807 = some 234648916322937828 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 8 2 229066617368972807 234648916322937828 234648916322937828 endpoint_14_48_prefix_8 endpoint_14_48_window_8
private theorem endpoint_14_48_window_10 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 10 2 234648916322937828 = some 234648916322937828 := by decide +kernel
private theorem endpoint_14_48_prefix_12 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 12 229066617368972807 = some 234648916322937828 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 10 2 229066617368972807 234648916322937828 234648916322937828 endpoint_14_48_prefix_10 endpoint_14_48_window_10
private theorem endpoint_14_48_window_12 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 12 1 234648916322937828 = some 234648916322937828 := by decide +kernel
private theorem endpoint_14_48_prefix_13 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 13 229066617368972807 = some 234648916322937828 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 12 1 229066617368972807 234648916322937828 234648916322937828 endpoint_14_48_prefix_12 endpoint_14_48_window_12

def endpoint_14_48 : CertifiedEndpoint :=
  ⟨⟨14, 48, 2935⟩, 234648916322937828, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_48_flag endpoint_14_48_sources 13 229066617368972807 234648916322937828 rfl endpoint_14_48_base endpoint_14_48_prefix_13) (by decide)⟩
private def endpoint_14_49_flag : Flag := ⟨14, 49, 2898⟩
private def endpoint_14_49_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_49_base : receiptBase endpoint_14_49_flag endpoint_14_49_sources = some 230254929851371149 := by decide +kernel
private theorem endpoint_14_49_window_0 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 2 230254929851371149 = some 238852960387023120 := by decide +kernel
private theorem endpoint_14_49_window_2 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 2 2 238852960387023120 = some 238852960387023120 := by decide +kernel
private theorem endpoint_14_49_prefix_4 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 4 230254929851371149 = some 238852960387023120 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 2 2 230254929851371149 238852960387023120 238852960387023120 endpoint_14_49_window_0 endpoint_14_49_window_2
private theorem endpoint_14_49_window_4 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 4 2 238852960387023120 = some 238852960387023120 := by decide +kernel
private theorem endpoint_14_49_prefix_6 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 6 230254929851371149 = some 238852960387023120 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 4 2 230254929851371149 238852960387023120 238852960387023120 endpoint_14_49_prefix_4 endpoint_14_49_window_4
private theorem endpoint_14_49_window_6 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 6 2 238852960387023120 = some 238852960387023120 := by decide +kernel
private theorem endpoint_14_49_prefix_8 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 8 230254929851371149 = some 238852960387023120 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 6 2 230254929851371149 238852960387023120 238852960387023120 endpoint_14_49_prefix_6 endpoint_14_49_window_6
private theorem endpoint_14_49_window_8 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 8 2 238852960387023120 = some 238852960387023120 := by decide +kernel
private theorem endpoint_14_49_prefix_10 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 10 230254929851371149 = some 238852960387023120 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 8 2 230254929851371149 238852960387023120 238852960387023120 endpoint_14_49_prefix_8 endpoint_14_49_window_8
private theorem endpoint_14_49_window_10 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 10 2 238852960387023120 = some 238852960387023120 := by decide +kernel
private theorem endpoint_14_49_prefix_12 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 12 230254929851371149 = some 238852960387023120 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 10 2 230254929851371149 238852960387023120 238852960387023120 endpoint_14_49_prefix_10 endpoint_14_49_window_10
private theorem endpoint_14_49_window_12 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 12 1 238852960387023120 = some 238852960387023120 := by decide +kernel
private theorem endpoint_14_49_prefix_13 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 13 230254929851371149 = some 238852960387023120 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 12 1 230254929851371149 238852960387023120 238852960387023120 endpoint_14_49_prefix_12 endpoint_14_49_window_12

def endpoint_14_49 : CertifiedEndpoint :=
  ⟨⟨14, 49, 2898⟩, 238852960387023120, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_49_flag endpoint_14_49_sources 13 230254929851371149 238852960387023120 rfl endpoint_14_49_base endpoint_14_49_prefix_13) (by decide)⟩
private def endpoint_14_50_flag : Flag := ⟨14, 50, 2860⟩
private def endpoint_14_50_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_50_base : receiptBase endpoint_14_50_flag endpoint_14_50_sources = some 231260661039241435 := by decide +kernel
private theorem endpoint_14_50_window_0 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 2 231260661039241435 = some 242931450780863454 := by decide +kernel
private theorem endpoint_14_50_window_2 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 2 2 242931450780863454 = some 242931450780863454 := by decide +kernel
private theorem endpoint_14_50_prefix_4 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 4 231260661039241435 = some 242931450780863454 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 2 2 231260661039241435 242931450780863454 242931450780863454 endpoint_14_50_window_0 endpoint_14_50_window_2
private theorem endpoint_14_50_window_4 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 4 2 242931450780863454 = some 242931450780863454 := by decide +kernel
private theorem endpoint_14_50_prefix_6 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 6 231260661039241435 = some 242931450780863454 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 4 2 231260661039241435 242931450780863454 242931450780863454 endpoint_14_50_prefix_4 endpoint_14_50_window_4
private theorem endpoint_14_50_window_6 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 6 2 242931450780863454 = some 242931450780863454 := by decide +kernel
private theorem endpoint_14_50_prefix_8 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 8 231260661039241435 = some 242931450780863454 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 6 2 231260661039241435 242931450780863454 242931450780863454 endpoint_14_50_prefix_6 endpoint_14_50_window_6
private theorem endpoint_14_50_window_8 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 8 2 242931450780863454 = some 242931450780863454 := by decide +kernel
private theorem endpoint_14_50_prefix_10 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 10 231260661039241435 = some 242931450780863454 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 8 2 231260661039241435 242931450780863454 242931450780863454 endpoint_14_50_prefix_8 endpoint_14_50_window_8
private theorem endpoint_14_50_window_10 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 10 2 242931450780863454 = some 242931450780863454 := by decide +kernel
private theorem endpoint_14_50_prefix_12 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 12 231260661039241435 = some 242931450780863454 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 10 2 231260661039241435 242931450780863454 242931450780863454 endpoint_14_50_prefix_10 endpoint_14_50_window_10
private theorem endpoint_14_50_window_12 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 12 1 242931450780863454 = some 242931450780863454 := by decide +kernel
private theorem endpoint_14_50_prefix_13 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 13 231260661039241435 = some 242931450780863454 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 12 1 231260661039241435 242931450780863454 242931450780863454 endpoint_14_50_prefix_12 endpoint_14_50_window_12

def endpoint_14_50 : CertifiedEndpoint :=
  ⟨⟨14, 50, 2860⟩, 242931450780863454, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_50_flag endpoint_14_50_sources 13 231260661039241435 242931450780863454 rfl endpoint_14_50_base endpoint_14_50_prefix_13) (by decide)⟩
private def endpoint_14_51_flag : Flag := ⟨14, 51, 2821⟩
private def endpoint_14_51_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_51_base : receiptBase endpoint_14_51_flag endpoint_14_51_sources = some 232079694625665829 := by decide +kernel
private theorem endpoint_14_51_window_0 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 2 232079694625665829 = some 246881217738574449 := by decide +kernel
private theorem endpoint_14_51_window_2 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 2 2 246881217738574449 = some 246881217738574449 := by decide +kernel
private theorem endpoint_14_51_prefix_4 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 4 232079694625665829 = some 246881217738574449 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 2 2 232079694625665829 246881217738574449 246881217738574449 endpoint_14_51_window_0 endpoint_14_51_window_2
private theorem endpoint_14_51_window_4 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 4 2 246881217738574449 = some 246881217738574449 := by decide +kernel
private theorem endpoint_14_51_prefix_6 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 6 232079694625665829 = some 246881217738574449 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 4 2 232079694625665829 246881217738574449 246881217738574449 endpoint_14_51_prefix_4 endpoint_14_51_window_4
private theorem endpoint_14_51_window_6 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 6 2 246881217738574449 = some 246881217738574449 := by decide +kernel
private theorem endpoint_14_51_prefix_8 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 8 232079694625665829 = some 246881217738574449 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 6 2 232079694625665829 246881217738574449 246881217738574449 endpoint_14_51_prefix_6 endpoint_14_51_window_6
private theorem endpoint_14_51_window_8 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 8 2 246881217738574449 = some 246881217738574449 := by decide +kernel
private theorem endpoint_14_51_prefix_10 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 10 232079694625665829 = some 246881217738574449 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 8 2 232079694625665829 246881217738574449 246881217738574449 endpoint_14_51_prefix_8 endpoint_14_51_window_8
private theorem endpoint_14_51_window_10 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 10 2 246881217738574449 = some 246881217738574449 := by decide +kernel
private theorem endpoint_14_51_prefix_12 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 12 232079694625665829 = some 246881217738574449 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 10 2 232079694625665829 246881217738574449 246881217738574449 endpoint_14_51_prefix_10 endpoint_14_51_window_10
private theorem endpoint_14_51_window_12 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 12 1 246881217738574449 = some 246881217738574449 := by decide +kernel
private theorem endpoint_14_51_prefix_13 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 13 232079694625665829 = some 246881217738574449 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 12 1 232079694625665829 246881217738574449 246881217738574449 endpoint_14_51_prefix_12 endpoint_14_51_window_12

def endpoint_14_51 : CertifiedEndpoint :=
  ⟨⟨14, 51, 2821⟩, 246881217738574449, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_51_flag endpoint_14_51_sources 13 232079694625665829 246881217738574449 rfl endpoint_14_51_base endpoint_14_51_prefix_13) (by decide)⟩
private def endpoint_14_52_flag : Flag := ⟨14, 52, 2780⟩
private def endpoint_14_52_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_52_base : receiptBase endpoint_14_52_flag endpoint_14_52_sources = some 232625496477532466 := by decide +kernel
private theorem endpoint_14_52_window_0 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 2 232625496477532466 = some 250652842101268256 := by decide +kernel
private theorem endpoint_14_52_window_2 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 2 2 250652842101268256 = some 250652842101268256 := by decide +kernel
private theorem endpoint_14_52_prefix_4 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 4 232625496477532466 = some 250652842101268256 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 2 2 232625496477532466 250652842101268256 250652842101268256 endpoint_14_52_window_0 endpoint_14_52_window_2
private theorem endpoint_14_52_window_4 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 4 2 250652842101268256 = some 250652842101268256 := by decide +kernel
private theorem endpoint_14_52_prefix_6 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 6 232625496477532466 = some 250652842101268256 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 4 2 232625496477532466 250652842101268256 250652842101268256 endpoint_14_52_prefix_4 endpoint_14_52_window_4
private theorem endpoint_14_52_window_6 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 6 2 250652842101268256 = some 250652842101268256 := by decide +kernel
private theorem endpoint_14_52_prefix_8 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 8 232625496477532466 = some 250652842101268256 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 6 2 232625496477532466 250652842101268256 250652842101268256 endpoint_14_52_prefix_6 endpoint_14_52_window_6
private theorem endpoint_14_52_window_8 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 8 2 250652842101268256 = some 250652842101268256 := by decide +kernel
private theorem endpoint_14_52_prefix_10 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 10 232625496477532466 = some 250652842101268256 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 8 2 232625496477532466 250652842101268256 250652842101268256 endpoint_14_52_prefix_8 endpoint_14_52_window_8
private theorem endpoint_14_52_window_10 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 10 2 250652842101268256 = some 250652842101268256 := by decide +kernel
private theorem endpoint_14_52_prefix_12 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 12 232625496477532466 = some 250652842101268256 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 10 2 232625496477532466 250652842101268256 250652842101268256 endpoint_14_52_prefix_10 endpoint_14_52_window_10
private theorem endpoint_14_52_window_12 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 12 1 250652842101268256 = some 250652842101268256 := by decide +kernel
private theorem endpoint_14_52_prefix_13 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 13 232625496477532466 = some 250652842101268256 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 12 1 232625496477532466 250652842101268256 250652842101268256 endpoint_14_52_prefix_12 endpoint_14_52_window_12

def endpoint_14_52 : CertifiedEndpoint :=
  ⟨⟨14, 52, 2780⟩, 250652842101268256, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_52_flag endpoint_14_52_sources 13 232625496477532466 250652842101268256 rfl endpoint_14_52_base endpoint_14_52_prefix_13) (by decide)⟩
private def endpoint_14_53_flag : Flag := ⟨14, 53, 2739⟩
private def endpoint_14_53_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_14_53_base : receiptBase endpoint_14_53_flag endpoint_14_53_sources = some 233858313354692360 := by decide +kernel
private theorem endpoint_14_53_window_0 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 2 233858313354692360 = some 248628383292962505 := by decide +kernel
private theorem endpoint_14_53_window_2 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 2 2 248628383292962505 = some 248628383292962505 := by decide +kernel
private theorem endpoint_14_53_prefix_4 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 4 233858313354692360 = some 248628383292962505 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 2 2 233858313354692360 248628383292962505 248628383292962505 endpoint_14_53_window_0 endpoint_14_53_window_2
private theorem endpoint_14_53_window_4 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 4 2 248628383292962505 = some 248628383292962505 := by decide +kernel
private theorem endpoint_14_53_prefix_6 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 6 233858313354692360 = some 248628383292962505 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 4 2 233858313354692360 248628383292962505 248628383292962505 endpoint_14_53_prefix_4 endpoint_14_53_window_4
private theorem endpoint_14_53_window_6 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 6 2 248628383292962505 = some 248628383292962505 := by decide +kernel
private theorem endpoint_14_53_prefix_8 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 8 233858313354692360 = some 248628383292962505 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 6 2 233858313354692360 248628383292962505 248628383292962505 endpoint_14_53_prefix_6 endpoint_14_53_window_6
private theorem endpoint_14_53_window_8 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 8 2 248628383292962505 = some 248628383292962505 := by decide +kernel
private theorem endpoint_14_53_prefix_10 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 10 233858313354692360 = some 248628383292962505 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 8 2 233858313354692360 248628383292962505 248628383292962505 endpoint_14_53_prefix_8 endpoint_14_53_window_8
private theorem endpoint_14_53_window_10 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 10 2 248628383292962505 = some 248628383292962505 := by decide +kernel
private theorem endpoint_14_53_prefix_12 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 12 233858313354692360 = some 248628383292962505 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 10 2 233858313354692360 248628383292962505 248628383292962505 endpoint_14_53_prefix_10 endpoint_14_53_window_10
private theorem endpoint_14_53_window_12 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 12 1 248628383292962505 = some 248628383292962505 := by decide +kernel
private theorem endpoint_14_53_prefix_13 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 13 233858313354692360 = some 248628383292962505 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 12 1 233858313354692360 248628383292962505 248628383292962505 endpoint_14_53_prefix_12 endpoint_14_53_window_12

def endpoint_14_53 : CertifiedEndpoint :=
  ⟨⟨14, 53, 2739⟩, 248628383292962505, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_14_53_flag endpoint_14_53_sources 13 233858313354692360 248628383292962505 rfl endpoint_14_53_base endpoint_14_53_prefix_13) (by decide)⟩
private def endpoint_14_54_flag : Flag := ⟨14, 54, 2696⟩
private def endpoint_14_54_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_14_54_base : receiptBase endpoint_14_54_flag endpoint_14_54_sources = some 234011198208859167 := by decide +kernel
private theorem endpoint_14_54_window_0 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 2 234011198208859167 = some 251997490359574646 := by decide +kernel
private theorem endpoint_14_54_window_2 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 2 2 251997490359574646 = some 251997490359574646 := by decide +kernel
private theorem endpoint_14_54_prefix_4 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 4 234011198208859167 = some 251997490359574646 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 2 2 234011198208859167 251997490359574646 251997490359574646 endpoint_14_54_window_0 endpoint_14_54_window_2
private theorem endpoint_14_54_window_4 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 4 2 251997490359574646 = some 251997490359574646 := by decide +kernel
private theorem endpoint_14_54_prefix_6 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 6 234011198208859167 = some 251997490359574646 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 4 2 234011198208859167 251997490359574646 251997490359574646 endpoint_14_54_prefix_4 endpoint_14_54_window_4
private theorem endpoint_14_54_window_6 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 6 2 251997490359574646 = some 251997490359574646 := by decide +kernel
private theorem endpoint_14_54_prefix_8 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 8 234011198208859167 = some 251997490359574646 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 6 2 234011198208859167 251997490359574646 251997490359574646 endpoint_14_54_prefix_6 endpoint_14_54_window_6
private theorem endpoint_14_54_window_8 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 8 2 251997490359574646 = some 251997490359574646 := by decide +kernel
private theorem endpoint_14_54_prefix_10 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 10 234011198208859167 = some 251997490359574646 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 8 2 234011198208859167 251997490359574646 251997490359574646 endpoint_14_54_prefix_8 endpoint_14_54_window_8
private theorem endpoint_14_54_window_10 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 10 2 251997490359574646 = some 251997490359574646 := by decide +kernel
private theorem endpoint_14_54_prefix_12 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 12 234011198208859167 = some 251997490359574646 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 10 2 234011198208859167 251997490359574646 251997490359574646 endpoint_14_54_prefix_10 endpoint_14_54_window_10
private theorem endpoint_14_54_window_12 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 12 1 251997490359574646 = some 251997490359574646 := by decide +kernel
private theorem endpoint_14_54_prefix_13 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 13 234011198208859167 = some 251997490359574646 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 12 1 234011198208859167 251997490359574646 251997490359574646 endpoint_14_54_prefix_12 endpoint_14_54_window_12

def endpoint_14_54 : CertifiedEndpoint :=
  ⟨⟨14, 54, 2696⟩, 251997490359574646, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_14_54_flag endpoint_14_54_sources 13 234011198208859167 251997490359574646 rfl endpoint_14_54_base endpoint_14_54_prefix_13) (by decide)⟩
private def endpoint_14_55_flag : Flag := ⟨14, 55, 2652⟩
private def endpoint_14_55_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_14_55_base : receiptBase endpoint_14_55_flag endpoint_14_55_sources = some 233957027208339363 := by decide +kernel
private theorem endpoint_14_55_window_0 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 2 233957027208339363 = some 255223081749263670 := by decide +kernel
private theorem endpoint_14_55_window_2 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 2 2 255223081749263670 = some 255223081749263670 := by decide +kernel
private theorem endpoint_14_55_prefix_4 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 4 233957027208339363 = some 255223081749263670 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 2 2 233957027208339363 255223081749263670 255223081749263670 endpoint_14_55_window_0 endpoint_14_55_window_2
private theorem endpoint_14_55_window_4 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 4 2 255223081749263670 = some 255223081749263670 := by decide +kernel
private theorem endpoint_14_55_prefix_6 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 6 233957027208339363 = some 255223081749263670 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 4 2 233957027208339363 255223081749263670 255223081749263670 endpoint_14_55_prefix_4 endpoint_14_55_window_4
private theorem endpoint_14_55_window_6 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 6 2 255223081749263670 = some 255223081749263670 := by decide +kernel
private theorem endpoint_14_55_prefix_8 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 8 233957027208339363 = some 255223081749263670 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 6 2 233957027208339363 255223081749263670 255223081749263670 endpoint_14_55_prefix_6 endpoint_14_55_window_6
private theorem endpoint_14_55_window_8 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 8 2 255223081749263670 = some 255223081749263670 := by decide +kernel
private theorem endpoint_14_55_prefix_10 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 10 233957027208339363 = some 255223081749263670 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 8 2 233957027208339363 255223081749263670 255223081749263670 endpoint_14_55_prefix_8 endpoint_14_55_window_8
private theorem endpoint_14_55_window_10 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 10 2 255223081749263670 = some 255223081749263670 := by decide +kernel
private theorem endpoint_14_55_prefix_12 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 12 233957027208339363 = some 255223081749263670 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 10 2 233957027208339363 255223081749263670 255223081749263670 endpoint_14_55_prefix_10 endpoint_14_55_window_10
private theorem endpoint_14_55_window_12 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 12 1 255223081749263670 = some 255223081749263670 := by decide +kernel
private theorem endpoint_14_55_prefix_13 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 13 233957027208339363 = some 255223081749263670 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 12 1 233957027208339363 255223081749263670 255223081749263670 endpoint_14_55_prefix_12 endpoint_14_55_window_12

def endpoint_14_55 : CertifiedEndpoint :=
  ⟨⟨14, 55, 2652⟩, 255223081749263670, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_14_55_flag endpoint_14_55_sources 13 233957027208339363 255223081749263670 rfl endpoint_14_55_base endpoint_14_55_prefix_13) (by decide)⟩
private def endpoint_14_56_flag : Flag := ⟨14, 56, 2606⟩
private def endpoint_14_56_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_14_56_base : receiptBase endpoint_14_56_flag endpoint_14_56_sources = some 233603376050347801 := by decide +kernel
private theorem endpoint_14_56_window_0 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 2 233603376050347801 = some 258251511948629220 := by decide +kernel
private theorem endpoint_14_56_window_2 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 2 2 258251511948629220 = some 258251511948629220 := by decide +kernel
private theorem endpoint_14_56_prefix_4 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 4 233603376050347801 = some 258251511948629220 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 2 2 233603376050347801 258251511948629220 258251511948629220 endpoint_14_56_window_0 endpoint_14_56_window_2
private theorem endpoint_14_56_window_4 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 4 2 258251511948629220 = some 258251511948629220 := by decide +kernel
private theorem endpoint_14_56_prefix_6 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 6 233603376050347801 = some 258251511948629220 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 4 2 233603376050347801 258251511948629220 258251511948629220 endpoint_14_56_prefix_4 endpoint_14_56_window_4
private theorem endpoint_14_56_window_6 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 6 2 258251511948629220 = some 258251511948629220 := by decide +kernel
private theorem endpoint_14_56_prefix_8 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 8 233603376050347801 = some 258251511948629220 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 6 2 233603376050347801 258251511948629220 258251511948629220 endpoint_14_56_prefix_6 endpoint_14_56_window_6
private theorem endpoint_14_56_window_8 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 8 2 258251511948629220 = some 258251511948629220 := by decide +kernel
private theorem endpoint_14_56_prefix_10 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 10 233603376050347801 = some 258251511948629220 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 8 2 233603376050347801 258251511948629220 258251511948629220 endpoint_14_56_prefix_8 endpoint_14_56_window_8
private theorem endpoint_14_56_window_10 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 10 2 258251511948629220 = some 258251511948629220 := by decide +kernel
private theorem endpoint_14_56_prefix_12 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 12 233603376050347801 = some 258251511948629220 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 10 2 233603376050347801 258251511948629220 258251511948629220 endpoint_14_56_prefix_10 endpoint_14_56_window_10
private theorem endpoint_14_56_window_12 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 12 1 258251511948629220 = some 258251511948629220 := by decide +kernel
private theorem endpoint_14_56_prefix_13 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 13 233603376050347801 = some 258251511948629220 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 12 1 233603376050347801 258251511948629220 258251511948629220 endpoint_14_56_prefix_12 endpoint_14_56_window_12

def endpoint_14_56 : CertifiedEndpoint :=
  ⟨⟨14, 56, 2606⟩, 258251511948629220, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_14_56_flag endpoint_14_56_sources 13 233603376050347801 258251511948629220 rfl endpoint_14_56_base endpoint_14_56_prefix_13) (by decide)⟩
private def endpoint_14_57_flag : Flag := ⟨14, 57, 2559⟩
private def endpoint_14_57_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_14_57_base : receiptBase endpoint_14_57_flag endpoint_14_57_sources = some 233896070879758045 := by decide +kernel
private theorem endpoint_14_57_window_0 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 2 233896070879758045 = some 256952001476870764 := by decide +kernel
private theorem endpoint_14_57_window_2 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 2 2 256952001476870764 = some 256952001476870764 := by decide +kernel
private theorem endpoint_14_57_prefix_4 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 4 233896070879758045 = some 256952001476870764 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 2 2 233896070879758045 256952001476870764 256952001476870764 endpoint_14_57_window_0 endpoint_14_57_window_2
private theorem endpoint_14_57_window_4 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 4 2 256952001476870764 = some 256952001476870764 := by decide +kernel
private theorem endpoint_14_57_prefix_6 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 6 233896070879758045 = some 256952001476870764 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 4 2 233896070879758045 256952001476870764 256952001476870764 endpoint_14_57_prefix_4 endpoint_14_57_window_4
private theorem endpoint_14_57_window_6 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 6 2 256952001476870764 = some 256952001476870764 := by decide +kernel
private theorem endpoint_14_57_prefix_8 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 8 233896070879758045 = some 256952001476870764 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 6 2 233896070879758045 256952001476870764 256952001476870764 endpoint_14_57_prefix_6 endpoint_14_57_window_6
private theorem endpoint_14_57_window_8 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 8 2 256952001476870764 = some 256952001476870764 := by decide +kernel
private theorem endpoint_14_57_prefix_10 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 10 233896070879758045 = some 256952001476870764 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 8 2 233896070879758045 256952001476870764 256952001476870764 endpoint_14_57_prefix_8 endpoint_14_57_window_8
private theorem endpoint_14_57_window_10 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 10 2 256952001476870764 = some 256952001476870764 := by decide +kernel
private theorem endpoint_14_57_prefix_12 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 12 233896070879758045 = some 256952001476870764 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 10 2 233896070879758045 256952001476870764 256952001476870764 endpoint_14_57_prefix_10 endpoint_14_57_window_10
private theorem endpoint_14_57_window_12 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 12 1 256952001476870764 = some 256952001476870764 := by decide +kernel
private theorem endpoint_14_57_prefix_13 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 13 233896070879758045 = some 256952001476870764 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 12 1 233896070879758045 256952001476870764 256952001476870764 endpoint_14_57_prefix_12 endpoint_14_57_window_12

def endpoint_14_57 : CertifiedEndpoint :=
  ⟨⟨14, 57, 2559⟩, 256952001476870764, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_14_57_flag endpoint_14_57_sources 13 233896070879758045 256952001476870764 rfl endpoint_14_57_base endpoint_14_57_prefix_13) (by decide)⟩
private def endpoint_14_58_flag : Flag := ⟨14, 58, 2510⟩
private def endpoint_14_58_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_14_58_base : receiptBase endpoint_14_58_flag endpoint_14_58_sources = some 233915277327031227 := by decide +kernel
private theorem endpoint_14_58_window_0 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 2 233915277327031227 = some 256804739229827246 := by decide +kernel
private theorem endpoint_14_58_window_2 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 2 2 256804739229827246 = some 256804739229827246 := by decide +kernel
private theorem endpoint_14_58_prefix_4 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 4 233915277327031227 = some 256804739229827246 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 2 2 233915277327031227 256804739229827246 256804739229827246 endpoint_14_58_window_0 endpoint_14_58_window_2
private theorem endpoint_14_58_window_4 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 4 2 256804739229827246 = some 256804739229827246 := by decide +kernel
private theorem endpoint_14_58_prefix_6 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 6 233915277327031227 = some 256804739229827246 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 4 2 233915277327031227 256804739229827246 256804739229827246 endpoint_14_58_prefix_4 endpoint_14_58_window_4
private theorem endpoint_14_58_window_6 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 6 2 256804739229827246 = some 256804739229827246 := by decide +kernel
private theorem endpoint_14_58_prefix_8 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 8 233915277327031227 = some 256804739229827246 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 6 2 233915277327031227 256804739229827246 256804739229827246 endpoint_14_58_prefix_6 endpoint_14_58_window_6
private theorem endpoint_14_58_window_8 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 8 2 256804739229827246 = some 256804739229827246 := by decide +kernel
private theorem endpoint_14_58_prefix_10 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 10 233915277327031227 = some 256804739229827246 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 8 2 233915277327031227 256804739229827246 256804739229827246 endpoint_14_58_prefix_8 endpoint_14_58_window_8
private theorem endpoint_14_58_window_10 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 10 2 256804739229827246 = some 256804739229827246 := by decide +kernel
private theorem endpoint_14_58_prefix_12 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 12 233915277327031227 = some 256804739229827246 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 10 2 233915277327031227 256804739229827246 256804739229827246 endpoint_14_58_prefix_10 endpoint_14_58_window_10
private theorem endpoint_14_58_window_12 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 12 1 256804739229827246 = some 256804739229827246 := by decide +kernel
private theorem endpoint_14_58_prefix_13 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 13 233915277327031227 = some 256804739229827246 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 12 1 233915277327031227 256804739229827246 256804739229827246 endpoint_14_58_prefix_12 endpoint_14_58_window_12

def endpoint_14_58 : CertifiedEndpoint :=
  ⟨⟨14, 58, 2510⟩, 256804739229827246, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_14_58_flag endpoint_14_58_sources 13 233915277327031227 256804739229827246 rfl endpoint_14_58_base endpoint_14_58_prefix_13) (by decide)⟩
private def endpoint_14_59_flag : Flag := ⟨14, 59, 2460⟩
private def endpoint_14_59_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_59_base : receiptBase endpoint_14_59_flag endpoint_14_59_sources = some 233584489629247398 := by decide +kernel
private theorem endpoint_14_59_window_0 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 2 233584489629247398 = some 251485786120858449 := by decide +kernel
private theorem endpoint_14_59_window_2 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 2 2 251485786120858449 = some 251485786120858449 := by decide +kernel
private theorem endpoint_14_59_prefix_4 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 4 233584489629247398 = some 251485786120858449 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 2 2 233584489629247398 251485786120858449 251485786120858449 endpoint_14_59_window_0 endpoint_14_59_window_2
private theorem endpoint_14_59_window_4 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 4 2 251485786120858449 = some 251485786120858449 := by decide +kernel
private theorem endpoint_14_59_prefix_6 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 6 233584489629247398 = some 251485786120858449 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 4 2 233584489629247398 251485786120858449 251485786120858449 endpoint_14_59_prefix_4 endpoint_14_59_window_4
private theorem endpoint_14_59_window_6 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 6 2 251485786120858449 = some 251485786120858449 := by decide +kernel
private theorem endpoint_14_59_prefix_8 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 8 233584489629247398 = some 251485786120858449 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 6 2 233584489629247398 251485786120858449 251485786120858449 endpoint_14_59_prefix_6 endpoint_14_59_window_6
private theorem endpoint_14_59_window_8 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 8 2 251485786120858449 = some 251485786120858449 := by decide +kernel
private theorem endpoint_14_59_prefix_10 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 10 233584489629247398 = some 251485786120858449 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 8 2 233584489629247398 251485786120858449 251485786120858449 endpoint_14_59_prefix_8 endpoint_14_59_window_8
private theorem endpoint_14_59_window_10 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 10 2 251485786120858449 = some 251485786120858449 := by decide +kernel
private theorem endpoint_14_59_prefix_12 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 12 233584489629247398 = some 251485786120858449 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 10 2 233584489629247398 251485786120858449 251485786120858449 endpoint_14_59_prefix_10 endpoint_14_59_window_10
private theorem endpoint_14_59_window_12 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 12 1 251485786120858449 = some 251485786120858449 := by decide +kernel
private theorem endpoint_14_59_prefix_13 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 13 233584489629247398 = some 251485786120858449 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 12 1 233584489629247398 251485786120858449 251485786120858449 endpoint_14_59_prefix_12 endpoint_14_59_window_12

def endpoint_14_59 : CertifiedEndpoint :=
  ⟨⟨14, 59, 2460⟩, 251485786120858449, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_59_flag endpoint_14_59_sources 13 233584489629247398 251485786120858449 rfl endpoint_14_59_base endpoint_14_59_prefix_13) (by decide)⟩
private def endpoint_14_60_flag : Flag := ⟨14, 60, 2408⟩
private def endpoint_14_60_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_60_base : receiptBase endpoint_14_60_flag endpoint_14_60_sources = some 232135609952954637 := by decide +kernel
private theorem endpoint_14_60_window_0 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 2 232135609952954637 = some 253486756917178832 := by decide +kernel
private theorem endpoint_14_60_window_2 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 2 2 253486756917178832 = some 253486756917178832 := by decide +kernel
private theorem endpoint_14_60_prefix_4 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 4 232135609952954637 = some 253486756917178832 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 2 2 232135609952954637 253486756917178832 253486756917178832 endpoint_14_60_window_0 endpoint_14_60_window_2
private theorem endpoint_14_60_window_4 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 4 2 253486756917178832 = some 253486756917178832 := by decide +kernel
private theorem endpoint_14_60_prefix_6 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 6 232135609952954637 = some 253486756917178832 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 4 2 232135609952954637 253486756917178832 253486756917178832 endpoint_14_60_prefix_4 endpoint_14_60_window_4
private theorem endpoint_14_60_window_6 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 6 2 253486756917178832 = some 253486756917178832 := by decide +kernel
private theorem endpoint_14_60_prefix_8 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 8 232135609952954637 = some 253486756917178832 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 6 2 232135609952954637 253486756917178832 253486756917178832 endpoint_14_60_prefix_6 endpoint_14_60_window_6
private theorem endpoint_14_60_window_8 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 8 2 253486756917178832 = some 253486756917178832 := by decide +kernel
private theorem endpoint_14_60_prefix_10 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 10 232135609952954637 = some 253486756917178832 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 8 2 232135609952954637 253486756917178832 253486756917178832 endpoint_14_60_prefix_8 endpoint_14_60_window_8
private theorem endpoint_14_60_window_10 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 10 2 253486756917178832 = some 253486756917178832 := by decide +kernel
private theorem endpoint_14_60_prefix_12 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 12 232135609952954637 = some 253486756917178832 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 10 2 232135609952954637 253486756917178832 253486756917178832 endpoint_14_60_prefix_10 endpoint_14_60_window_10
private theorem endpoint_14_60_window_12 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 12 1 253486756917178832 = some 253486756917178832 := by decide +kernel
private theorem endpoint_14_60_prefix_13 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 13 232135609952954637 = some 253486756917178832 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 12 1 232135609952954637 253486756917178832 253486756917178832 endpoint_14_60_prefix_12 endpoint_14_60_window_12

def endpoint_14_60 : CertifiedEndpoint :=
  ⟨⟨14, 60, 2408⟩, 253486756917178832, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_60_flag endpoint_14_60_sources 13 232135609952954637 253486756917178832 rfl endpoint_14_60_base endpoint_14_60_prefix_13) (by decide)⟩
private def endpoint_14_61_flag : Flag := ⟨14, 61, 2354⟩
private def endpoint_14_61_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_61_base : receiptBase endpoint_14_61_flag endpoint_14_61_sources = some 230345988284763109 := by decide +kernel
private theorem endpoint_14_61_window_0 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 2 230345988284763109 = some 255263095218844439 := by decide +kernel
private theorem endpoint_14_61_window_2 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 2 2 255263095218844439 = some 255263095218844439 := by decide +kernel
private theorem endpoint_14_61_prefix_4 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 4 230345988284763109 = some 255263095218844439 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 2 2 230345988284763109 255263095218844439 255263095218844439 endpoint_14_61_window_0 endpoint_14_61_window_2
private theorem endpoint_14_61_window_4 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 4 2 255263095218844439 = some 255263095218844439 := by decide +kernel
private theorem endpoint_14_61_prefix_6 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 6 230345988284763109 = some 255263095218844439 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 4 2 230345988284763109 255263095218844439 255263095218844439 endpoint_14_61_prefix_4 endpoint_14_61_window_4
private theorem endpoint_14_61_window_6 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 6 2 255263095218844439 = some 255263095218844439 := by decide +kernel
private theorem endpoint_14_61_prefix_8 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 8 230345988284763109 = some 255263095218844439 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 6 2 230345988284763109 255263095218844439 255263095218844439 endpoint_14_61_prefix_6 endpoint_14_61_window_6
private theorem endpoint_14_61_window_8 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 8 2 255263095218844439 = some 255263095218844439 := by decide +kernel
private theorem endpoint_14_61_prefix_10 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 10 230345988284763109 = some 255263095218844439 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 8 2 230345988284763109 255263095218844439 255263095218844439 endpoint_14_61_prefix_8 endpoint_14_61_window_8
private theorem endpoint_14_61_window_10 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 10 2 255263095218844439 = some 255263095218844439 := by decide +kernel
private theorem endpoint_14_61_prefix_12 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 12 230345988284763109 = some 255263095218844439 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 10 2 230345988284763109 255263095218844439 255263095218844439 endpoint_14_61_prefix_10 endpoint_14_61_window_10
private theorem endpoint_14_61_window_12 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 12 1 255263095218844439 = some 255263095218844439 := by decide +kernel
private theorem endpoint_14_61_prefix_13 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 13 230345988284763109 = some 255263095218844439 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 12 1 230345988284763109 255263095218844439 255263095218844439 endpoint_14_61_prefix_12 endpoint_14_61_window_12

def endpoint_14_61 : CertifiedEndpoint :=
  ⟨⟨14, 61, 2354⟩, 255263095218844439, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_61_flag endpoint_14_61_sources 13 230345988284763109 255263095218844439 rfl endpoint_14_61_base endpoint_14_61_prefix_13) (by decide)⟩
private def endpoint_14_62_flag : Flag := ⟨14, 62, 2298⟩
private def endpoint_14_62_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_62_base : receiptBase endpoint_14_62_flag endpoint_14_62_sources = some 228207176011568595 := by decide +kernel
private theorem endpoint_14_62_window_0 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 2 228207176011568595 = some 256808461494086508 := by decide +kernel
private theorem endpoint_14_62_window_2 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 2 2 256808461494086508 = some 256808461494086508 := by decide +kernel
private theorem endpoint_14_62_prefix_4 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 4 228207176011568595 = some 256808461494086508 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 2 2 228207176011568595 256808461494086508 256808461494086508 endpoint_14_62_window_0 endpoint_14_62_window_2
private theorem endpoint_14_62_window_4 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 4 2 256808461494086508 = some 256808461494086508 := by decide +kernel
private theorem endpoint_14_62_prefix_6 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 6 228207176011568595 = some 256808461494086508 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 4 2 228207176011568595 256808461494086508 256808461494086508 endpoint_14_62_prefix_4 endpoint_14_62_window_4
private theorem endpoint_14_62_window_6 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 6 2 256808461494086508 = some 256808461494086508 := by decide +kernel
private theorem endpoint_14_62_prefix_8 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 8 228207176011568595 = some 256808461494086508 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 6 2 228207176011568595 256808461494086508 256808461494086508 endpoint_14_62_prefix_6 endpoint_14_62_window_6
private theorem endpoint_14_62_window_8 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 8 2 256808461494086508 = some 256808461494086508 := by decide +kernel
private theorem endpoint_14_62_prefix_10 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 10 228207176011568595 = some 256808461494086508 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 8 2 228207176011568595 256808461494086508 256808461494086508 endpoint_14_62_prefix_8 endpoint_14_62_window_8
private theorem endpoint_14_62_window_10 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 10 2 256808461494086508 = some 256808461494086508 := by decide +kernel
private theorem endpoint_14_62_prefix_12 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 12 228207176011568595 = some 256808461494086508 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 10 2 228207176011568595 256808461494086508 256808461494086508 endpoint_14_62_prefix_10 endpoint_14_62_window_10
private theorem endpoint_14_62_window_12 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 12 1 256808461494086508 = some 256808461494086508 := by decide +kernel
private theorem endpoint_14_62_prefix_13 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 13 228207176011568595 = some 256808461494086508 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 12 1 228207176011568595 256808461494086508 256808461494086508 endpoint_14_62_prefix_12 endpoint_14_62_window_12

def endpoint_14_62 : CertifiedEndpoint :=
  ⟨⟨14, 62, 2298⟩, 256808461494086508, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_62_flag endpoint_14_62_sources 13 228207176011568595 256808461494086508 rfl endpoint_14_62_base endpoint_14_62_prefix_13) (by decide)⟩
private def endpoint_14_63_flag : Flag := ⟨14, 63, 2240⟩
private def endpoint_14_63_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_63_base : receiptBase endpoint_14_63_flag endpoint_14_63_sources = some 231362629787754528 := by decide +kernel
private theorem endpoint_14_63_window_0 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 2 231362629787754528 = some 244543401796157804 := by decide +kernel
private theorem endpoint_14_63_window_2 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 2 2 244543401796157804 = some 244543401796157804 := by decide +kernel
private theorem endpoint_14_63_prefix_4 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 4 231362629787754528 = some 244543401796157804 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 2 2 231362629787754528 244543401796157804 244543401796157804 endpoint_14_63_window_0 endpoint_14_63_window_2
private theorem endpoint_14_63_window_4 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 4 2 244543401796157804 = some 244543401796157804 := by decide +kernel
private theorem endpoint_14_63_prefix_6 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 6 231362629787754528 = some 244543401796157804 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 4 2 231362629787754528 244543401796157804 244543401796157804 endpoint_14_63_prefix_4 endpoint_14_63_window_4
private theorem endpoint_14_63_window_6 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 6 2 244543401796157804 = some 244543401796157804 := by decide +kernel
private theorem endpoint_14_63_prefix_8 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 8 231362629787754528 = some 244543401796157804 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 6 2 231362629787754528 244543401796157804 244543401796157804 endpoint_14_63_prefix_6 endpoint_14_63_window_6
private theorem endpoint_14_63_window_8 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 8 2 244543401796157804 = some 244543401796157804 := by decide +kernel
private theorem endpoint_14_63_prefix_10 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 10 231362629787754528 = some 244543401796157804 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 8 2 231362629787754528 244543401796157804 244543401796157804 endpoint_14_63_prefix_8 endpoint_14_63_window_8
private theorem endpoint_14_63_window_10 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 10 2 244543401796157804 = some 244543401796157804 := by decide +kernel
private theorem endpoint_14_63_prefix_12 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 12 231362629787754528 = some 244543401796157804 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 10 2 231362629787754528 244543401796157804 244543401796157804 endpoint_14_63_prefix_10 endpoint_14_63_window_10
private theorem endpoint_14_63_window_12 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 12 1 244543401796157804 = some 244543401796157804 := by decide +kernel
private theorem endpoint_14_63_prefix_13 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 13 231362629787754528 = some 244543401796157804 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 12 1 231362629787754528 244543401796157804 244543401796157804 endpoint_14_63_prefix_12 endpoint_14_63_window_12

def endpoint_14_63 : CertifiedEndpoint :=
  ⟨⟨14, 63, 2240⟩, 244543401796157804, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_63_flag endpoint_14_63_sources 13 231362629787754528 244543401796157804 rfl endpoint_14_63_base endpoint_14_63_prefix_13) (by decide)⟩
private def endpoint_14_64_flag : Flag := ⟨14, 64, 2180⟩
private def endpoint_14_64_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_64_base : receiptBase endpoint_14_64_flag endpoint_14_64_sources = some 228470283599690419 := by decide +kernel
private theorem endpoint_14_64_window_0 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 2 228470283599690419 = some 245362221688377764 := by decide +kernel
private theorem endpoint_14_64_window_2 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 2 2 245362221688377764 = some 245362221688377764 := by decide +kernel
private theorem endpoint_14_64_prefix_4 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 4 228470283599690419 = some 245362221688377764 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 2 2 228470283599690419 245362221688377764 245362221688377764 endpoint_14_64_window_0 endpoint_14_64_window_2
private theorem endpoint_14_64_window_4 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 4 2 245362221688377764 = some 245362221688377764 := by decide +kernel
private theorem endpoint_14_64_prefix_6 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 6 228470283599690419 = some 245362221688377764 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 4 2 228470283599690419 245362221688377764 245362221688377764 endpoint_14_64_prefix_4 endpoint_14_64_window_4
private theorem endpoint_14_64_window_6 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 6 2 245362221688377764 = some 245362221688377764 := by decide +kernel
private theorem endpoint_14_64_prefix_8 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 8 228470283599690419 = some 245362221688377764 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 6 2 228470283599690419 245362221688377764 245362221688377764 endpoint_14_64_prefix_6 endpoint_14_64_window_6
private theorem endpoint_14_64_window_8 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 8 2 245362221688377764 = some 245362221688377764 := by decide +kernel
private theorem endpoint_14_64_prefix_10 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 10 228470283599690419 = some 245362221688377764 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 8 2 228470283599690419 245362221688377764 245362221688377764 endpoint_14_64_prefix_8 endpoint_14_64_window_8
private theorem endpoint_14_64_window_10 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 10 2 245362221688377764 = some 245362221688377764 := by decide +kernel
private theorem endpoint_14_64_prefix_12 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 12 228470283599690419 = some 245362221688377764 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 10 2 228470283599690419 245362221688377764 245362221688377764 endpoint_14_64_prefix_10 endpoint_14_64_window_10
private theorem endpoint_14_64_window_12 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 12 1 245362221688377764 = some 245362221688377764 := by decide +kernel
private theorem endpoint_14_64_prefix_13 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 13 228470283599690419 = some 245362221688377764 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 12 1 228470283599690419 245362221688377764 245362221688377764 endpoint_14_64_prefix_12 endpoint_14_64_window_12

def endpoint_14_64 : CertifiedEndpoint :=
  ⟨⟨14, 64, 2180⟩, 245362221688377764, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_64_flag endpoint_14_64_sources 13 228470283599690419 245362221688377764 rfl endpoint_14_64_base endpoint_14_64_prefix_13) (by decide)⟩
private def endpoint_14_65_flag : Flag := ⟨14, 65, 2118⟩
private def endpoint_14_65_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_65_base : receiptBase endpoint_14_65_flag endpoint_14_65_sources = some 225200328945362831 := by decide +kernel
private theorem endpoint_14_65_window_0 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 2 225200328945362831 = some 245931050958867900 := by decide +kernel
private theorem endpoint_14_65_window_2 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 2 2 245931050958867900 = some 245931050958867900 := by decide +kernel
private theorem endpoint_14_65_prefix_4 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 4 225200328945362831 = some 245931050958867900 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 2 2 225200328945362831 245931050958867900 245931050958867900 endpoint_14_65_window_0 endpoint_14_65_window_2
private theorem endpoint_14_65_window_4 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 4 2 245931050958867900 = some 245931050958867900 := by decide +kernel
private theorem endpoint_14_65_prefix_6 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 6 225200328945362831 = some 245931050958867900 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 4 2 225200328945362831 245931050958867900 245931050958867900 endpoint_14_65_prefix_4 endpoint_14_65_window_4
private theorem endpoint_14_65_window_6 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 6 2 245931050958867900 = some 245931050958867900 := by decide +kernel
private theorem endpoint_14_65_prefix_8 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 8 225200328945362831 = some 245931050958867900 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 6 2 225200328945362831 245931050958867900 245931050958867900 endpoint_14_65_prefix_6 endpoint_14_65_window_6
private theorem endpoint_14_65_window_8 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 8 2 245931050958867900 = some 245931050958867900 := by decide +kernel
private theorem endpoint_14_65_prefix_10 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 10 225200328945362831 = some 245931050958867900 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 8 2 225200328945362831 245931050958867900 245931050958867900 endpoint_14_65_prefix_8 endpoint_14_65_window_8
private theorem endpoint_14_65_window_10 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 10 2 245931050958867900 = some 245931050958867900 := by decide +kernel
private theorem endpoint_14_65_prefix_12 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 12 225200328945362831 = some 245931050958867900 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 10 2 225200328945362831 245931050958867900 245931050958867900 endpoint_14_65_prefix_10 endpoint_14_65_window_10
private theorem endpoint_14_65_window_12 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 12 1 245931050958867900 = some 245931050958867900 := by decide +kernel
private theorem endpoint_14_65_prefix_13 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 13 225200328945362831 = some 245931050958867900 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 12 1 225200328945362831 245931050958867900 245931050958867900 endpoint_14_65_prefix_12 endpoint_14_65_window_12

def endpoint_14_65 : CertifiedEndpoint :=
  ⟨⟨14, 65, 2118⟩, 245931050958867900, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_65_flag endpoint_14_65_sources 13 225200328945362831 245931050958867900 rfl endpoint_14_65_base endpoint_14_65_prefix_13) (by decide)⟩
private def endpoint_14_66_flag : Flag := ⟨14, 66, 2054⟩
private def endpoint_14_66_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_14_66_base : receiptBase endpoint_14_66_flag endpoint_14_66_sources = some 222611095683613216 := by decide +kernel
private theorem endpoint_14_66_window_0 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 2 222611095683613216 = some 233453316203487272 := by decide +kernel
private theorem endpoint_14_66_window_2 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 2 2 233453316203487272 = some 233453316203487272 := by decide +kernel
private theorem endpoint_14_66_prefix_4 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 4 222611095683613216 = some 233453316203487272 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 2 2 222611095683613216 233453316203487272 233453316203487272 endpoint_14_66_window_0 endpoint_14_66_window_2
private theorem endpoint_14_66_window_4 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 4 2 233453316203487272 = some 233453316203487272 := by decide +kernel
private theorem endpoint_14_66_prefix_6 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 6 222611095683613216 = some 233453316203487272 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 4 2 222611095683613216 233453316203487272 233453316203487272 endpoint_14_66_prefix_4 endpoint_14_66_window_4
private theorem endpoint_14_66_window_6 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 6 2 233453316203487272 = some 233453316203487272 := by decide +kernel
private theorem endpoint_14_66_prefix_8 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 8 222611095683613216 = some 233453316203487272 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 6 2 222611095683613216 233453316203487272 233453316203487272 endpoint_14_66_prefix_6 endpoint_14_66_window_6
private theorem endpoint_14_66_window_8 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 8 2 233453316203487272 = some 233453316203487272 := by decide +kernel
private theorem endpoint_14_66_prefix_10 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 10 222611095683613216 = some 233453316203487272 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 8 2 222611095683613216 233453316203487272 233453316203487272 endpoint_14_66_prefix_8 endpoint_14_66_window_8
private theorem endpoint_14_66_window_10 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 10 2 233453316203487272 = some 233453316203487272 := by decide +kernel
private theorem endpoint_14_66_prefix_12 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 12 222611095683613216 = some 233453316203487272 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 10 2 222611095683613216 233453316203487272 233453316203487272 endpoint_14_66_prefix_10 endpoint_14_66_window_10
private theorem endpoint_14_66_window_12 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 12 1 233453316203487272 = some 233453316203487272 := by decide +kernel
private theorem endpoint_14_66_prefix_13 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 13 222611095683613216 = some 233453316203487272 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 12 1 222611095683613216 233453316203487272 233453316203487272 endpoint_14_66_prefix_12 endpoint_14_66_window_12

def endpoint_14_66 : CertifiedEndpoint :=
  ⟨⟨14, 66, 2054⟩, 233453316203487272, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_14_66_flag endpoint_14_66_sources 13 222611095683613216 233453316203487272 rfl endpoint_14_66_base endpoint_14_66_prefix_13) (by decide)⟩
private def endpoint_14_67_flag : Flag := ⟨14, 67, 1987⟩
private def endpoint_14_67_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_14_67_base : receiptBase endpoint_14_67_flag endpoint_14_67_sources = some 218418858660028025 := by decide +kernel
private theorem endpoint_14_67_window_0 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 2 218418858660028025 = some 233221543366575982 := by decide +kernel
private theorem endpoint_14_67_window_2 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 2 2 233221543366575982 = some 233221543366575982 := by decide +kernel
private theorem endpoint_14_67_prefix_4 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 4 218418858660028025 = some 233221543366575982 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 2 2 218418858660028025 233221543366575982 233221543366575982 endpoint_14_67_window_0 endpoint_14_67_window_2
private theorem endpoint_14_67_window_4 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 4 2 233221543366575982 = some 233221543366575982 := by decide +kernel
private theorem endpoint_14_67_prefix_6 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 6 218418858660028025 = some 233221543366575982 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 4 2 218418858660028025 233221543366575982 233221543366575982 endpoint_14_67_prefix_4 endpoint_14_67_window_4
private theorem endpoint_14_67_window_6 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 6 2 233221543366575982 = some 233221543366575982 := by decide +kernel
private theorem endpoint_14_67_prefix_8 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 8 218418858660028025 = some 233221543366575982 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 6 2 218418858660028025 233221543366575982 233221543366575982 endpoint_14_67_prefix_6 endpoint_14_67_window_6
private theorem endpoint_14_67_window_8 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 8 2 233221543366575982 = some 233221543366575982 := by decide +kernel
private theorem endpoint_14_67_prefix_10 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 10 218418858660028025 = some 233221543366575982 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 8 2 218418858660028025 233221543366575982 233221543366575982 endpoint_14_67_prefix_8 endpoint_14_67_window_8
private theorem endpoint_14_67_window_10 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 10 2 233221543366575982 = some 233221543366575982 := by decide +kernel
private theorem endpoint_14_67_prefix_12 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 12 218418858660028025 = some 233221543366575982 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 10 2 218418858660028025 233221543366575982 233221543366575982 endpoint_14_67_prefix_10 endpoint_14_67_window_10
private theorem endpoint_14_67_window_12 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 12 1 233221543366575982 = some 233221543366575982 := by decide +kernel
private theorem endpoint_14_67_prefix_13 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 13 218418858660028025 = some 233221543366575982 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 12 1 218418858660028025 233221543366575982 233221543366575982 endpoint_14_67_prefix_12 endpoint_14_67_window_12

def endpoint_14_67 : CertifiedEndpoint :=
  ⟨⟨14, 67, 1987⟩, 233221543366575982, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_14_67_flag endpoint_14_67_sources 13 218418858660028025 233221543366575982 rfl endpoint_14_67_base endpoint_14_67_prefix_13) (by decide)⟩
private def endpoint_14_68_flag : Flag := ⟨14, 68, 1918⟩
private def endpoint_14_68_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_14_68_base : receiptBase endpoint_14_68_flag endpoint_14_68_sources = some 213763975346692631 := by decide +kernel
private theorem endpoint_14_68_window_0 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 2 213763975346692631 = some 232718648135372328 := by decide +kernel
private theorem endpoint_14_68_window_2 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 2 2 232718648135372328 = some 232718648135372328 := by decide +kernel
private theorem endpoint_14_68_prefix_4 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 4 213763975346692631 = some 232718648135372328 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 2 2 213763975346692631 232718648135372328 232718648135372328 endpoint_14_68_window_0 endpoint_14_68_window_2
private theorem endpoint_14_68_window_4 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 4 2 232718648135372328 = some 232718648135372328 := by decide +kernel
private theorem endpoint_14_68_prefix_6 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 6 213763975346692631 = some 232718648135372328 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 4 2 213763975346692631 232718648135372328 232718648135372328 endpoint_14_68_prefix_4 endpoint_14_68_window_4
private theorem endpoint_14_68_window_6 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 6 2 232718648135372328 = some 232718648135372328 := by decide +kernel
private theorem endpoint_14_68_prefix_8 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 8 213763975346692631 = some 232718648135372328 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 6 2 213763975346692631 232718648135372328 232718648135372328 endpoint_14_68_prefix_6 endpoint_14_68_window_6
private theorem endpoint_14_68_window_8 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 8 2 232718648135372328 = some 232718648135372328 := by decide +kernel
private theorem endpoint_14_68_prefix_10 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 10 213763975346692631 = some 232718648135372328 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 8 2 213763975346692631 232718648135372328 232718648135372328 endpoint_14_68_prefix_8 endpoint_14_68_window_8
private theorem endpoint_14_68_window_10 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 10 2 232718648135372328 = some 232718648135372328 := by decide +kernel
private theorem endpoint_14_68_prefix_12 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 12 213763975346692631 = some 232718648135372328 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 10 2 213763975346692631 232718648135372328 232718648135372328 endpoint_14_68_prefix_10 endpoint_14_68_window_10
private theorem endpoint_14_68_window_12 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 12 1 232718648135372328 = some 232718648135372328 := by decide +kernel
private theorem endpoint_14_68_prefix_13 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 13 213763975346692631 = some 232718648135372328 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 12 1 213763975346692631 232718648135372328 232718648135372328 endpoint_14_68_prefix_12 endpoint_14_68_window_12

def endpoint_14_68 : CertifiedEndpoint :=
  ⟨⟨14, 68, 1918⟩, 232718648135372328, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_14_68_flag endpoint_14_68_sources 13 213763975346692631 232718648135372328 rfl endpoint_14_68_base endpoint_14_68_prefix_13) (by decide)⟩
private def endpoint_14_69_flag : Flag := ⟨14, 69, 1846⟩
private def endpoint_14_69_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_14_69_base : receiptBase endpoint_14_69_flag endpoint_14_69_sources = some 209800655709989148 := by decide +kernel
private theorem endpoint_14_69_window_0 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 2 209800655709989148 = some 225216284523474171 := by decide +kernel
private theorem endpoint_14_69_window_2 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 2 2 225216284523474171 = some 225216284523474171 := by decide +kernel
private theorem endpoint_14_69_prefix_4 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 4 209800655709989148 = some 225216284523474171 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 2 2 209800655709989148 225216284523474171 225216284523474171 endpoint_14_69_window_0 endpoint_14_69_window_2
private theorem endpoint_14_69_window_4 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 4 2 225216284523474171 = some 225216284523474171 := by decide +kernel
private theorem endpoint_14_69_prefix_6 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 6 209800655709989148 = some 225216284523474171 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 4 2 209800655709989148 225216284523474171 225216284523474171 endpoint_14_69_prefix_4 endpoint_14_69_window_4
private theorem endpoint_14_69_window_6 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 6 2 225216284523474171 = some 225216284523474171 := by decide +kernel
private theorem endpoint_14_69_prefix_8 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 8 209800655709989148 = some 225216284523474171 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 6 2 209800655709989148 225216284523474171 225216284523474171 endpoint_14_69_prefix_6 endpoint_14_69_window_6
private theorem endpoint_14_69_window_8 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 8 2 225216284523474171 = some 225216284523474171 := by decide +kernel
private theorem endpoint_14_69_prefix_10 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 10 209800655709989148 = some 225216284523474171 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 8 2 209800655709989148 225216284523474171 225216284523474171 endpoint_14_69_prefix_8 endpoint_14_69_window_8
private theorem endpoint_14_69_window_10 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 10 2 225216284523474171 = some 225216284523474171 := by decide +kernel
private theorem endpoint_14_69_prefix_12 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 12 209800655709989148 = some 225216284523474171 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 10 2 209800655709989148 225216284523474171 225216284523474171 endpoint_14_69_prefix_10 endpoint_14_69_window_10
private theorem endpoint_14_69_window_12 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 12 1 225216284523474171 = some 225216284523474171 := by decide +kernel
private theorem endpoint_14_69_prefix_13 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 13 209800655709989148 = some 225216284523474171 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 12 1 209800655709989148 225216284523474171 225216284523474171 endpoint_14_69_prefix_12 endpoint_14_69_window_12

def endpoint_14_69 : CertifiedEndpoint :=
  ⟨⟨14, 69, 1846⟩, 225216284523474171, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_14_69_flag endpoint_14_69_sources 13 209800655709989148 225216284523474171 rfl endpoint_14_69_base endpoint_14_69_prefix_13) (by decide)⟩
private def endpoint_14_70_flag : Flag := ⟨14, 70, 1772⟩
private def endpoint_14_70_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_14_70_base : receiptBase endpoint_14_70_flag endpoint_14_70_sources = some 205506396678531428 := by decide +kernel
private theorem endpoint_14_70_window_0 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 2 205506396678531428 = some 208820264611458224 := by decide +kernel
private theorem endpoint_14_70_window_2 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 2 2 208820264611458224 = some 208820264611458224 := by decide +kernel
private theorem endpoint_14_70_prefix_4 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 4 205506396678531428 = some 208820264611458224 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 2 2 205506396678531428 208820264611458224 208820264611458224 endpoint_14_70_window_0 endpoint_14_70_window_2
private theorem endpoint_14_70_window_4 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 4 2 208820264611458224 = some 208820264611458224 := by decide +kernel
private theorem endpoint_14_70_prefix_6 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 6 205506396678531428 = some 208820264611458224 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 4 2 205506396678531428 208820264611458224 208820264611458224 endpoint_14_70_prefix_4 endpoint_14_70_window_4
private theorem endpoint_14_70_window_6 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 6 2 208820264611458224 = some 208820264611458224 := by decide +kernel
private theorem endpoint_14_70_prefix_8 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 8 205506396678531428 = some 208820264611458224 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 6 2 205506396678531428 208820264611458224 208820264611458224 endpoint_14_70_prefix_6 endpoint_14_70_window_6
private theorem endpoint_14_70_window_8 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 8 2 208820264611458224 = some 208820264611458224 := by decide +kernel
private theorem endpoint_14_70_prefix_10 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 10 205506396678531428 = some 208820264611458224 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 8 2 205506396678531428 208820264611458224 208820264611458224 endpoint_14_70_prefix_8 endpoint_14_70_window_8
private theorem endpoint_14_70_window_10 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 10 2 208820264611458224 = some 208820264611458224 := by decide +kernel
private theorem endpoint_14_70_prefix_12 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 12 205506396678531428 = some 208820264611458224 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 10 2 205506396678531428 208820264611458224 208820264611458224 endpoint_14_70_prefix_10 endpoint_14_70_window_10
private theorem endpoint_14_70_window_12 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 12 1 208820264611458224 = some 208820264611458224 := by decide +kernel
private theorem endpoint_14_70_prefix_13 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 13 205506396678531428 = some 208820264611458224 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 12 1 205506396678531428 208820264611458224 208820264611458224 endpoint_14_70_prefix_12 endpoint_14_70_window_12

def endpoint_14_70 : CertifiedEndpoint :=
  ⟨⟨14, 70, 1772⟩, 208820264611458224, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_14_70_flag endpoint_14_70_sources 13 205506396678531428 208820264611458224 rfl endpoint_14_70_base endpoint_14_70_prefix_13) (by decide)⟩
private def endpoint_14_71_flag : Flag := ⟨14, 71, 1696⟩
private def endpoint_14_71_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_14_71_base : receiptBase endpoint_14_71_flag endpoint_14_71_sources = some 200694435942826985 := by decide +kernel
private theorem endpoint_14_71_window_0 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 2 200694435942826985 = some 206082933844550982 := by decide +kernel
private theorem endpoint_14_71_window_2 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 2 2 206082933844550982 = some 206082933844550982 := by decide +kernel
private theorem endpoint_14_71_prefix_4 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 4 200694435942826985 = some 206082933844550982 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 2 2 200694435942826985 206082933844550982 206082933844550982 endpoint_14_71_window_0 endpoint_14_71_window_2
private theorem endpoint_14_71_window_4 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 4 2 206082933844550982 = some 206082933844550982 := by decide +kernel
private theorem endpoint_14_71_prefix_6 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 6 200694435942826985 = some 206082933844550982 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 4 2 200694435942826985 206082933844550982 206082933844550982 endpoint_14_71_prefix_4 endpoint_14_71_window_4
private theorem endpoint_14_71_window_6 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 6 2 206082933844550982 = some 206082933844550982 := by decide +kernel
private theorem endpoint_14_71_prefix_8 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 8 200694435942826985 = some 206082933844550982 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 6 2 200694435942826985 206082933844550982 206082933844550982 endpoint_14_71_prefix_6 endpoint_14_71_window_6
private theorem endpoint_14_71_window_8 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 8 2 206082933844550982 = some 206082933844550982 := by decide +kernel
private theorem endpoint_14_71_prefix_10 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 10 200694435942826985 = some 206082933844550982 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 8 2 200694435942826985 206082933844550982 206082933844550982 endpoint_14_71_prefix_8 endpoint_14_71_window_8
private theorem endpoint_14_71_window_10 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 10 2 206082933844550982 = some 206082933844550982 := by decide +kernel
private theorem endpoint_14_71_prefix_12 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 12 200694435942826985 = some 206082933844550982 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 10 2 200694435942826985 206082933844550982 206082933844550982 endpoint_14_71_prefix_10 endpoint_14_71_window_10
private theorem endpoint_14_71_window_12 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 12 1 206082933844550982 = some 206082933844550982 := by decide +kernel
private theorem endpoint_14_71_prefix_13 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 13 200694435942826985 = some 206082933844550982 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 12 1 200694435942826985 206082933844550982 206082933844550982 endpoint_14_71_prefix_12 endpoint_14_71_window_12

def endpoint_14_71 : CertifiedEndpoint :=
  ⟨⟨14, 71, 1696⟩, 206082933844550982, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_14_71_flag endpoint_14_71_sources 13 200694435942826985 206082933844550982 rfl endpoint_14_71_base endpoint_14_71_prefix_13) (by decide)⟩
private def endpoint_14_72_flag : Flag := ⟨14, 72, 1617⟩
private def endpoint_14_72_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_14_72_base : receiptBase endpoint_14_72_flag endpoint_14_72_sources = some 193823282726078891 := by decide +kernel
private theorem endpoint_14_72_window_0 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 2 193823282726078891 = some 203926932672864844 := by decide +kernel
private theorem endpoint_14_72_window_2 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 2 2 203926932672864844 = some 203926932672864844 := by decide +kernel
private theorem endpoint_14_72_prefix_4 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 4 193823282726078891 = some 203926932672864844 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 2 2 193823282726078891 203926932672864844 203926932672864844 endpoint_14_72_window_0 endpoint_14_72_window_2
private theorem endpoint_14_72_window_4 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 4 2 203926932672864844 = some 203926932672864844 := by decide +kernel
private theorem endpoint_14_72_prefix_6 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 6 193823282726078891 = some 203926932672864844 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 4 2 193823282726078891 203926932672864844 203926932672864844 endpoint_14_72_prefix_4 endpoint_14_72_window_4
private theorem endpoint_14_72_window_6 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 6 2 203926932672864844 = some 203926932672864844 := by decide +kernel
private theorem endpoint_14_72_prefix_8 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 8 193823282726078891 = some 203926932672864844 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 6 2 193823282726078891 203926932672864844 203926932672864844 endpoint_14_72_prefix_6 endpoint_14_72_window_6
private theorem endpoint_14_72_window_8 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 8 2 203926932672864844 = some 203926932672864844 := by decide +kernel
private theorem endpoint_14_72_prefix_10 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 10 193823282726078891 = some 203926932672864844 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 8 2 193823282726078891 203926932672864844 203926932672864844 endpoint_14_72_prefix_8 endpoint_14_72_window_8
private theorem endpoint_14_72_window_10 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 10 2 203926932672864844 = some 203926932672864844 := by decide +kernel
private theorem endpoint_14_72_prefix_12 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 12 193823282726078891 = some 203926932672864844 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 10 2 193823282726078891 203926932672864844 203926932672864844 endpoint_14_72_prefix_10 endpoint_14_72_window_10
private theorem endpoint_14_72_window_12 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 12 1 203926932672864844 = some 203926932672864844 := by decide +kernel
private theorem endpoint_14_72_prefix_13 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 13 193823282726078891 = some 203926932672864844 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 12 1 193823282726078891 203926932672864844 203926932672864844 endpoint_14_72_prefix_12 endpoint_14_72_window_12

def endpoint_14_72 : CertifiedEndpoint :=
  ⟨⟨14, 72, 1617⟩, 203926932672864844, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_14_72_flag endpoint_14_72_sources 13 193823282726078891 203926932672864844 rfl endpoint_14_72_base endpoint_14_72_prefix_13) (by decide)⟩
private def endpoint_14_73_flag : Flag := ⟨14, 73, 1536⟩
private def endpoint_14_73_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_14_73_base : receiptBase endpoint_14_73_flag endpoint_14_73_sources = some 187962570743418982 := by decide +kernel
private theorem endpoint_14_73_window_0 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 2 187962570743418982 = some 187962570743418982 := by decide +kernel
private theorem endpoint_14_73_window_2 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 2 2 187962570743418982 = some 187962570743418982 := by decide +kernel
private theorem endpoint_14_73_prefix_4 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 4 187962570743418982 = some 187962570743418982 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 2 2 187962570743418982 187962570743418982 187962570743418982 endpoint_14_73_window_0 endpoint_14_73_window_2
private theorem endpoint_14_73_window_4 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 4 2 187962570743418982 = some 187962570743418982 := by decide +kernel
private theorem endpoint_14_73_prefix_6 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 6 187962570743418982 = some 187962570743418982 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 4 2 187962570743418982 187962570743418982 187962570743418982 endpoint_14_73_prefix_4 endpoint_14_73_window_4
private theorem endpoint_14_73_window_6 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 6 2 187962570743418982 = some 187962570743418982 := by decide +kernel
private theorem endpoint_14_73_prefix_8 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 8 187962570743418982 = some 187962570743418982 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 6 2 187962570743418982 187962570743418982 187962570743418982 endpoint_14_73_prefix_6 endpoint_14_73_window_6
private theorem endpoint_14_73_window_8 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 8 2 187962570743418982 = some 187962570743418982 := by decide +kernel
private theorem endpoint_14_73_prefix_10 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 10 187962570743418982 = some 187962570743418982 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 8 2 187962570743418982 187962570743418982 187962570743418982 endpoint_14_73_prefix_8 endpoint_14_73_window_8
private theorem endpoint_14_73_window_10 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 10 2 187962570743418982 = some 187962570743418982 := by decide +kernel
private theorem endpoint_14_73_prefix_12 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 12 187962570743418982 = some 187962570743418982 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 10 2 187962570743418982 187962570743418982 187962570743418982 endpoint_14_73_prefix_10 endpoint_14_73_window_10
private theorem endpoint_14_73_window_12 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 12 1 187962570743418982 = some 187962570743418982 := by decide +kernel
private theorem endpoint_14_73_prefix_13 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 13 187962570743418982 = some 187962570743418982 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 12 1 187962570743418982 187962570743418982 187962570743418982 endpoint_14_73_prefix_12 endpoint_14_73_window_12

def endpoint_14_73 : CertifiedEndpoint :=
  ⟨⟨14, 73, 1536⟩, 187962570743418982, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_14_73_flag endpoint_14_73_sources 13 187962570743418982 187962570743418982 rfl endpoint_14_73_base endpoint_14_73_prefix_13) (by decide)⟩
private def endpoint_14_74_flag : Flag := ⟨14, 74, 1452⟩
private def endpoint_14_74_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_14_74_base : receiptBase endpoint_14_74_flag endpoint_14_74_sources = some 179934021917632992 := by decide +kernel
private theorem endpoint_14_74_window_0 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 2 179934021917632992 = some 183639623675781978 := by decide +kernel
private theorem endpoint_14_74_window_2 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 2 2 183639623675781978 = some 183639623675781978 := by decide +kernel
private theorem endpoint_14_74_prefix_4 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 4 179934021917632992 = some 183639623675781978 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 2 2 179934021917632992 183639623675781978 183639623675781978 endpoint_14_74_window_0 endpoint_14_74_window_2
private theorem endpoint_14_74_window_4 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 4 2 183639623675781978 = some 183639623675781978 := by decide +kernel
private theorem endpoint_14_74_prefix_6 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 6 179934021917632992 = some 183639623675781978 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 4 2 179934021917632992 183639623675781978 183639623675781978 endpoint_14_74_prefix_4 endpoint_14_74_window_4
private theorem endpoint_14_74_window_6 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 6 2 183639623675781978 = some 183639623675781978 := by decide +kernel
private theorem endpoint_14_74_prefix_8 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 8 179934021917632992 = some 183639623675781978 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 6 2 179934021917632992 183639623675781978 183639623675781978 endpoint_14_74_prefix_6 endpoint_14_74_window_6
private theorem endpoint_14_74_window_8 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 8 2 183639623675781978 = some 183639623675781978 := by decide +kernel
private theorem endpoint_14_74_prefix_10 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 10 179934021917632992 = some 183639623675781978 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 8 2 179934021917632992 183639623675781978 183639623675781978 endpoint_14_74_prefix_8 endpoint_14_74_window_8
private theorem endpoint_14_74_window_10 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 10 2 183639623675781978 = some 183639623675781978 := by decide +kernel
private theorem endpoint_14_74_prefix_12 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 12 179934021917632992 = some 183639623675781978 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 10 2 179934021917632992 183639623675781978 183639623675781978 endpoint_14_74_prefix_10 endpoint_14_74_window_10
private theorem endpoint_14_74_window_12 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 12 1 183639623675781978 = some 183639623675781978 := by decide +kernel
private theorem endpoint_14_74_prefix_13 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 13 179934021917632992 = some 183639623675781978 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 12 1 179934021917632992 183639623675781978 183639623675781978 endpoint_14_74_prefix_12 endpoint_14_74_window_12

def endpoint_14_74 : CertifiedEndpoint :=
  ⟨⟨14, 74, 1452⟩, 183639623675781978, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_14_74_flag endpoint_14_74_sources 13 179934021917632992 183639623675781978 rfl endpoint_14_74_base endpoint_14_74_prefix_13) (by decide)⟩
private def endpoint_14_75_flag : Flag := ⟨14, 75, 1365⟩
private def endpoint_14_75_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_14_75_base : receiptBase endpoint_14_75_flag endpoint_14_75_sources = some 171281523656756219 := by decide +kernel
private theorem endpoint_14_75_window_0 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 2 171281523656756219 = some 180175282265939827 := by decide +kernel
private theorem endpoint_14_75_window_2 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 2 2 180175282265939827 = some 180175282265939827 := by decide +kernel
private theorem endpoint_14_75_prefix_4 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 4 171281523656756219 = some 180175282265939827 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 2 2 171281523656756219 180175282265939827 180175282265939827 endpoint_14_75_window_0 endpoint_14_75_window_2
private theorem endpoint_14_75_window_4 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 4 2 180175282265939827 = some 180175282265939827 := by decide +kernel
private theorem endpoint_14_75_prefix_6 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 6 171281523656756219 = some 180175282265939827 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 4 2 171281523656756219 180175282265939827 180175282265939827 endpoint_14_75_prefix_4 endpoint_14_75_window_4
private theorem endpoint_14_75_window_6 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 6 2 180175282265939827 = some 180175282265939827 := by decide +kernel
private theorem endpoint_14_75_prefix_8 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 8 171281523656756219 = some 180175282265939827 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 6 2 171281523656756219 180175282265939827 180175282265939827 endpoint_14_75_prefix_6 endpoint_14_75_window_6
private theorem endpoint_14_75_window_8 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 8 2 180175282265939827 = some 180175282265939827 := by decide +kernel
private theorem endpoint_14_75_prefix_10 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 10 171281523656756219 = some 180175282265939827 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 8 2 171281523656756219 180175282265939827 180175282265939827 endpoint_14_75_prefix_8 endpoint_14_75_window_8
private theorem endpoint_14_75_window_10 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 10 2 180175282265939827 = some 180175282265939827 := by decide +kernel
private theorem endpoint_14_75_prefix_12 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 12 171281523656756219 = some 180175282265939827 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 10 2 171281523656756219 180175282265939827 180175282265939827 endpoint_14_75_prefix_10 endpoint_14_75_window_10
private theorem endpoint_14_75_window_12 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 12 1 180175282265939827 = some 180175282265939827 := by decide +kernel
private theorem endpoint_14_75_prefix_13 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 13 171281523656756219 = some 180175282265939827 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 12 1 171281523656756219 180175282265939827 180175282265939827 endpoint_14_75_prefix_12 endpoint_14_75_window_12

def endpoint_14_75 : CertifiedEndpoint :=
  ⟨⟨14, 75, 1365⟩, 180175282265939827, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_14_75_flag endpoint_14_75_sources 13 171281523656756219 180175282265939827 rfl endpoint_14_75_base endpoint_14_75_prefix_13) (by decide)⟩
private def endpoint_14_76_flag : Flag := ⟨14, 76, 1276⟩
private def endpoint_14_76_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_14_76_base : receiptBase endpoint_14_76_flag endpoint_14_76_sources = some 163502144682388635 := by decide +kernel
private theorem endpoint_14_76_window_0 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 2 163502144682388635 = some 165994815801470440 := by decide +kernel
private theorem endpoint_14_76_window_2 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 2 2 165994815801470440 = some 165994815801470440 := by decide +kernel
private theorem endpoint_14_76_prefix_4 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 4 163502144682388635 = some 165994815801470440 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 2 2 163502144682388635 165994815801470440 165994815801470440 endpoint_14_76_window_0 endpoint_14_76_window_2
private theorem endpoint_14_76_window_4 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 4 2 165994815801470440 = some 165994815801470440 := by decide +kernel
private theorem endpoint_14_76_prefix_6 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 6 163502144682388635 = some 165994815801470440 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 4 2 163502144682388635 165994815801470440 165994815801470440 endpoint_14_76_prefix_4 endpoint_14_76_window_4
private theorem endpoint_14_76_window_6 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 6 2 165994815801470440 = some 165994815801470440 := by decide +kernel
private theorem endpoint_14_76_prefix_8 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 8 163502144682388635 = some 165994815801470440 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 6 2 163502144682388635 165994815801470440 165994815801470440 endpoint_14_76_prefix_6 endpoint_14_76_window_6
private theorem endpoint_14_76_window_8 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 8 2 165994815801470440 = some 165994815801470440 := by decide +kernel
private theorem endpoint_14_76_prefix_10 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 10 163502144682388635 = some 165994815801470440 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 8 2 163502144682388635 165994815801470440 165994815801470440 endpoint_14_76_prefix_8 endpoint_14_76_window_8
private theorem endpoint_14_76_window_10 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 10 2 165994815801470440 = some 165994815801470440 := by decide +kernel
private theorem endpoint_14_76_prefix_12 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 12 163502144682388635 = some 165994815801470440 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 10 2 163502144682388635 165994815801470440 165994815801470440 endpoint_14_76_prefix_10 endpoint_14_76_window_10
private theorem endpoint_14_76_window_12 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 12 1 165994815801470440 = some 165994815801470440 := by decide +kernel
private theorem endpoint_14_76_prefix_13 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 13 163502144682388635 = some 165994815801470440 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 12 1 163502144682388635 165994815801470440 165994815801470440 endpoint_14_76_prefix_12 endpoint_14_76_window_12

def endpoint_14_76 : CertifiedEndpoint :=
  ⟨⟨14, 76, 1276⟩, 165994815801470440, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_14_76_flag endpoint_14_76_sources 13 163502144682388635 165994815801470440 rfl endpoint_14_76_base endpoint_14_76_prefix_13) (by decide)⟩
private def endpoint_14_77_flag : Flag := ⟨14, 77, 1185⟩
private def endpoint_14_77_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_14_77_base : receiptBase endpoint_14_77_flag endpoint_14_77_sources = some 153773691427896874 := by decide +kernel
private theorem endpoint_14_77_window_0 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 2 153773691427896874 = some 161711420627749245 := by decide +kernel
private theorem endpoint_14_77_window_2 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 2 2 161711420627749245 = some 161711420627749245 := by decide +kernel
private theorem endpoint_14_77_prefix_4 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 4 153773691427896874 = some 161711420627749245 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 2 2 153773691427896874 161711420627749245 161711420627749245 endpoint_14_77_window_0 endpoint_14_77_window_2
private theorem endpoint_14_77_window_4 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 4 2 161711420627749245 = some 161711420627749245 := by decide +kernel
private theorem endpoint_14_77_prefix_6 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 6 153773691427896874 = some 161711420627749245 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 4 2 153773691427896874 161711420627749245 161711420627749245 endpoint_14_77_prefix_4 endpoint_14_77_window_4
private theorem endpoint_14_77_window_6 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 6 2 161711420627749245 = some 161711420627749245 := by decide +kernel
private theorem endpoint_14_77_prefix_8 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 8 153773691427896874 = some 161711420627749245 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 6 2 153773691427896874 161711420627749245 161711420627749245 endpoint_14_77_prefix_6 endpoint_14_77_window_6
private theorem endpoint_14_77_window_8 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 8 2 161711420627749245 = some 161711420627749245 := by decide +kernel
private theorem endpoint_14_77_prefix_10 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 10 153773691427896874 = some 161711420627749245 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 8 2 153773691427896874 161711420627749245 161711420627749245 endpoint_14_77_prefix_8 endpoint_14_77_window_8
private theorem endpoint_14_77_window_10 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 10 2 161711420627749245 = some 161711420627749245 := by decide +kernel
private theorem endpoint_14_77_prefix_12 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 12 153773691427896874 = some 161711420627749245 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 10 2 153773691427896874 161711420627749245 161711420627749245 endpoint_14_77_prefix_10 endpoint_14_77_window_10
private theorem endpoint_14_77_window_12 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 12 1 161711420627749245 = some 161711420627749245 := by decide +kernel
private theorem endpoint_14_77_prefix_13 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 13 153773691427896874 = some 161711420627749245 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 12 1 153773691427896874 161711420627749245 161711420627749245 endpoint_14_77_prefix_12 endpoint_14_77_window_12

def endpoint_14_77 : CertifiedEndpoint :=
  ⟨⟨14, 77, 1185⟩, 161711420627749245, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_14_77_flag endpoint_14_77_sources 13 153773691427896874 161711420627749245 rfl endpoint_14_77_base endpoint_14_77_prefix_13) (by decide)⟩
private def endpoint_14_78_flag : Flag := ⟨14, 78, 1090⟩
private def endpoint_14_78_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_14_78_base : receiptBase endpoint_14_78_flag endpoint_14_78_sources = some 144327088372159101 := by decide +kernel
private theorem endpoint_14_78_window_0 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 2 144327088372159101 = some 147927389250366156 := by decide +kernel
private theorem endpoint_14_78_window_2 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 2 2 147927389250366156 = some 147927389250366156 := by decide +kernel
private theorem endpoint_14_78_prefix_4 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 4 144327088372159101 = some 147927389250366156 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 2 2 144327088372159101 147927389250366156 147927389250366156 endpoint_14_78_window_0 endpoint_14_78_window_2
private theorem endpoint_14_78_window_4 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 4 2 147927389250366156 = some 147927389250366156 := by decide +kernel
private theorem endpoint_14_78_prefix_6 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 6 144327088372159101 = some 147927389250366156 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 4 2 144327088372159101 147927389250366156 147927389250366156 endpoint_14_78_prefix_4 endpoint_14_78_window_4
private theorem endpoint_14_78_window_6 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 6 2 147927389250366156 = some 147927389250366156 := by decide +kernel
private theorem endpoint_14_78_prefix_8 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 8 144327088372159101 = some 147927389250366156 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 6 2 144327088372159101 147927389250366156 147927389250366156 endpoint_14_78_prefix_6 endpoint_14_78_window_6
private theorem endpoint_14_78_window_8 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 8 2 147927389250366156 = some 147927389250366156 := by decide +kernel
private theorem endpoint_14_78_prefix_10 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 10 144327088372159101 = some 147927389250366156 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 8 2 144327088372159101 147927389250366156 147927389250366156 endpoint_14_78_prefix_8 endpoint_14_78_window_8
private theorem endpoint_14_78_window_10 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 10 2 147927389250366156 = some 147927389250366156 := by decide +kernel
private theorem endpoint_14_78_prefix_12 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 12 144327088372159101 = some 147927389250366156 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 10 2 144327088372159101 147927389250366156 147927389250366156 endpoint_14_78_prefix_10 endpoint_14_78_window_10
private theorem endpoint_14_78_window_12 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 12 1 147927389250366156 = some 147927389250366156 := by decide +kernel
private theorem endpoint_14_78_prefix_13 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 13 144327088372159101 = some 147927389250366156 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 12 1 144327088372159101 147927389250366156 147927389250366156 endpoint_14_78_prefix_12 endpoint_14_78_window_12

def endpoint_14_78 : CertifiedEndpoint :=
  ⟨⟨14, 78, 1090⟩, 147927389250366156, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_14_78_flag endpoint_14_78_sources 13 144327088372159101 147927389250366156 rfl endpoint_14_78_base endpoint_14_78_prefix_13) (by decide)⟩
def endpoint_14_79 : CertifiedEndpoint :=
  ⟨⟨14, 79, 993⟩, 236867983841542230, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_80 : CertifiedEndpoint :=
  ⟨⟨14, 80, 894⟩, 215020800993295026, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_81 : CertifiedEndpoint :=
  ⟨⟨14, 81, 792⟩, 191710543912693057, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_82 : CertifiedEndpoint :=
  ⟨⟨14, 82, 687⟩, 166905824196625941, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_83 : CertifiedEndpoint :=
  ⟨⟨14, 83, 579⟩, 140575253441983296, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_84 : CertifiedEndpoint :=
  ⟨⟨14, 84, 469⟩, 112954253301218455, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_85 : CertifiedEndpoint :=
  ⟨⟨14, 85, 357⟩, 84021898172257830, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_86 : CertifiedEndpoint :=
  ⟨⟨14, 86, 241⟩, 53209691940518011, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_87 : CertifiedEndpoint :=
  ⟨⟨14, 87, 123⟩, 21030329115052840, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_15 : CertifiedEndpoint :=
  ⟨⟨15, 15, 3701⟩, 115345004629661826, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_16 : CertifiedEndpoint :=
  ⟨⟨15, 16, 3678⟩, 119123175370757998, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_17 : CertifiedEndpoint :=
  ⟨⟨15, 17, 3656⟩, 122878556476213791, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_18 : CertifiedEndpoint :=
  ⟨⟨15, 18, 3634⟩, 135681690604430614, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_19 : CertifiedEndpoint :=
  ⟨⟨15, 19, 3611⟩, 148275079038912296, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_20 : CertifiedEndpoint :=
  ⟨⟨15, 20, 3588⟩, 160692438153676028, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_21 : CertifiedEndpoint :=
  ⟨⟨15, 21, 3564⟩, 172885070356005219, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_22 : CertifiedEndpoint :=
  ⟨⟨15, 22, 3540⟩, 184894182629266760, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_23 : CertifiedEndpoint :=
  ⟨⟨15, 23, 3516⟩, 196719774973460651, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_24 : CertifiedEndpoint :=
  ⟨⟨15, 24, 3492⟩, 208361847388586892, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_25 : CertifiedEndpoint :=
  ⟨⟨15, 25, 3467⟩, 219756721063229492, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_26 : CertifiedEndpoint :=
  ⟨⟨15, 26, 3442⟩, 230960584199454742, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_27 : CertifiedEndpoint :=
  ⟨⟨15, 27, 3416⟩, 241902267376496951, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_28 : CertifiedEndpoint :=
  ⟨⟨15, 28, 3391⟩, 252720364131212651, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_15_29_flag : Flag := ⟨15, 29, 3364⟩
private def endpoint_15_29_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_29_base : receiptBase endpoint_15_29_flag endpoint_15_29_sources = some 177038708943085483 := by decide +kernel
private theorem endpoint_15_29_window_0 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 2 177038708943085483 = some 177038708943085483 := by decide +kernel
private theorem endpoint_15_29_window_2 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 2 2 177038708943085483 = some 177038708943085483 := by decide +kernel
private theorem endpoint_15_29_prefix_4 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 4 177038708943085483 = some 177038708943085483 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 2 2 177038708943085483 177038708943085483 177038708943085483 endpoint_15_29_window_0 endpoint_15_29_window_2
private theorem endpoint_15_29_window_4 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 4 2 177038708943085483 = some 177038708943085483 := by decide +kernel
private theorem endpoint_15_29_prefix_6 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 6 177038708943085483 = some 177038708943085483 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 4 2 177038708943085483 177038708943085483 177038708943085483 endpoint_15_29_prefix_4 endpoint_15_29_window_4
private theorem endpoint_15_29_window_6 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 6 2 177038708943085483 = some 177038708943085483 := by decide +kernel
private theorem endpoint_15_29_prefix_8 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 8 177038708943085483 = some 177038708943085483 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 6 2 177038708943085483 177038708943085483 177038708943085483 endpoint_15_29_prefix_6 endpoint_15_29_window_6
private theorem endpoint_15_29_window_8 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 8 2 177038708943085483 = some 177038708943085483 := by decide +kernel
private theorem endpoint_15_29_prefix_10 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 10 177038708943085483 = some 177038708943085483 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 8 2 177038708943085483 177038708943085483 177038708943085483 endpoint_15_29_prefix_8 endpoint_15_29_window_8
private theorem endpoint_15_29_window_10 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 10 2 177038708943085483 = some 177038708943085483 := by decide +kernel
private theorem endpoint_15_29_prefix_12 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 12 177038708943085483 = some 177038708943085483 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 10 2 177038708943085483 177038708943085483 177038708943085483 endpoint_15_29_prefix_10 endpoint_15_29_window_10
private theorem endpoint_15_29_window_12 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 12 2 177038708943085483 = some 177038708943085483 := by decide +kernel
private theorem endpoint_15_29_prefix_14 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 14 177038708943085483 = some 177038708943085483 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 12 2 177038708943085483 177038708943085483 177038708943085483 endpoint_15_29_prefix_12 endpoint_15_29_window_12

def endpoint_15_29 : CertifiedEndpoint :=
  ⟨⟨15, 29, 3364⟩, 177038708943085483, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_29_flag endpoint_15_29_sources 14 177038708943085483 177038708943085483 rfl endpoint_15_29_base endpoint_15_29_prefix_14) (by decide)⟩
private def endpoint_15_30_flag : Flag := ⟨15, 30, 3338⟩
private def endpoint_15_30_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_30_base : receiptBase endpoint_15_30_flag endpoint_15_30_sources = some 180656014374838473 := by decide +kernel
private theorem endpoint_15_30_window_0 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 2 180656014374838473 = some 180656014374838473 := by decide +kernel
private theorem endpoint_15_30_window_2 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 2 2 180656014374838473 = some 180656014374838473 := by decide +kernel
private theorem endpoint_15_30_prefix_4 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 4 180656014374838473 = some 180656014374838473 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 2 2 180656014374838473 180656014374838473 180656014374838473 endpoint_15_30_window_0 endpoint_15_30_window_2
private theorem endpoint_15_30_window_4 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 4 2 180656014374838473 = some 180656014374838473 := by decide +kernel
private theorem endpoint_15_30_prefix_6 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 6 180656014374838473 = some 180656014374838473 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 4 2 180656014374838473 180656014374838473 180656014374838473 endpoint_15_30_prefix_4 endpoint_15_30_window_4
private theorem endpoint_15_30_window_6 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 6 2 180656014374838473 = some 180656014374838473 := by decide +kernel
private theorem endpoint_15_30_prefix_8 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 8 180656014374838473 = some 180656014374838473 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 6 2 180656014374838473 180656014374838473 180656014374838473 endpoint_15_30_prefix_6 endpoint_15_30_window_6
private theorem endpoint_15_30_window_8 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 8 2 180656014374838473 = some 180656014374838473 := by decide +kernel
private theorem endpoint_15_30_prefix_10 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 10 180656014374838473 = some 180656014374838473 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 8 2 180656014374838473 180656014374838473 180656014374838473 endpoint_15_30_prefix_8 endpoint_15_30_window_8
private theorem endpoint_15_30_window_10 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 10 2 180656014374838473 = some 180656014374838473 := by decide +kernel
private theorem endpoint_15_30_prefix_12 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 12 180656014374838473 = some 180656014374838473 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 10 2 180656014374838473 180656014374838473 180656014374838473 endpoint_15_30_prefix_10 endpoint_15_30_window_10
private theorem endpoint_15_30_window_12 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 12 2 180656014374838473 = some 180656014374838473 := by decide +kernel
private theorem endpoint_15_30_prefix_14 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 14 180656014374838473 = some 180656014374838473 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 12 2 180656014374838473 180656014374838473 180656014374838473 endpoint_15_30_prefix_12 endpoint_15_30_window_12

def endpoint_15_30 : CertifiedEndpoint :=
  ⟨⟨15, 30, 3338⟩, 180656014374838473, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_30_flag endpoint_15_30_sources 14 180656014374838473 180656014374838473 rfl endpoint_15_30_base endpoint_15_30_prefix_14) (by decide)⟩
private def endpoint_15_31_flag : Flag := ⟨15, 31, 3310⟩
private def endpoint_15_31_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_31_base : receiptBase endpoint_15_31_flag endpoint_15_31_sources = some 184086513643411531 := by decide +kernel
private theorem endpoint_15_31_window_0 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 2 184086513643411531 = some 184086513643411531 := by decide +kernel
private theorem endpoint_15_31_window_2 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 2 2 184086513643411531 = some 184086513643411531 := by decide +kernel
private theorem endpoint_15_31_prefix_4 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 4 184086513643411531 = some 184086513643411531 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 2 2 184086513643411531 184086513643411531 184086513643411531 endpoint_15_31_window_0 endpoint_15_31_window_2
private theorem endpoint_15_31_window_4 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 4 2 184086513643411531 = some 184086513643411531 := by decide +kernel
private theorem endpoint_15_31_prefix_6 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 6 184086513643411531 = some 184086513643411531 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 4 2 184086513643411531 184086513643411531 184086513643411531 endpoint_15_31_prefix_4 endpoint_15_31_window_4
private theorem endpoint_15_31_window_6 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 6 2 184086513643411531 = some 184086513643411531 := by decide +kernel
private theorem endpoint_15_31_prefix_8 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 8 184086513643411531 = some 184086513643411531 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 6 2 184086513643411531 184086513643411531 184086513643411531 endpoint_15_31_prefix_6 endpoint_15_31_window_6
private theorem endpoint_15_31_window_8 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 8 2 184086513643411531 = some 184086513643411531 := by decide +kernel
private theorem endpoint_15_31_prefix_10 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 10 184086513643411531 = some 184086513643411531 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 8 2 184086513643411531 184086513643411531 184086513643411531 endpoint_15_31_prefix_8 endpoint_15_31_window_8
private theorem endpoint_15_31_window_10 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 10 2 184086513643411531 = some 184086513643411531 := by decide +kernel
private theorem endpoint_15_31_prefix_12 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 12 184086513643411531 = some 184086513643411531 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 10 2 184086513643411531 184086513643411531 184086513643411531 endpoint_15_31_prefix_10 endpoint_15_31_window_10
private theorem endpoint_15_31_window_12 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 12 2 184086513643411531 = some 184086513643411531 := by decide +kernel
private theorem endpoint_15_31_prefix_14 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 14 184086513643411531 = some 184086513643411531 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 12 2 184086513643411531 184086513643411531 184086513643411531 endpoint_15_31_prefix_12 endpoint_15_31_window_12

def endpoint_15_31 : CertifiedEndpoint :=
  ⟨⟨15, 31, 3310⟩, 184086513643411531, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_31_flag endpoint_15_31_sources 14 184086513643411531 184086513643411531 rfl endpoint_15_31_base endpoint_15_31_prefix_14) (by decide)⟩

def endpointBlock09 : List CertifiedEndpoint := [
  endpoint_13_78, endpoint_13_79, endpoint_13_80, endpoint_13_81, endpoint_13_82, endpoint_13_83,
  endpoint_13_84, endpoint_13_85, endpoint_13_86, endpoint_13_87, endpoint_13_88, endpoint_13_89,
  endpoint_14_14, endpoint_14_15, endpoint_14_16, endpoint_14_17, endpoint_14_18, endpoint_14_19,
  endpoint_14_20, endpoint_14_21, endpoint_14_22, endpoint_14_23, endpoint_14_24, endpoint_14_25,
  endpoint_14_26, endpoint_14_27, endpoint_14_28, endpoint_14_29, endpoint_14_30, endpoint_14_31,
  endpoint_14_32, endpoint_14_33, endpoint_14_34, endpoint_14_35, endpoint_14_36, endpoint_14_37,
  endpoint_14_38, endpoint_14_39, endpoint_14_40, endpoint_14_41, endpoint_14_42, endpoint_14_43,
  endpoint_14_44, endpoint_14_45, endpoint_14_46, endpoint_14_47, endpoint_14_48, endpoint_14_49,
  endpoint_14_50, endpoint_14_51, endpoint_14_52, endpoint_14_53, endpoint_14_54, endpoint_14_55,
  endpoint_14_56, endpoint_14_57, endpoint_14_58, endpoint_14_59, endpoint_14_60, endpoint_14_61,
  endpoint_14_62, endpoint_14_63, endpoint_14_64, endpoint_14_65, endpoint_14_66, endpoint_14_67,
  endpoint_14_68, endpoint_14_69, endpoint_14_70, endpoint_14_71, endpoint_14_72, endpoint_14_73,
  endpoint_14_74, endpoint_14_75, endpoint_14_76, endpoint_14_77, endpoint_14_78, endpoint_14_79,
  endpoint_14_80, endpoint_14_81, endpoint_14_82, endpoint_14_83, endpoint_14_84, endpoint_14_85,
  endpoint_14_86, endpoint_14_87, endpoint_15_15, endpoint_15_16, endpoint_15_17, endpoint_15_18,
  endpoint_15_19, endpoint_15_20, endpoint_15_21, endpoint_15_22, endpoint_15_23, endpoint_15_24,
  endpoint_15_25, endpoint_15_26, endpoint_15_27, endpoint_15_28, endpoint_15_29, endpoint_15_30,
  endpoint_15_31
]

end ProximityPrize.SubmissionLower.Koala6844Receipts
