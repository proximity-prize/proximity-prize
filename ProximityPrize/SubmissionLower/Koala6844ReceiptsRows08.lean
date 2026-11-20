import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


private def endpoint_12_76_flag : Flag := ⟨12, 76, 1683⟩
private def endpoint_12_76_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_12_76_base : receiptBase endpoint_12_76_flag endpoint_12_76_sources = some 190170843463524114 := by decide +kernel
private theorem endpoint_12_76_window_0 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 2 190170843463524114 = some 190170843463524114 := by decide +kernel
private theorem endpoint_12_76_window_2 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 2 2 190170843463524114 = some 190170843463524114 := by decide +kernel
private theorem endpoint_12_76_prefix_4 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 4 190170843463524114 = some 190170843463524114 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 2 2 190170843463524114 190170843463524114 190170843463524114 endpoint_12_76_window_0 endpoint_12_76_window_2
private theorem endpoint_12_76_window_4 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 4 2 190170843463524114 = some 190170843463524114 := by decide +kernel
private theorem endpoint_12_76_prefix_6 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 6 190170843463524114 = some 190170843463524114 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 4 2 190170843463524114 190170843463524114 190170843463524114 endpoint_12_76_prefix_4 endpoint_12_76_window_4
private theorem endpoint_12_76_window_6 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 6 2 190170843463524114 = some 190170843463524114 := by decide +kernel
private theorem endpoint_12_76_prefix_8 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 8 190170843463524114 = some 190170843463524114 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 6 2 190170843463524114 190170843463524114 190170843463524114 endpoint_12_76_prefix_6 endpoint_12_76_window_6
private theorem endpoint_12_76_window_8 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 8 2 190170843463524114 = some 190170843463524114 := by decide +kernel
private theorem endpoint_12_76_prefix_10 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 10 190170843463524114 = some 190170843463524114 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 8 2 190170843463524114 190170843463524114 190170843463524114 endpoint_12_76_prefix_8 endpoint_12_76_window_8
private theorem endpoint_12_76_window_10 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 10 1 190170843463524114 = some 190170843463524114 := by decide +kernel
private theorem endpoint_12_76_prefix_11 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 11 190170843463524114 = some 190170843463524114 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 10 1 190170843463524114 190170843463524114 190170843463524114 endpoint_12_76_prefix_10 endpoint_12_76_window_10

def endpoint_12_76 : CertifiedEndpoint :=
  ⟨⟨12, 76, 1683⟩, 190170843463524114, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_12_76_flag endpoint_12_76_sources 11 190170843463524114 190170843463524114 rfl endpoint_12_76_base endpoint_12_76_prefix_11) (by decide)⟩
private def endpoint_12_77_flag : Flag := ⟨12, 77, 1594⟩
private def endpoint_12_77_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_12_77_base : receiptBase endpoint_12_77_flag endpoint_12_77_sources = some 182335453086535615 := by decide +kernel
private theorem endpoint_12_77_window_0 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 2 182335453086535615 = some 186390758353975219 := by decide +kernel
private theorem endpoint_12_77_window_2 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 2 2 186390758353975219 = some 186390758353975219 := by decide +kernel
private theorem endpoint_12_77_prefix_4 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 4 182335453086535615 = some 186390758353975219 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 2 2 182335453086535615 186390758353975219 186390758353975219 endpoint_12_77_window_0 endpoint_12_77_window_2
private theorem endpoint_12_77_window_4 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 4 2 186390758353975219 = some 186390758353975219 := by decide +kernel
private theorem endpoint_12_77_prefix_6 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 6 182335453086535615 = some 186390758353975219 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 4 2 182335453086535615 186390758353975219 186390758353975219 endpoint_12_77_prefix_4 endpoint_12_77_window_4
private theorem endpoint_12_77_window_6 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 6 2 186390758353975219 = some 186390758353975219 := by decide +kernel
private theorem endpoint_12_77_prefix_8 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 8 182335453086535615 = some 186390758353975219 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 6 2 182335453086535615 186390758353975219 186390758353975219 endpoint_12_77_prefix_6 endpoint_12_77_window_6
private theorem endpoint_12_77_window_8 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 8 2 186390758353975219 = some 186390758353975219 := by decide +kernel
private theorem endpoint_12_77_prefix_10 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 10 182335453086535615 = some 186390758353975219 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 8 2 182335453086535615 186390758353975219 186390758353975219 endpoint_12_77_prefix_8 endpoint_12_77_window_8
private theorem endpoint_12_77_window_10 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 10 1 186390758353975219 = some 186390758353975219 := by decide +kernel
private theorem endpoint_12_77_prefix_11 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 11 182335453086535615 = some 186390758353975219 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 10 1 182335453086535615 186390758353975219 186390758353975219 endpoint_12_77_prefix_10 endpoint_12_77_window_10

def endpoint_12_77 : CertifiedEndpoint :=
  ⟨⟨12, 77, 1594⟩, 186390758353975219, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_12_77_flag endpoint_12_77_sources 11 182335453086535615 186390758353975219 rfl endpoint_12_77_base endpoint_12_77_prefix_11) (by decide)⟩
private def endpoint_12_78_flag : Flag := ⟨12, 78, 1503⟩
private def endpoint_12_78_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_12_78_base : receiptBase endpoint_12_78_flag endpoint_12_78_sources = some 176908516345837102 := by decide +kernel
private theorem endpoint_12_78_window_0 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 2 176908516345837102 = some 176908516345837102 := by decide +kernel
private theorem endpoint_12_78_window_2 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 2 2 176908516345837102 = some 176908516345837102 := by decide +kernel
private theorem endpoint_12_78_prefix_4 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 4 176908516345837102 = some 176908516345837102 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 2 2 176908516345837102 176908516345837102 176908516345837102 endpoint_12_78_window_0 endpoint_12_78_window_2
private theorem endpoint_12_78_window_4 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 4 2 176908516345837102 = some 176908516345837102 := by decide +kernel
private theorem endpoint_12_78_prefix_6 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 6 176908516345837102 = some 176908516345837102 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 4 2 176908516345837102 176908516345837102 176908516345837102 endpoint_12_78_prefix_4 endpoint_12_78_window_4
private theorem endpoint_12_78_window_6 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 6 2 176908516345837102 = some 176908516345837102 := by decide +kernel
private theorem endpoint_12_78_prefix_8 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 8 176908516345837102 = some 176908516345837102 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 6 2 176908516345837102 176908516345837102 176908516345837102 endpoint_12_78_prefix_6 endpoint_12_78_window_6
private theorem endpoint_12_78_window_8 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 8 2 176908516345837102 = some 176908516345837102 := by decide +kernel
private theorem endpoint_12_78_prefix_10 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 10 176908516345837102 = some 176908516345837102 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 8 2 176908516345837102 176908516345837102 176908516345837102 endpoint_12_78_prefix_8 endpoint_12_78_window_8
private theorem endpoint_12_78_window_10 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 10 1 176908516345837102 = some 176908516345837102 := by decide +kernel
private theorem endpoint_12_78_prefix_11 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 11 176908516345837102 = some 176908516345837102 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 10 1 176908516345837102 176908516345837102 176908516345837102 endpoint_12_78_prefix_10 endpoint_12_78_window_10

def endpoint_12_78 : CertifiedEndpoint :=
  ⟨⟨12, 78, 1503⟩, 176908516345837102, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_12_78_flag endpoint_12_78_sources 11 176908516345837102 176908516345837102 rfl endpoint_12_78_base endpoint_12_78_prefix_11) (by decide)⟩
private def endpoint_12_79_flag : Flag := ⟨12, 79, 1410⟩
private def endpoint_12_79_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_12_79_base : receiptBase endpoint_12_79_flag endpoint_12_79_sources = some 167928470745958086 := by decide +kernel
private theorem endpoint_12_79_window_0 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 2 167928470745958086 = some 167928470745958086 := by decide +kernel
private theorem endpoint_12_79_window_2 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 2 2 167928470745958086 = some 167928470745958086 := by decide +kernel
private theorem endpoint_12_79_prefix_4 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 4 167928470745958086 = some 167928470745958086 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 2 2 167928470745958086 167928470745958086 167928470745958086 endpoint_12_79_window_0 endpoint_12_79_window_2
private theorem endpoint_12_79_window_4 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 4 2 167928470745958086 = some 167928470745958086 := by decide +kernel
private theorem endpoint_12_79_prefix_6 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 6 167928470745958086 = some 167928470745958086 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 4 2 167928470745958086 167928470745958086 167928470745958086 endpoint_12_79_prefix_4 endpoint_12_79_window_4
private theorem endpoint_12_79_window_6 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 6 2 167928470745958086 = some 167928470745958086 := by decide +kernel
private theorem endpoint_12_79_prefix_8 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 8 167928470745958086 = some 167928470745958086 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 6 2 167928470745958086 167928470745958086 167928470745958086 endpoint_12_79_prefix_6 endpoint_12_79_window_6
private theorem endpoint_12_79_window_8 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 8 2 167928470745958086 = some 167928470745958086 := by decide +kernel
private theorem endpoint_12_79_prefix_10 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 10 167928470745958086 = some 167928470745958086 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 8 2 167928470745958086 167928470745958086 167928470745958086 endpoint_12_79_prefix_8 endpoint_12_79_window_8
private theorem endpoint_12_79_window_10 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 10 1 167928470745958086 = some 167928470745958086 := by decide +kernel
private theorem endpoint_12_79_prefix_11 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 11 167928470745958086 = some 167928470745958086 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 10 1 167928470745958086 167928470745958086 167928470745958086 endpoint_12_79_prefix_10 endpoint_12_79_window_10

def endpoint_12_79 : CertifiedEndpoint :=
  ⟨⟨12, 79, 1410⟩, 167928470745958086, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_12_79_flag endpoint_12_79_sources 11 167928470745958086 167928470745958086 rfl endpoint_12_79_base endpoint_12_79_prefix_11) (by decide)⟩
private def endpoint_12_80_flag : Flag := ⟨12, 80, 1313⟩
private def endpoint_12_80_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_12_80_base : receiptBase endpoint_12_80_flag endpoint_12_80_sources = some 158596384777060050 := by decide +kernel
private theorem endpoint_12_80_window_0 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 2 158596384777060050 = some 158596384777060050 := by decide +kernel
private theorem endpoint_12_80_window_2 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 2 2 158596384777060050 = some 158596384777060050 := by decide +kernel
private theorem endpoint_12_80_prefix_4 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 4 158596384777060050 = some 158596384777060050 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 2 2 158596384777060050 158596384777060050 158596384777060050 endpoint_12_80_window_0 endpoint_12_80_window_2
private theorem endpoint_12_80_window_4 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 4 2 158596384777060050 = some 158596384777060050 := by decide +kernel
private theorem endpoint_12_80_prefix_6 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 6 158596384777060050 = some 158596384777060050 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 4 2 158596384777060050 158596384777060050 158596384777060050 endpoint_12_80_prefix_4 endpoint_12_80_window_4
private theorem endpoint_12_80_window_6 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 6 2 158596384777060050 = some 158596384777060050 := by decide +kernel
private theorem endpoint_12_80_prefix_8 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 8 158596384777060050 = some 158596384777060050 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 6 2 158596384777060050 158596384777060050 158596384777060050 endpoint_12_80_prefix_6 endpoint_12_80_window_6
private theorem endpoint_12_80_window_8 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 8 2 158596384777060050 = some 158596384777060050 := by decide +kernel
private theorem endpoint_12_80_prefix_10 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 10 158596384777060050 = some 158596384777060050 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 8 2 158596384777060050 158596384777060050 158596384777060050 endpoint_12_80_prefix_8 endpoint_12_80_window_8
private theorem endpoint_12_80_window_10 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 10 1 158596384777060050 = some 158596384777060050 := by decide +kernel
private theorem endpoint_12_80_prefix_11 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 11 158596384777060050 = some 158596384777060050 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 10 1 158596384777060050 158596384777060050 158596384777060050 endpoint_12_80_prefix_10 endpoint_12_80_window_10

def endpoint_12_80 : CertifiedEndpoint :=
  ⟨⟨12, 80, 1313⟩, 158596384777060050, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_12_80_flag endpoint_12_80_sources 11 158596384777060050 158596384777060050 rfl endpoint_12_80_base endpoint_12_80_prefix_11) (by decide)⟩
private def endpoint_12_81_flag : Flag := ⟨12, 81, 1214⟩
private def endpoint_12_81_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_12_81_base : receiptBase endpoint_12_81_flag endpoint_12_81_sources = some 149205559653945491 := by decide +kernel
private theorem endpoint_12_81_window_0 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 2 149205559653945491 = some 149205559653945491 := by decide +kernel
private theorem endpoint_12_81_window_2 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 2 2 149205559653945491 = some 149205559653945491 := by decide +kernel
private theorem endpoint_12_81_prefix_4 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 4 149205559653945491 = some 149205559653945491 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 2 2 149205559653945491 149205559653945491 149205559653945491 endpoint_12_81_window_0 endpoint_12_81_window_2
private theorem endpoint_12_81_window_4 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 4 2 149205559653945491 = some 149205559653945491 := by decide +kernel
private theorem endpoint_12_81_prefix_6 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 6 149205559653945491 = some 149205559653945491 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 4 2 149205559653945491 149205559653945491 149205559653945491 endpoint_12_81_prefix_4 endpoint_12_81_window_4
private theorem endpoint_12_81_window_6 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 6 2 149205559653945491 = some 149205559653945491 := by decide +kernel
private theorem endpoint_12_81_prefix_8 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 8 149205559653945491 = some 149205559653945491 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 6 2 149205559653945491 149205559653945491 149205559653945491 endpoint_12_81_prefix_6 endpoint_12_81_window_6
private theorem endpoint_12_81_window_8 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 8 2 149205559653945491 = some 149205559653945491 := by decide +kernel
private theorem endpoint_12_81_prefix_10 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 10 149205559653945491 = some 149205559653945491 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 8 2 149205559653945491 149205559653945491 149205559653945491 endpoint_12_81_prefix_8 endpoint_12_81_window_8
private theorem endpoint_12_81_window_10 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 10 1 149205559653945491 = some 149205559653945491 := by decide +kernel
private theorem endpoint_12_81_prefix_11 : receiptWindow endpoint_12_81_flag endpoint_12_81_sources 0 11 149205559653945491 = some 149205559653945491 :=
  join_receipt_window endpoint_12_81_flag endpoint_12_81_sources 0 10 1 149205559653945491 149205559653945491 149205559653945491 endpoint_12_81_prefix_10 endpoint_12_81_window_10

def endpoint_12_81 : CertifiedEndpoint :=
  ⟨⟨12, 81, 1214⟩, 149205559653945491, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_12_81_flag endpoint_12_81_sources 11 149205559653945491 149205559653945491 rfl endpoint_12_81_base endpoint_12_81_prefix_11) (by decide)⟩
def endpoint_12_82 : CertifiedEndpoint :=
  ⟨⟨12, 82, 1113⟩, 239853981874346867, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_83 : CertifiedEndpoint :=
  ⟨⟨12, 83, 1009⟩, 219269171502487882, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_84 : CertifiedEndpoint :=
  ⟨⟨12, 84, 902⟩, 197372112630308930, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_85 : CertifiedEndpoint :=
  ⟨⟨12, 85, 792⟩, 174136055532626165, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_86 : CertifiedEndpoint :=
  ⟨⟨12, 86, 680⟩, 149770548346869036, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_87 : CertifiedEndpoint :=
  ⟨⟨12, 87, 565⟩, 124018487868614590, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_88 : CertifiedEndpoint :=
  ⟨⟨12, 88, 447⟩, 96853124372678981, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_89 : CertifiedEndpoint :=
  ⟨⟨12, 89, 326⟩, 68247708133878363, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_90 : CertifiedEndpoint :=
  ⟨⟨12, 90, 203⟩, 38423676056390561, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_13 : CertifiedEndpoint :=
  ⟨⟨13, 13, 3975⟩, 94113607162249684, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_14 : CertifiedEndpoint :=
  ⟨⟨13, 14, 3955⟩, 97801874013431884, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_15 : CertifiedEndpoint :=
  ⟨⟨13, 15, 3935⟩, 101447877319489004, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_16 : CertifiedEndpoint :=
  ⟨⟨13, 16, 3914⟩, 113496823256012462, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_17 : CertifiedEndpoint :=
  ⟨⟨13, 17, 3893⟩, 125406883663833042, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_18 : CertifiedEndpoint :=
  ⟨⟨13, 18, 3872⟩, 137178058542950744, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_19 : CertifiedEndpoint :=
  ⟨⟨13, 19, 3851⟩, 148810347893365568, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_20 : CertifiedEndpoint :=
  ⟨⟨13, 20, 3830⟩, 160303751715077514, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_21 : CertifiedEndpoint :=
  ⟨⟨13, 21, 3808⟩, 171613042837550343, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_22 : CertifiedEndpoint :=
  ⟨⟨13, 22, 3786⟩, 182776988639287602, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_23 : CertifiedEndpoint :=
  ⟨⟨13, 23, 3764⟩, 193795589120289291, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_24 : CertifiedEndpoint :=
  ⟨⟨13, 24, 3741⟩, 204613927421970133, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_25 : CertifiedEndpoint :=
  ⟨⟨13, 25, 3718⟩, 215280460610882713, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_26 : CertifiedEndpoint :=
  ⟨⟨13, 26, 3695⟩, 225795188687027031, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_27 : CertifiedEndpoint :=
  ⟨⟨13, 27, 3672⟩, 236158111650403087, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_28 : CertifiedEndpoint :=
  ⟨⟨13, 28, 3648⟩, 246301393058360220, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_13_29_flag : Flag := ⟨13, 29, 3625⟩
private def endpoint_13_29_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_29_base : receiptBase endpoint_13_29_flag endpoint_13_29_sources = some 172349983246664968 := by decide +kernel
private theorem endpoint_13_29_window_0 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 2 172349983246664968 = some 172349983246664968 := by decide +kernel
private theorem endpoint_13_29_window_2 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 2 2 172349983246664968 = some 172349983246664968 := by decide +kernel
private theorem endpoint_13_29_prefix_4 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 4 172349983246664968 = some 172349983246664968 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 2 2 172349983246664968 172349983246664968 172349983246664968 endpoint_13_29_window_0 endpoint_13_29_window_2
private theorem endpoint_13_29_window_4 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 4 2 172349983246664968 = some 172349983246664968 := by decide +kernel
private theorem endpoint_13_29_prefix_6 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 6 172349983246664968 = some 172349983246664968 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 4 2 172349983246664968 172349983246664968 172349983246664968 endpoint_13_29_prefix_4 endpoint_13_29_window_4
private theorem endpoint_13_29_window_6 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 6 2 172349983246664968 = some 172349983246664968 := by decide +kernel
private theorem endpoint_13_29_prefix_8 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 8 172349983246664968 = some 172349983246664968 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 6 2 172349983246664968 172349983246664968 172349983246664968 endpoint_13_29_prefix_6 endpoint_13_29_window_6
private theorem endpoint_13_29_window_8 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 8 2 172349983246664968 = some 172349983246664968 := by decide +kernel
private theorem endpoint_13_29_prefix_10 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 10 172349983246664968 = some 172349983246664968 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 8 2 172349983246664968 172349983246664968 172349983246664968 endpoint_13_29_prefix_8 endpoint_13_29_window_8
private theorem endpoint_13_29_window_10 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 10 2 172349983246664968 = some 172349983246664968 := by decide +kernel
private theorem endpoint_13_29_prefix_12 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 12 172349983246664968 = some 172349983246664968 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 10 2 172349983246664968 172349983246664968 172349983246664968 endpoint_13_29_prefix_10 endpoint_13_29_window_10

def endpoint_13_29 : CertifiedEndpoint :=
  ⟨⟨13, 29, 3625⟩, 172349983246664968, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_29_flag endpoint_13_29_sources 12 172349983246664968 172349983246664968 rfl endpoint_13_29_base endpoint_13_29_prefix_12) (by decide)⟩
private def endpoint_13_30_flag : Flag := ⟨13, 30, 3600⟩
private def endpoint_13_30_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_30_base : receiptBase endpoint_13_30_flag endpoint_13_30_sources = some 175988214529401571 := by decide +kernel
private theorem endpoint_13_30_window_0 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 2 175988214529401571 = some 175988214529401571 := by decide +kernel
private theorem endpoint_13_30_window_2 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 2 2 175988214529401571 = some 175988214529401571 := by decide +kernel
private theorem endpoint_13_30_prefix_4 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 4 175988214529401571 = some 175988214529401571 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 2 2 175988214529401571 175988214529401571 175988214529401571 endpoint_13_30_window_0 endpoint_13_30_window_2
private theorem endpoint_13_30_window_4 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 4 2 175988214529401571 = some 175988214529401571 := by decide +kernel
private theorem endpoint_13_30_prefix_6 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 6 175988214529401571 = some 175988214529401571 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 4 2 175988214529401571 175988214529401571 175988214529401571 endpoint_13_30_prefix_4 endpoint_13_30_window_4
private theorem endpoint_13_30_window_6 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 6 2 175988214529401571 = some 175988214529401571 := by decide +kernel
private theorem endpoint_13_30_prefix_8 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 8 175988214529401571 = some 175988214529401571 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 6 2 175988214529401571 175988214529401571 175988214529401571 endpoint_13_30_prefix_6 endpoint_13_30_window_6
private theorem endpoint_13_30_window_8 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 8 2 175988214529401571 = some 175988214529401571 := by decide +kernel
private theorem endpoint_13_30_prefix_10 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 10 175988214529401571 = some 175988214529401571 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 8 2 175988214529401571 175988214529401571 175988214529401571 endpoint_13_30_prefix_8 endpoint_13_30_window_8
private theorem endpoint_13_30_window_10 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 10 2 175988214529401571 = some 175988214529401571 := by decide +kernel
private theorem endpoint_13_30_prefix_12 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 12 175988214529401571 = some 175988214529401571 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 10 2 175988214529401571 175988214529401571 175988214529401571 endpoint_13_30_prefix_10 endpoint_13_30_window_10

def endpoint_13_30 : CertifiedEndpoint :=
  ⟨⟨13, 30, 3600⟩, 175988214529401571, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_30_flag endpoint_13_30_sources 12 175988214529401571 175988214529401571 rfl endpoint_13_30_base endpoint_13_30_prefix_12) (by decide)⟩
private def endpoint_13_31_flag : Flag := ⟨13, 31, 3576⟩
private def endpoint_13_31_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_31_base : receiptBase endpoint_13_31_flag endpoint_13_31_sources = some 179609280964401581 := by decide +kernel
private theorem endpoint_13_31_window_0 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 2 179609280964401581 = some 179609280964401581 := by decide +kernel
private theorem endpoint_13_31_window_2 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 2 2 179609280964401581 = some 179609280964401581 := by decide +kernel
private theorem endpoint_13_31_prefix_4 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 4 179609280964401581 = some 179609280964401581 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 2 2 179609280964401581 179609280964401581 179609280964401581 endpoint_13_31_window_0 endpoint_13_31_window_2
private theorem endpoint_13_31_window_4 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 4 2 179609280964401581 = some 179609280964401581 := by decide +kernel
private theorem endpoint_13_31_prefix_6 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 6 179609280964401581 = some 179609280964401581 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 4 2 179609280964401581 179609280964401581 179609280964401581 endpoint_13_31_prefix_4 endpoint_13_31_window_4
private theorem endpoint_13_31_window_6 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 6 2 179609280964401581 = some 179609280964401581 := by decide +kernel
private theorem endpoint_13_31_prefix_8 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 8 179609280964401581 = some 179609280964401581 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 6 2 179609280964401581 179609280964401581 179609280964401581 endpoint_13_31_prefix_6 endpoint_13_31_window_6
private theorem endpoint_13_31_window_8 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 8 2 179609280964401581 = some 179609280964401581 := by decide +kernel
private theorem endpoint_13_31_prefix_10 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 10 179609280964401581 = some 179609280964401581 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 8 2 179609280964401581 179609280964401581 179609280964401581 endpoint_13_31_prefix_8 endpoint_13_31_window_8
private theorem endpoint_13_31_window_10 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 10 2 179609280964401581 = some 179609280964401581 := by decide +kernel
private theorem endpoint_13_31_prefix_12 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 12 179609280964401581 = some 179609280964401581 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 10 2 179609280964401581 179609280964401581 179609280964401581 endpoint_13_31_prefix_10 endpoint_13_31_window_10

def endpoint_13_31 : CertifiedEndpoint :=
  ⟨⟨13, 31, 3576⟩, 179609280964401581, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_31_flag endpoint_13_31_sources 12 179609280964401581 179609280964401581 rfl endpoint_13_31_base endpoint_13_31_prefix_12) (by decide)⟩
private def endpoint_13_32_flag : Flag := ⟨13, 32, 3551⟩
private def endpoint_13_32_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_32_base : receiptBase endpoint_13_32_flag endpoint_13_32_sources = some 183115602193711711 := by decide +kernel
private theorem endpoint_13_32_window_0 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 2 183115602193711711 = some 183115602193711711 := by decide +kernel
private theorem endpoint_13_32_window_2 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 2 2 183115602193711711 = some 183115602193711711 := by decide +kernel
private theorem endpoint_13_32_prefix_4 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 4 183115602193711711 = some 183115602193711711 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 2 2 183115602193711711 183115602193711711 183115602193711711 endpoint_13_32_window_0 endpoint_13_32_window_2
private theorem endpoint_13_32_window_4 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 4 2 183115602193711711 = some 183115602193711711 := by decide +kernel
private theorem endpoint_13_32_prefix_6 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 6 183115602193711711 = some 183115602193711711 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 4 2 183115602193711711 183115602193711711 183115602193711711 endpoint_13_32_prefix_4 endpoint_13_32_window_4
private theorem endpoint_13_32_window_6 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 6 2 183115602193711711 = some 183115602193711711 := by decide +kernel
private theorem endpoint_13_32_prefix_8 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 8 183115602193711711 = some 183115602193711711 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 6 2 183115602193711711 183115602193711711 183115602193711711 endpoint_13_32_prefix_6 endpoint_13_32_window_6
private theorem endpoint_13_32_window_8 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 8 2 183115602193711711 = some 183115602193711711 := by decide +kernel
private theorem endpoint_13_32_prefix_10 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 10 183115602193711711 = some 183115602193711711 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 8 2 183115602193711711 183115602193711711 183115602193711711 endpoint_13_32_prefix_8 endpoint_13_32_window_8
private theorem endpoint_13_32_window_10 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 10 2 183115602193711711 = some 183115602193711711 := by decide +kernel
private theorem endpoint_13_32_prefix_12 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 12 183115602193711711 = some 183115602193711711 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 10 2 183115602193711711 183115602193711711 183115602193711711 endpoint_13_32_prefix_10 endpoint_13_32_window_10

def endpoint_13_32 : CertifiedEndpoint :=
  ⟨⟨13, 32, 3551⟩, 183115602193711711, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_32_flag endpoint_13_32_sources 12 183115602193711711 183115602193711711 rfl endpoint_13_32_base endpoint_13_32_prefix_12) (by decide)⟩
private def endpoint_13_33_flag : Flag := ⟨13, 33, 3525⟩
private def endpoint_13_33_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_33_base : receiptBase endpoint_13_33_flag endpoint_13_33_sources = some 186503261299797862 := by decide +kernel
private theorem endpoint_13_33_window_0 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 2 186503261299797862 = some 186503261299797862 := by decide +kernel
private theorem endpoint_13_33_window_2 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 2 2 186503261299797862 = some 186503261299797862 := by decide +kernel
private theorem endpoint_13_33_prefix_4 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 4 186503261299797862 = some 186503261299797862 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 2 2 186503261299797862 186503261299797862 186503261299797862 endpoint_13_33_window_0 endpoint_13_33_window_2
private theorem endpoint_13_33_window_4 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 4 2 186503261299797862 = some 186503261299797862 := by decide +kernel
private theorem endpoint_13_33_prefix_6 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 6 186503261299797862 = some 186503261299797862 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 4 2 186503261299797862 186503261299797862 186503261299797862 endpoint_13_33_prefix_4 endpoint_13_33_window_4
private theorem endpoint_13_33_window_6 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 6 2 186503261299797862 = some 186503261299797862 := by decide +kernel
private theorem endpoint_13_33_prefix_8 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 8 186503261299797862 = some 186503261299797862 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 6 2 186503261299797862 186503261299797862 186503261299797862 endpoint_13_33_prefix_6 endpoint_13_33_window_6
private theorem endpoint_13_33_window_8 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 8 2 186503261299797862 = some 186503261299797862 := by decide +kernel
private theorem endpoint_13_33_prefix_10 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 10 186503261299797862 = some 186503261299797862 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 8 2 186503261299797862 186503261299797862 186503261299797862 endpoint_13_33_prefix_8 endpoint_13_33_window_8
private theorem endpoint_13_33_window_10 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 10 2 186503261299797862 = some 186503261299797862 := by decide +kernel
private theorem endpoint_13_33_prefix_12 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 12 186503261299797862 = some 186503261299797862 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 10 2 186503261299797862 186503261299797862 186503261299797862 endpoint_13_33_prefix_10 endpoint_13_33_window_10

def endpoint_13_33 : CertifiedEndpoint :=
  ⟨⟨13, 33, 3525⟩, 186503261299797862, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_33_flag endpoint_13_33_sources 12 186503261299797862 186503261299797862 rfl endpoint_13_33_base endpoint_13_33_prefix_12) (by decide)⟩
private def endpoint_13_34_flag : Flag := ⟨13, 34, 3499⟩
private def endpoint_13_34_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_34_base : receiptBase endpoint_13_34_flag endpoint_13_34_sources = some 189821701281225693 := by decide +kernel
private theorem endpoint_13_34_window_0 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 2 189821701281225693 = some 189821701281225693 := by decide +kernel
private theorem endpoint_13_34_window_2 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 2 2 189821701281225693 = some 189821701281225693 := by decide +kernel
private theorem endpoint_13_34_prefix_4 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 4 189821701281225693 = some 189821701281225693 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 2 2 189821701281225693 189821701281225693 189821701281225693 endpoint_13_34_window_0 endpoint_13_34_window_2
private theorem endpoint_13_34_window_4 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 4 2 189821701281225693 = some 189821701281225693 := by decide +kernel
private theorem endpoint_13_34_prefix_6 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 6 189821701281225693 = some 189821701281225693 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 4 2 189821701281225693 189821701281225693 189821701281225693 endpoint_13_34_prefix_4 endpoint_13_34_window_4
private theorem endpoint_13_34_window_6 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 6 2 189821701281225693 = some 189821701281225693 := by decide +kernel
private theorem endpoint_13_34_prefix_8 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 8 189821701281225693 = some 189821701281225693 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 6 2 189821701281225693 189821701281225693 189821701281225693 endpoint_13_34_prefix_6 endpoint_13_34_window_6
private theorem endpoint_13_34_window_8 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 8 2 189821701281225693 = some 189821701281225693 := by decide +kernel
private theorem endpoint_13_34_prefix_10 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 10 189821701281225693 = some 189821701281225693 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 8 2 189821701281225693 189821701281225693 189821701281225693 endpoint_13_34_prefix_8 endpoint_13_34_window_8
private theorem endpoint_13_34_window_10 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 10 2 189821701281225693 = some 189821701281225693 := by decide +kernel
private theorem endpoint_13_34_prefix_12 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 12 189821701281225693 = some 189821701281225693 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 10 2 189821701281225693 189821701281225693 189821701281225693 endpoint_13_34_prefix_10 endpoint_13_34_window_10

def endpoint_13_34 : CertifiedEndpoint :=
  ⟨⟨13, 34, 3499⟩, 189821701281225693, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_34_flag endpoint_13_34_sources 12 189821701281225693 189821701281225693 rfl endpoint_13_34_base endpoint_13_34_prefix_12) (by decide)⟩
private def endpoint_13_35_flag : Flag := ⟨13, 35, 3473⟩
private def endpoint_13_35_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_35_base : receiptBase endpoint_13_35_flag endpoint_13_35_sources = some 193641409247347882 := by decide +kernel
private theorem endpoint_13_35_window_0 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 2 193641409247347882 = some 193641409247347882 := by decide +kernel
private theorem endpoint_13_35_window_2 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 2 2 193641409247347882 = some 193641409247347882 := by decide +kernel
private theorem endpoint_13_35_prefix_4 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 4 193641409247347882 = some 193641409247347882 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 2 2 193641409247347882 193641409247347882 193641409247347882 endpoint_13_35_window_0 endpoint_13_35_window_2
private theorem endpoint_13_35_window_4 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 4 2 193641409247347882 = some 193641409247347882 := by decide +kernel
private theorem endpoint_13_35_prefix_6 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 6 193641409247347882 = some 193641409247347882 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 4 2 193641409247347882 193641409247347882 193641409247347882 endpoint_13_35_prefix_4 endpoint_13_35_window_4
private theorem endpoint_13_35_window_6 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 6 2 193641409247347882 = some 193641409247347882 := by decide +kernel
private theorem endpoint_13_35_prefix_8 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 8 193641409247347882 = some 193641409247347882 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 6 2 193641409247347882 193641409247347882 193641409247347882 endpoint_13_35_prefix_6 endpoint_13_35_window_6
private theorem endpoint_13_35_window_8 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 8 2 193641409247347882 = some 193641409247347882 := by decide +kernel
private theorem endpoint_13_35_prefix_10 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 10 193641409247347882 = some 193641409247347882 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 8 2 193641409247347882 193641409247347882 193641409247347882 endpoint_13_35_prefix_8 endpoint_13_35_window_8
private theorem endpoint_13_35_window_10 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 10 2 193641409247347882 = some 193641409247347882 := by decide +kernel
private theorem endpoint_13_35_prefix_12 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 12 193641409247347882 = some 193641409247347882 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 10 2 193641409247347882 193641409247347882 193641409247347882 endpoint_13_35_prefix_10 endpoint_13_35_window_10

def endpoint_13_35 : CertifiedEndpoint :=
  ⟨⟨13, 35, 3473⟩, 193641409247347882, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_35_flag endpoint_13_35_sources 12 193641409247347882 193641409247347882 rfl endpoint_13_35_base endpoint_13_35_prefix_12) (by decide)⟩
private def endpoint_13_36_flag : Flag := ⟨13, 36, 3447⟩
private def endpoint_13_36_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_36_base : receiptBase endpoint_13_36_flag endpoint_13_36_sources = some 196736138885581402 := by decide +kernel
private theorem endpoint_13_36_window_0 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 2 196736138885581402 = some 196736138885581402 := by decide +kernel
private theorem endpoint_13_36_window_2 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 2 2 196736138885581402 = some 196736138885581402 := by decide +kernel
private theorem endpoint_13_36_prefix_4 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 4 196736138885581402 = some 196736138885581402 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 2 2 196736138885581402 196736138885581402 196736138885581402 endpoint_13_36_window_0 endpoint_13_36_window_2
private theorem endpoint_13_36_window_4 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 4 2 196736138885581402 = some 196736138885581402 := by decide +kernel
private theorem endpoint_13_36_prefix_6 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 6 196736138885581402 = some 196736138885581402 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 4 2 196736138885581402 196736138885581402 196736138885581402 endpoint_13_36_prefix_4 endpoint_13_36_window_4
private theorem endpoint_13_36_window_6 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 6 2 196736138885581402 = some 196736138885581402 := by decide +kernel
private theorem endpoint_13_36_prefix_8 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 8 196736138885581402 = some 196736138885581402 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 6 2 196736138885581402 196736138885581402 196736138885581402 endpoint_13_36_prefix_6 endpoint_13_36_window_6
private theorem endpoint_13_36_window_8 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 8 2 196736138885581402 = some 196736138885581402 := by decide +kernel
private theorem endpoint_13_36_prefix_10 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 10 196736138885581402 = some 196736138885581402 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 8 2 196736138885581402 196736138885581402 196736138885581402 endpoint_13_36_prefix_8 endpoint_13_36_window_8
private theorem endpoint_13_36_window_10 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 10 2 196736138885581402 = some 196736138885581402 := by decide +kernel
private theorem endpoint_13_36_prefix_12 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 12 196736138885581402 = some 196736138885581402 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 10 2 196736138885581402 196736138885581402 196736138885581402 endpoint_13_36_prefix_10 endpoint_13_36_window_10

def endpoint_13_36 : CertifiedEndpoint :=
  ⟨⟨13, 36, 3447⟩, 196736138885581402, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_36_flag endpoint_13_36_sources 12 196736138885581402 196736138885581402 rfl endpoint_13_36_base endpoint_13_36_prefix_12) (by decide)⟩
private def endpoint_13_37_flag : Flag := ⟨13, 37, 3420⟩
private def endpoint_13_37_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_37_base : receiptBase endpoint_13_37_flag endpoint_13_37_sources = some 199705247341526374 := by decide +kernel
private theorem endpoint_13_37_window_0 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 2 199705247341526374 = some 199705247341526374 := by decide +kernel
private theorem endpoint_13_37_window_2 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 2 2 199705247341526374 = some 199705247341526374 := by decide +kernel
private theorem endpoint_13_37_prefix_4 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 4 199705247341526374 = some 199705247341526374 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 2 2 199705247341526374 199705247341526374 199705247341526374 endpoint_13_37_window_0 endpoint_13_37_window_2
private theorem endpoint_13_37_window_4 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 4 2 199705247341526374 = some 199705247341526374 := by decide +kernel
private theorem endpoint_13_37_prefix_6 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 6 199705247341526374 = some 199705247341526374 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 4 2 199705247341526374 199705247341526374 199705247341526374 endpoint_13_37_prefix_4 endpoint_13_37_window_4
private theorem endpoint_13_37_window_6 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 6 2 199705247341526374 = some 199705247341526374 := by decide +kernel
private theorem endpoint_13_37_prefix_8 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 8 199705247341526374 = some 199705247341526374 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 6 2 199705247341526374 199705247341526374 199705247341526374 endpoint_13_37_prefix_6 endpoint_13_37_window_6
private theorem endpoint_13_37_window_8 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 8 2 199705247341526374 = some 199705247341526374 := by decide +kernel
private theorem endpoint_13_37_prefix_10 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 10 199705247341526374 = some 199705247341526374 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 8 2 199705247341526374 199705247341526374 199705247341526374 endpoint_13_37_prefix_8 endpoint_13_37_window_8
private theorem endpoint_13_37_window_10 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 10 2 199705247341526374 = some 199705247341526374 := by decide +kernel
private theorem endpoint_13_37_prefix_12 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 12 199705247341526374 = some 199705247341526374 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 10 2 199705247341526374 199705247341526374 199705247341526374 endpoint_13_37_prefix_10 endpoint_13_37_window_10

def endpoint_13_37 : CertifiedEndpoint :=
  ⟨⟨13, 37, 3420⟩, 199705247341526374, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_37_flag endpoint_13_37_sources 12 199705247341526374 199705247341526374 rfl endpoint_13_37_base endpoint_13_37_prefix_12) (by decide)⟩
private def endpoint_13_38_flag : Flag := ⟨13, 38, 3392⟩
private def endpoint_13_38_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_38_base : receiptBase endpoint_13_38_flag endpoint_13_38_sources = some 202544878458265697 := by decide +kernel
private theorem endpoint_13_38_window_0 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 2 202544878458265697 = some 202544878458265697 := by decide +kernel
private theorem endpoint_13_38_window_2 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 2 2 202544878458265697 = some 202544878458265697 := by decide +kernel
private theorem endpoint_13_38_prefix_4 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 4 202544878458265697 = some 202544878458265697 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 2 2 202544878458265697 202544878458265697 202544878458265697 endpoint_13_38_window_0 endpoint_13_38_window_2
private theorem endpoint_13_38_window_4 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 4 2 202544878458265697 = some 202544878458265697 := by decide +kernel
private theorem endpoint_13_38_prefix_6 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 6 202544878458265697 = some 202544878458265697 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 4 2 202544878458265697 202544878458265697 202544878458265697 endpoint_13_38_prefix_4 endpoint_13_38_window_4
private theorem endpoint_13_38_window_6 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 6 2 202544878458265697 = some 202544878458265697 := by decide +kernel
private theorem endpoint_13_38_prefix_8 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 8 202544878458265697 = some 202544878458265697 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 6 2 202544878458265697 202544878458265697 202544878458265697 endpoint_13_38_prefix_6 endpoint_13_38_window_6
private theorem endpoint_13_38_window_8 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 8 2 202544878458265697 = some 202544878458265697 := by decide +kernel
private theorem endpoint_13_38_prefix_10 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 10 202544878458265697 = some 202544878458265697 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 8 2 202544878458265697 202544878458265697 202544878458265697 endpoint_13_38_prefix_8 endpoint_13_38_window_8
private theorem endpoint_13_38_window_10 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 10 2 202544878458265697 = some 202544878458265697 := by decide +kernel
private theorem endpoint_13_38_prefix_12 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 12 202544878458265697 = some 202544878458265697 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 10 2 202544878458265697 202544878458265697 202544878458265697 endpoint_13_38_prefix_10 endpoint_13_38_window_10

def endpoint_13_38 : CertifiedEndpoint :=
  ⟨⟨13, 38, 3392⟩, 202544878458265697, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_38_flag endpoint_13_38_sources 12 202544878458265697 202544878458265697 rfl endpoint_13_38_base endpoint_13_38_prefix_12) (by decide)⟩
private def endpoint_13_39_flag : Flag := ⟨13, 39, 3364⟩
private def endpoint_13_39_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_39_base : receiptBase endpoint_13_39_flag endpoint_13_39_sources = some 205311242593580103 := by decide +kernel
private theorem endpoint_13_39_window_0 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 2 205311242593580103 = some 205311242593580103 := by decide +kernel
private theorem endpoint_13_39_window_2 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 2 2 205311242593580103 = some 205311242593580103 := by decide +kernel
private theorem endpoint_13_39_prefix_4 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 4 205311242593580103 = some 205311242593580103 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 2 2 205311242593580103 205311242593580103 205311242593580103 endpoint_13_39_window_0 endpoint_13_39_window_2
private theorem endpoint_13_39_window_4 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 4 2 205311242593580103 = some 205311242593580103 := by decide +kernel
private theorem endpoint_13_39_prefix_6 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 6 205311242593580103 = some 205311242593580103 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 4 2 205311242593580103 205311242593580103 205311242593580103 endpoint_13_39_prefix_4 endpoint_13_39_window_4
private theorem endpoint_13_39_window_6 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 6 2 205311242593580103 = some 205311242593580103 := by decide +kernel
private theorem endpoint_13_39_prefix_8 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 8 205311242593580103 = some 205311242593580103 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 6 2 205311242593580103 205311242593580103 205311242593580103 endpoint_13_39_prefix_6 endpoint_13_39_window_6
private theorem endpoint_13_39_window_8 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 8 2 205311242593580103 = some 205311242593580103 := by decide +kernel
private theorem endpoint_13_39_prefix_10 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 10 205311242593580103 = some 205311242593580103 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 8 2 205311242593580103 205311242593580103 205311242593580103 endpoint_13_39_prefix_8 endpoint_13_39_window_8
private theorem endpoint_13_39_window_10 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 10 2 205311242593580103 = some 205311242593580103 := by decide +kernel
private theorem endpoint_13_39_prefix_12 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 12 205311242593580103 = some 205311242593580103 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 10 2 205311242593580103 205311242593580103 205311242593580103 endpoint_13_39_prefix_10 endpoint_13_39_window_10

def endpoint_13_39 : CertifiedEndpoint :=
  ⟨⟨13, 39, 3364⟩, 205311242593580103, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_39_flag endpoint_13_39_sources 12 205311242593580103 205311242593580103 rfl endpoint_13_39_base endpoint_13_39_prefix_12) (by decide)⟩
private def endpoint_13_40_flag : Flag := ⟨13, 40, 3336⟩
private def endpoint_13_40_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_40_base : receiptBase endpoint_13_40_flag endpoint_13_40_sources = some 208404803645566883 := by decide +kernel
private theorem endpoint_13_40_window_0 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 2 208404803645566883 = some 208404803645566883 := by decide +kernel
private theorem endpoint_13_40_window_2 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 2 2 208404803645566883 = some 208404803645566883 := by decide +kernel
private theorem endpoint_13_40_prefix_4 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 4 208404803645566883 = some 208404803645566883 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 2 2 208404803645566883 208404803645566883 208404803645566883 endpoint_13_40_window_0 endpoint_13_40_window_2
private theorem endpoint_13_40_window_4 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 4 2 208404803645566883 = some 208404803645566883 := by decide +kernel
private theorem endpoint_13_40_prefix_6 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 6 208404803645566883 = some 208404803645566883 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 4 2 208404803645566883 208404803645566883 208404803645566883 endpoint_13_40_prefix_4 endpoint_13_40_window_4
private theorem endpoint_13_40_window_6 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 6 2 208404803645566883 = some 208404803645566883 := by decide +kernel
private theorem endpoint_13_40_prefix_8 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 8 208404803645566883 = some 208404803645566883 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 6 2 208404803645566883 208404803645566883 208404803645566883 endpoint_13_40_prefix_6 endpoint_13_40_window_6
private theorem endpoint_13_40_window_8 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 8 2 208404803645566883 = some 208404803645566883 := by decide +kernel
private theorem endpoint_13_40_prefix_10 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 10 208404803645566883 = some 208404803645566883 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 8 2 208404803645566883 208404803645566883 208404803645566883 endpoint_13_40_prefix_8 endpoint_13_40_window_8
private theorem endpoint_13_40_window_10 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 10 2 208404803645566883 = some 208404803645566883 := by decide +kernel
private theorem endpoint_13_40_prefix_12 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 12 208404803645566883 = some 208404803645566883 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 10 2 208404803645566883 208404803645566883 208404803645566883 endpoint_13_40_prefix_10 endpoint_13_40_window_10

def endpoint_13_40 : CertifiedEndpoint :=
  ⟨⟨13, 40, 3336⟩, 208404803645566883, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_40_flag endpoint_13_40_sources 12 208404803645566883 208404803645566883 rfl endpoint_13_40_base endpoint_13_40_prefix_12) (by decide)⟩
private def endpoint_13_41_flag : Flag := ⟨13, 41, 3307⟩
private def endpoint_13_41_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_41_base : receiptBase endpoint_13_41_flag endpoint_13_41_sources = some 210973048460913282 := by decide +kernel
private theorem endpoint_13_41_window_0 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 2 210973048460913282 = some 210973048460913282 := by decide +kernel
private theorem endpoint_13_41_window_2 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 2 2 210973048460913282 = some 210973048460913282 := by decide +kernel
private theorem endpoint_13_41_prefix_4 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 4 210973048460913282 = some 210973048460913282 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 2 2 210973048460913282 210973048460913282 210973048460913282 endpoint_13_41_window_0 endpoint_13_41_window_2
private theorem endpoint_13_41_window_4 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 4 2 210973048460913282 = some 210973048460913282 := by decide +kernel
private theorem endpoint_13_41_prefix_6 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 6 210973048460913282 = some 210973048460913282 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 4 2 210973048460913282 210973048460913282 210973048460913282 endpoint_13_41_prefix_4 endpoint_13_41_window_4
private theorem endpoint_13_41_window_6 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 6 2 210973048460913282 = some 210973048460913282 := by decide +kernel
private theorem endpoint_13_41_prefix_8 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 8 210973048460913282 = some 210973048460913282 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 6 2 210973048460913282 210973048460913282 210973048460913282 endpoint_13_41_prefix_6 endpoint_13_41_window_6
private theorem endpoint_13_41_window_8 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 8 2 210973048460913282 = some 210973048460913282 := by decide +kernel
private theorem endpoint_13_41_prefix_10 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 10 210973048460913282 = some 210973048460913282 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 8 2 210973048460913282 210973048460913282 210973048460913282 endpoint_13_41_prefix_8 endpoint_13_41_window_8
private theorem endpoint_13_41_window_10 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 10 2 210973048460913282 = some 210973048460913282 := by decide +kernel
private theorem endpoint_13_41_prefix_12 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 12 210973048460913282 = some 210973048460913282 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 10 2 210973048460913282 210973048460913282 210973048460913282 endpoint_13_41_prefix_10 endpoint_13_41_window_10

def endpoint_13_41 : CertifiedEndpoint :=
  ⟨⟨13, 41, 3307⟩, 210973048460913282, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_41_flag endpoint_13_41_sources 12 210973048460913282 210973048460913282 rfl endpoint_13_41_base endpoint_13_41_prefix_12) (by decide)⟩
private def endpoint_13_42_flag : Flag := ⟨13, 42, 3277⟩
private def endpoint_13_42_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_42_base : receiptBase endpoint_13_42_flag endpoint_13_42_sources = some 213401132320260225 := by decide +kernel
private theorem endpoint_13_42_window_0 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 2 213401132320260225 = some 213401132320260225 := by decide +kernel
private theorem endpoint_13_42_window_2 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 2 2 213401132320260225 = some 213401132320260225 := by decide +kernel
private theorem endpoint_13_42_prefix_4 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 4 213401132320260225 = some 213401132320260225 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 2 2 213401132320260225 213401132320260225 213401132320260225 endpoint_13_42_window_0 endpoint_13_42_window_2
private theorem endpoint_13_42_window_4 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 4 2 213401132320260225 = some 213401132320260225 := by decide +kernel
private theorem endpoint_13_42_prefix_6 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 6 213401132320260225 = some 213401132320260225 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 4 2 213401132320260225 213401132320260225 213401132320260225 endpoint_13_42_prefix_4 endpoint_13_42_window_4
private theorem endpoint_13_42_window_6 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 6 2 213401132320260225 = some 213401132320260225 := by decide +kernel
private theorem endpoint_13_42_prefix_8 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 8 213401132320260225 = some 213401132320260225 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 6 2 213401132320260225 213401132320260225 213401132320260225 endpoint_13_42_prefix_6 endpoint_13_42_window_6
private theorem endpoint_13_42_window_8 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 8 2 213401132320260225 = some 213401132320260225 := by decide +kernel
private theorem endpoint_13_42_prefix_10 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 10 213401132320260225 = some 213401132320260225 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 8 2 213401132320260225 213401132320260225 213401132320260225 endpoint_13_42_prefix_8 endpoint_13_42_window_8
private theorem endpoint_13_42_window_10 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 10 2 213401132320260225 = some 213401132320260225 := by decide +kernel
private theorem endpoint_13_42_prefix_12 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 12 213401132320260225 = some 213401132320260225 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 10 2 213401132320260225 213401132320260225 213401132320260225 endpoint_13_42_prefix_10 endpoint_13_42_window_10

def endpoint_13_42 : CertifiedEndpoint :=
  ⟨⟨13, 42, 3277⟩, 213401132320260225, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_42_flag endpoint_13_42_sources 12 213401132320260225 213401132320260225 rfl endpoint_13_42_base endpoint_13_42_prefix_12) (by decide)⟩
private def endpoint_13_43_flag : Flag := ⟨13, 43, 3247⟩
private def endpoint_13_43_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_43_base : receiptBase endpoint_13_43_flag endpoint_13_43_sources = some 215750528633786239 := by decide +kernel
private theorem endpoint_13_43_window_0 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 2 215750528633786239 = some 217672199945200732 := by decide +kernel
private theorem endpoint_13_43_window_2 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 2 2 217672199945200732 = some 217672199945200732 := by decide +kernel
private theorem endpoint_13_43_prefix_4 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 4 215750528633786239 = some 217672199945200732 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 2 2 215750528633786239 217672199945200732 217672199945200732 endpoint_13_43_window_0 endpoint_13_43_window_2
private theorem endpoint_13_43_window_4 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 4 2 217672199945200732 = some 217672199945200732 := by decide +kernel
private theorem endpoint_13_43_prefix_6 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 6 215750528633786239 = some 217672199945200732 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 4 2 215750528633786239 217672199945200732 217672199945200732 endpoint_13_43_prefix_4 endpoint_13_43_window_4
private theorem endpoint_13_43_window_6 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 6 2 217672199945200732 = some 217672199945200732 := by decide +kernel
private theorem endpoint_13_43_prefix_8 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 8 215750528633786239 = some 217672199945200732 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 6 2 215750528633786239 217672199945200732 217672199945200732 endpoint_13_43_prefix_6 endpoint_13_43_window_6
private theorem endpoint_13_43_window_8 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 8 2 217672199945200732 = some 217672199945200732 := by decide +kernel
private theorem endpoint_13_43_prefix_10 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 10 215750528633786239 = some 217672199945200732 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 8 2 215750528633786239 217672199945200732 217672199945200732 endpoint_13_43_prefix_8 endpoint_13_43_window_8
private theorem endpoint_13_43_window_10 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 10 2 217672199945200732 = some 217672199945200732 := by decide +kernel
private theorem endpoint_13_43_prefix_12 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 12 215750528633786239 = some 217672199945200732 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 10 2 215750528633786239 217672199945200732 217672199945200732 endpoint_13_43_prefix_10 endpoint_13_43_window_10

def endpoint_13_43 : CertifiedEndpoint :=
  ⟨⟨13, 43, 3247⟩, 217672199945200732, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_43_flag endpoint_13_43_sources 12 215750528633786239 217672199945200732 rfl endpoint_13_43_base endpoint_13_43_prefix_12) (by decide)⟩
private def endpoint_13_44_flag : Flag := ⟨13, 44, 3216⟩
private def endpoint_13_44_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_44_base : receiptBase endpoint_13_44_flag endpoint_13_44_sources = some 217954604447298639 := by decide +kernel
private theorem endpoint_13_44_window_0 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 2 217954604447298639 = some 222653481221050284 := by decide +kernel
private theorem endpoint_13_44_window_2 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 2 2 222653481221050284 = some 222653481221050284 := by decide +kernel
private theorem endpoint_13_44_prefix_4 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 4 217954604447298639 = some 222653481221050284 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 2 2 217954604447298639 222653481221050284 222653481221050284 endpoint_13_44_window_0 endpoint_13_44_window_2
private theorem endpoint_13_44_window_4 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 4 2 222653481221050284 = some 222653481221050284 := by decide +kernel
private theorem endpoint_13_44_prefix_6 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 6 217954604447298639 = some 222653481221050284 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 4 2 217954604447298639 222653481221050284 222653481221050284 endpoint_13_44_prefix_4 endpoint_13_44_window_4
private theorem endpoint_13_44_window_6 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 6 2 222653481221050284 = some 222653481221050284 := by decide +kernel
private theorem endpoint_13_44_prefix_8 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 8 217954604447298639 = some 222653481221050284 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 6 2 217954604447298639 222653481221050284 222653481221050284 endpoint_13_44_prefix_6 endpoint_13_44_window_6
private theorem endpoint_13_44_window_8 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 8 2 222653481221050284 = some 222653481221050284 := by decide +kernel
private theorem endpoint_13_44_prefix_10 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 10 217954604447298639 = some 222653481221050284 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 8 2 217954604447298639 222653481221050284 222653481221050284 endpoint_13_44_prefix_8 endpoint_13_44_window_8
private theorem endpoint_13_44_window_10 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 10 2 222653481221050284 = some 222653481221050284 := by decide +kernel
private theorem endpoint_13_44_prefix_12 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 12 217954604447298639 = some 222653481221050284 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 10 2 217954604447298639 222653481221050284 222653481221050284 endpoint_13_44_prefix_10 endpoint_13_44_window_10

def endpoint_13_44 : CertifiedEndpoint :=
  ⟨⟨13, 44, 3216⟩, 222653481221050284, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_44_flag endpoint_13_44_sources 12 217954604447298639 222653481221050284 rfl endpoint_13_44_base endpoint_13_44_prefix_12) (by decide)⟩
private def endpoint_13_45_flag : Flag := ⟨13, 45, 3185⟩
private def endpoint_13_45_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_45_base : receiptBase endpoint_13_45_flag endpoint_13_45_sources = some 220077412942983031 := by decide +kernel
private theorem endpoint_13_45_window_0 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 2 220077412942983031 = some 227571607699740076 := by decide +kernel
private theorem endpoint_13_45_window_2 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 2 2 227571607699740076 = some 227571607699740076 := by decide +kernel
private theorem endpoint_13_45_prefix_4 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 4 220077412942983031 = some 227571607699740076 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 2 2 220077412942983031 227571607699740076 227571607699740076 endpoint_13_45_window_0 endpoint_13_45_window_2
private theorem endpoint_13_45_window_4 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 4 2 227571607699740076 = some 227571607699740076 := by decide +kernel
private theorem endpoint_13_45_prefix_6 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 6 220077412942983031 = some 227571607699740076 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 4 2 220077412942983031 227571607699740076 227571607699740076 endpoint_13_45_prefix_4 endpoint_13_45_window_4
private theorem endpoint_13_45_window_6 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 6 2 227571607699740076 = some 227571607699740076 := by decide +kernel
private theorem endpoint_13_45_prefix_8 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 8 220077412942983031 = some 227571607699740076 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 6 2 220077412942983031 227571607699740076 227571607699740076 endpoint_13_45_prefix_6 endpoint_13_45_window_6
private theorem endpoint_13_45_window_8 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 8 2 227571607699740076 = some 227571607699740076 := by decide +kernel
private theorem endpoint_13_45_prefix_10 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 10 220077412942983031 = some 227571607699740076 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 8 2 220077412942983031 227571607699740076 227571607699740076 endpoint_13_45_prefix_8 endpoint_13_45_window_8
private theorem endpoint_13_45_window_10 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 10 2 227571607699740076 = some 227571607699740076 := by decide +kernel
private theorem endpoint_13_45_prefix_12 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 12 220077412942983031 = some 227571607699740076 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 10 2 220077412942983031 227571607699740076 227571607699740076 endpoint_13_45_prefix_10 endpoint_13_45_window_10

def endpoint_13_45 : CertifiedEndpoint :=
  ⟨⟨13, 45, 3185⟩, 227571607699740076, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_45_flag endpoint_13_45_sources 12 220077412942983031 227571607699740076 rfl endpoint_13_45_base endpoint_13_45_prefix_12) (by decide)⟩
private def endpoint_13_46_flag : Flag := ⟨13, 46, 3152⟩
private def endpoint_13_46_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_46_base : receiptBase endpoint_13_46_flag endpoint_13_46_sources = some 221980528668439885 := by decide +kernel
private theorem endpoint_13_46_window_0 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 2 221980528668439885 = some 232352274533386568 := by decide +kernel
private theorem endpoint_13_46_window_2 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 2 2 232352274533386568 = some 232352274533386568 := by decide +kernel
private theorem endpoint_13_46_prefix_4 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 4 221980528668439885 = some 232352274533386568 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 2 2 221980528668439885 232352274533386568 232352274533386568 endpoint_13_46_window_0 endpoint_13_46_window_2
private theorem endpoint_13_46_window_4 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 4 2 232352274533386568 = some 232352274533386568 := by decide +kernel
private theorem endpoint_13_46_prefix_6 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 6 221980528668439885 = some 232352274533386568 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 4 2 221980528668439885 232352274533386568 232352274533386568 endpoint_13_46_prefix_4 endpoint_13_46_window_4
private theorem endpoint_13_46_window_6 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 6 2 232352274533386568 = some 232352274533386568 := by decide +kernel
private theorem endpoint_13_46_prefix_8 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 8 221980528668439885 = some 232352274533386568 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 6 2 221980528668439885 232352274533386568 232352274533386568 endpoint_13_46_prefix_6 endpoint_13_46_window_6
private theorem endpoint_13_46_window_8 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 8 2 232352274533386568 = some 232352274533386568 := by decide +kernel
private theorem endpoint_13_46_prefix_10 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 10 221980528668439885 = some 232352274533386568 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 8 2 221980528668439885 232352274533386568 232352274533386568 endpoint_13_46_prefix_8 endpoint_13_46_window_8
private theorem endpoint_13_46_window_10 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 10 2 232352274533386568 = some 232352274533386568 := by decide +kernel
private theorem endpoint_13_46_prefix_12 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 12 221980528668439885 = some 232352274533386568 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 10 2 221980528668439885 232352274533386568 232352274533386568 endpoint_13_46_prefix_10 endpoint_13_46_window_10

def endpoint_13_46 : CertifiedEndpoint :=
  ⟨⟨13, 46, 3152⟩, 232352274533386568, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_46_flag endpoint_13_46_sources 12 221980528668439885 232352274533386568 rfl endpoint_13_46_base endpoint_13_46_prefix_12) (by decide)⟩
private def endpoint_13_47_flag : Flag := ⟨13, 47, 3119⟩
private def endpoint_13_47_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_47_base : receiptBase endpoint_13_47_flag endpoint_13_47_sources = some 223797217532054574 := by decide +kernel
private theorem endpoint_13_47_window_0 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 2 223797217532054574 = some 237065903821133128 := by decide +kernel
private theorem endpoint_13_47_window_2 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 2 2 237065903821133128 = some 237065903821133128 := by decide +kernel
private theorem endpoint_13_47_prefix_4 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 4 223797217532054574 = some 237065903821133128 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 2 2 223797217532054574 237065903821133128 237065903821133128 endpoint_13_47_window_0 endpoint_13_47_window_2
private theorem endpoint_13_47_window_4 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 4 2 237065903821133128 = some 237065903821133128 := by decide +kernel
private theorem endpoint_13_47_prefix_6 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 6 223797217532054574 = some 237065903821133128 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 4 2 223797217532054574 237065903821133128 237065903821133128 endpoint_13_47_prefix_4 endpoint_13_47_window_4
private theorem endpoint_13_47_window_6 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 6 2 237065903821133128 = some 237065903821133128 := by decide +kernel
private theorem endpoint_13_47_prefix_8 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 8 223797217532054574 = some 237065903821133128 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 6 2 223797217532054574 237065903821133128 237065903821133128 endpoint_13_47_prefix_6 endpoint_13_47_window_6
private theorem endpoint_13_47_window_8 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 8 2 237065903821133128 = some 237065903821133128 := by decide +kernel
private theorem endpoint_13_47_prefix_10 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 10 223797217532054574 = some 237065903821133128 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 8 2 223797217532054574 237065903821133128 237065903821133128 endpoint_13_47_prefix_8 endpoint_13_47_window_8
private theorem endpoint_13_47_window_10 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 10 2 237065903821133128 = some 237065903821133128 := by decide +kernel
private theorem endpoint_13_47_prefix_12 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 12 223797217532054574 = some 237065903821133128 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 10 2 223797217532054574 237065903821133128 237065903821133128 endpoint_13_47_prefix_10 endpoint_13_47_window_10

def endpoint_13_47 : CertifiedEndpoint :=
  ⟨⟨13, 47, 3119⟩, 237065903821133128, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_47_flag endpoint_13_47_sources 12 223797217532054574 237065903821133128 rfl endpoint_13_47_base endpoint_13_47_prefix_12) (by decide)⟩
private def endpoint_13_48_flag : Flag := ⟨13, 48, 3086⟩
private def endpoint_13_48_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_48_base : receiptBase endpoint_13_48_flag endpoint_13_48_sources = some 226247357181306069 := by decide +kernel
private theorem endpoint_13_48_window_0 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 2 226247357181306069 = some 237794562475894924 := by decide +kernel
private theorem endpoint_13_48_window_2 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 2 2 237794562475894924 = some 237794562475894924 := by decide +kernel
private theorem endpoint_13_48_prefix_4 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 4 226247357181306069 = some 237794562475894924 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 2 2 226247357181306069 237794562475894924 237794562475894924 endpoint_13_48_window_0 endpoint_13_48_window_2
private theorem endpoint_13_48_window_4 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 4 2 237794562475894924 = some 237794562475894924 := by decide +kernel
private theorem endpoint_13_48_prefix_6 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 6 226247357181306069 = some 237794562475894924 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 4 2 226247357181306069 237794562475894924 237794562475894924 endpoint_13_48_prefix_4 endpoint_13_48_window_4
private theorem endpoint_13_48_window_6 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 6 2 237794562475894924 = some 237794562475894924 := by decide +kernel
private theorem endpoint_13_48_prefix_8 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 8 226247357181306069 = some 237794562475894924 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 6 2 226247357181306069 237794562475894924 237794562475894924 endpoint_13_48_prefix_6 endpoint_13_48_window_6
private theorem endpoint_13_48_window_8 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 8 2 237794562475894924 = some 237794562475894924 := by decide +kernel
private theorem endpoint_13_48_prefix_10 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 10 226247357181306069 = some 237794562475894924 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 8 2 226247357181306069 237794562475894924 237794562475894924 endpoint_13_48_prefix_8 endpoint_13_48_window_8
private theorem endpoint_13_48_window_10 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 10 2 237794562475894924 = some 237794562475894924 := by decide +kernel
private theorem endpoint_13_48_prefix_12 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 12 226247357181306069 = some 237794562475894924 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 10 2 226247357181306069 237794562475894924 237794562475894924 endpoint_13_48_prefix_10 endpoint_13_48_window_10

def endpoint_13_48 : CertifiedEndpoint :=
  ⟨⟨13, 48, 3086⟩, 237794562475894924, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_48_flag endpoint_13_48_sources 12 226247357181306069 237794562475894924 rfl endpoint_13_48_base endpoint_13_48_prefix_12) (by decide)⟩
private def endpoint_13_49_flag : Flag := ⟨13, 49, 3051⟩
private def endpoint_13_49_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_49_base : receiptBase endpoint_13_49_flag endpoint_13_49_sources = some 227754353720573671 := by decide +kernel
private theorem endpoint_13_49_window_0 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 2 227754353720573671 = some 242197915484749374 := by decide +kernel
private theorem endpoint_13_49_window_2 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 2 2 242197915484749374 = some 242197915484749374 := by decide +kernel
private theorem endpoint_13_49_prefix_4 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 4 227754353720573671 = some 242197915484749374 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 2 2 227754353720573671 242197915484749374 242197915484749374 endpoint_13_49_window_0 endpoint_13_49_window_2
private theorem endpoint_13_49_window_4 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 4 2 242197915484749374 = some 242197915484749374 := by decide +kernel
private theorem endpoint_13_49_prefix_6 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 6 227754353720573671 = some 242197915484749374 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 4 2 227754353720573671 242197915484749374 242197915484749374 endpoint_13_49_prefix_4 endpoint_13_49_window_4
private theorem endpoint_13_49_window_6 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 6 2 242197915484749374 = some 242197915484749374 := by decide +kernel
private theorem endpoint_13_49_prefix_8 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 8 227754353720573671 = some 242197915484749374 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 6 2 227754353720573671 242197915484749374 242197915484749374 endpoint_13_49_prefix_6 endpoint_13_49_window_6
private theorem endpoint_13_49_window_8 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 8 2 242197915484749374 = some 242197915484749374 := by decide +kernel
private theorem endpoint_13_49_prefix_10 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 10 227754353720573671 = some 242197915484749374 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 8 2 227754353720573671 242197915484749374 242197915484749374 endpoint_13_49_prefix_8 endpoint_13_49_window_8
private theorem endpoint_13_49_window_10 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 10 2 242197915484749374 = some 242197915484749374 := by decide +kernel
private theorem endpoint_13_49_prefix_12 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 12 227754353720573671 = some 242197915484749374 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 10 2 227754353720573671 242197915484749374 242197915484749374 endpoint_13_49_prefix_10 endpoint_13_49_window_10

def endpoint_13_49 : CertifiedEndpoint :=
  ⟨⟨13, 49, 3051⟩, 242197915484749374, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_49_flag endpoint_13_49_sources 12 227754353720573671 242197915484749374 rfl endpoint_13_49_base endpoint_13_49_prefix_12) (by decide)⟩
private def endpoint_13_50_flag : Flag := ⟨13, 50, 3016⟩
private def endpoint_13_50_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_50_base : receiptBase endpoint_13_50_flag endpoint_13_50_sources = some 229169124802225111 := by decide +kernel
private theorem endpoint_13_50_window_0 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 2 229169124802225111 = some 246530348198963720 := by decide +kernel
private theorem endpoint_13_50_window_2 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 2 2 246530348198963720 = some 246530348198963720 := by decide +kernel
private theorem endpoint_13_50_prefix_4 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 4 229169124802225111 = some 246530348198963720 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 2 2 229169124802225111 246530348198963720 246530348198963720 endpoint_13_50_window_0 endpoint_13_50_window_2
private theorem endpoint_13_50_window_4 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 4 2 246530348198963720 = some 246530348198963720 := by decide +kernel
private theorem endpoint_13_50_prefix_6 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 6 229169124802225111 = some 246530348198963720 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 4 2 229169124802225111 246530348198963720 246530348198963720 endpoint_13_50_prefix_4 endpoint_13_50_window_4
private theorem endpoint_13_50_window_6 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 6 2 246530348198963720 = some 246530348198963720 := by decide +kernel
private theorem endpoint_13_50_prefix_8 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 8 229169124802225111 = some 246530348198963720 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 6 2 229169124802225111 246530348198963720 246530348198963720 endpoint_13_50_prefix_6 endpoint_13_50_window_6
private theorem endpoint_13_50_window_8 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 8 2 246530348198963720 = some 246530348198963720 := by decide +kernel
private theorem endpoint_13_50_prefix_10 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 10 229169124802225111 = some 246530348198963720 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 8 2 229169124802225111 246530348198963720 246530348198963720 endpoint_13_50_prefix_8 endpoint_13_50_window_8
private theorem endpoint_13_50_window_10 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 10 2 246530348198963720 = some 246530348198963720 := by decide +kernel
private theorem endpoint_13_50_prefix_12 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 12 229169124802225111 = some 246530348198963720 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 10 2 229169124802225111 246530348198963720 246530348198963720 endpoint_13_50_prefix_10 endpoint_13_50_window_10

def endpoint_13_50 : CertifiedEndpoint :=
  ⟨⟨13, 50, 3016⟩, 246530348198963720, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_50_flag endpoint_13_50_sources 12 229169124802225111 246530348198963720 rfl endpoint_13_50_base endpoint_13_50_prefix_12) (by decide)⟩
private def endpoint_13_51_flag : Flag := ⟨13, 51, 2979⟩
private def endpoint_13_51_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_51_base : receiptBase endpoint_13_51_flag endpoint_13_51_sources = some 232204046059837563 := by decide +kernel
private theorem endpoint_13_51_window_0 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 2 232204046059837563 = some 243522343100862858 := by decide +kernel
private theorem endpoint_13_51_window_2 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 2 2 243522343100862858 = some 243522343100862858 := by decide +kernel
private theorem endpoint_13_51_prefix_4 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 4 232204046059837563 = some 243522343100862858 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 2 2 232204046059837563 243522343100862858 243522343100862858 endpoint_13_51_window_0 endpoint_13_51_window_2
private theorem endpoint_13_51_window_4 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 4 2 243522343100862858 = some 243522343100862858 := by decide +kernel
private theorem endpoint_13_51_prefix_6 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 6 232204046059837563 = some 243522343100862858 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 4 2 232204046059837563 243522343100862858 243522343100862858 endpoint_13_51_prefix_4 endpoint_13_51_window_4
private theorem endpoint_13_51_window_6 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 6 2 243522343100862858 = some 243522343100862858 := by decide +kernel
private theorem endpoint_13_51_prefix_8 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 8 232204046059837563 = some 243522343100862858 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 6 2 232204046059837563 243522343100862858 243522343100862858 endpoint_13_51_prefix_6 endpoint_13_51_window_6
private theorem endpoint_13_51_window_8 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 8 2 243522343100862858 = some 243522343100862858 := by decide +kernel
private theorem endpoint_13_51_prefix_10 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 10 232204046059837563 = some 243522343100862858 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 8 2 232204046059837563 243522343100862858 243522343100862858 endpoint_13_51_prefix_8 endpoint_13_51_window_8
private theorem endpoint_13_51_window_10 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 10 2 243522343100862858 = some 243522343100862858 := by decide +kernel
private theorem endpoint_13_51_prefix_12 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 12 232204046059837563 = some 243522343100862858 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 10 2 232204046059837563 243522343100862858 243522343100862858 endpoint_13_51_prefix_10 endpoint_13_51_window_10

def endpoint_13_51 : CertifiedEndpoint :=
  ⟨⟨13, 51, 2979⟩, 243522343100862858, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_51_flag endpoint_13_51_sources 12 232204046059837563 243522343100862858 rfl endpoint_13_51_base endpoint_13_51_prefix_12) (by decide)⟩
private def endpoint_13_52_flag : Flag := ⟨13, 52, 2942⟩
private def endpoint_13_52_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_52_base : receiptBase endpoint_13_52_flag endpoint_13_52_sources = some 233224285956860082 := by decide +kernel
private theorem endpoint_13_52_window_0 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 2 233224285956860082 = some 247460917388154672 := by decide +kernel
private theorem endpoint_13_52_window_2 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 2 2 247460917388154672 = some 247460917388154672 := by decide +kernel
private theorem endpoint_13_52_prefix_4 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 4 233224285956860082 = some 247460917388154672 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 2 2 233224285956860082 247460917388154672 247460917388154672 endpoint_13_52_window_0 endpoint_13_52_window_2
private theorem endpoint_13_52_window_4 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 4 2 247460917388154672 = some 247460917388154672 := by decide +kernel
private theorem endpoint_13_52_prefix_6 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 6 233224285956860082 = some 247460917388154672 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 4 2 233224285956860082 247460917388154672 247460917388154672 endpoint_13_52_prefix_4 endpoint_13_52_window_4
private theorem endpoint_13_52_window_6 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 6 2 247460917388154672 = some 247460917388154672 := by decide +kernel
private theorem endpoint_13_52_prefix_8 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 8 233224285956860082 = some 247460917388154672 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 6 2 233224285956860082 247460917388154672 247460917388154672 endpoint_13_52_prefix_6 endpoint_13_52_window_6
private theorem endpoint_13_52_window_8 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 8 2 247460917388154672 = some 247460917388154672 := by decide +kernel
private theorem endpoint_13_52_prefix_10 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 10 233224285956860082 = some 247460917388154672 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 8 2 233224285956860082 247460917388154672 247460917388154672 endpoint_13_52_prefix_8 endpoint_13_52_window_8
private theorem endpoint_13_52_window_10 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 10 2 247460917388154672 = some 247460917388154672 := by decide +kernel
private theorem endpoint_13_52_prefix_12 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 12 233224285956860082 = some 247460917388154672 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 10 2 233224285956860082 247460917388154672 247460917388154672 endpoint_13_52_prefix_10 endpoint_13_52_window_10

def endpoint_13_52 : CertifiedEndpoint :=
  ⟨⟨13, 52, 2942⟩, 247460917388154672, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_52_flag endpoint_13_52_sources 12 233224285956860082 247460917388154672 rfl endpoint_13_52_base endpoint_13_52_prefix_12) (by decide)⟩
private def endpoint_13_53_flag : Flag := ⟨13, 53, 2903⟩
private def endpoint_13_53_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_53_base : receiptBase endpoint_13_53_flag endpoint_13_53_sources = some 233988666086807330 := by decide +kernel
private theorem endpoint_13_53_window_0 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 2 233988666086807330 = some 251236794163592068 := by decide +kernel
private theorem endpoint_13_53_window_2 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 2 2 251236794163592068 = some 251236794163592068 := by decide +kernel
private theorem endpoint_13_53_prefix_4 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 4 233988666086807330 = some 251236794163592068 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 2 2 233988666086807330 251236794163592068 251236794163592068 endpoint_13_53_window_0 endpoint_13_53_window_2
private theorem endpoint_13_53_window_4 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 4 2 251236794163592068 = some 251236794163592068 := by decide +kernel
private theorem endpoint_13_53_prefix_6 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 6 233988666086807330 = some 251236794163592068 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 4 2 233988666086807330 251236794163592068 251236794163592068 endpoint_13_53_prefix_4 endpoint_13_53_window_4
private theorem endpoint_13_53_window_6 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 6 2 251236794163592068 = some 251236794163592068 := by decide +kernel
private theorem endpoint_13_53_prefix_8 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 8 233988666086807330 = some 251236794163592068 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 6 2 233988666086807330 251236794163592068 251236794163592068 endpoint_13_53_prefix_6 endpoint_13_53_window_6
private theorem endpoint_13_53_window_8 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 8 2 251236794163592068 = some 251236794163592068 := by decide +kernel
private theorem endpoint_13_53_prefix_10 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 10 233988666086807330 = some 251236794163592068 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 8 2 233988666086807330 251236794163592068 251236794163592068 endpoint_13_53_prefix_8 endpoint_13_53_window_8
private theorem endpoint_13_53_window_10 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 10 2 251236794163592068 = some 251236794163592068 := by decide +kernel
private theorem endpoint_13_53_prefix_12 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 12 233988666086807330 = some 251236794163592068 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 10 2 233988666086807330 251236794163592068 251236794163592068 endpoint_13_53_prefix_10 endpoint_13_53_window_10

def endpoint_13_53 : CertifiedEndpoint :=
  ⟨⟨13, 53, 2903⟩, 251236794163592068, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_53_flag endpoint_13_53_sources 12 233988666086807330 251236794163592068 rfl endpoint_13_53_base endpoint_13_53_prefix_12) (by decide)⟩
private def endpoint_13_54_flag : Flag := ⟨13, 54, 2863⟩
private def endpoint_13_54_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_54_base : receiptBase endpoint_13_54_flag endpoint_13_54_sources = some 234570105138523015 := by decide +kernel
private theorem endpoint_13_54_window_0 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 2 234570105138523015 = some 254889067225486902 := by decide +kernel
private theorem endpoint_13_54_window_2 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 2 2 254889067225486902 = some 254889067225486902 := by decide +kernel
private theorem endpoint_13_54_prefix_4 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 4 234570105138523015 = some 254889067225486902 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 2 2 234570105138523015 254889067225486902 254889067225486902 endpoint_13_54_window_0 endpoint_13_54_window_2
private theorem endpoint_13_54_window_4 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 4 2 254889067225486902 = some 254889067225486902 := by decide +kernel
private theorem endpoint_13_54_prefix_6 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 6 234570105138523015 = some 254889067225486902 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 4 2 234570105138523015 254889067225486902 254889067225486902 endpoint_13_54_prefix_4 endpoint_13_54_window_4
private theorem endpoint_13_54_window_6 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 6 2 254889067225486902 = some 254889067225486902 := by decide +kernel
private theorem endpoint_13_54_prefix_8 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 8 234570105138523015 = some 254889067225486902 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 6 2 234570105138523015 254889067225486902 254889067225486902 endpoint_13_54_prefix_6 endpoint_13_54_window_6
private theorem endpoint_13_54_window_8 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 8 2 254889067225486902 = some 254889067225486902 := by decide +kernel
private theorem endpoint_13_54_prefix_10 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 10 234570105138523015 = some 254889067225486902 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 8 2 234570105138523015 254889067225486902 254889067225486902 endpoint_13_54_prefix_8 endpoint_13_54_window_8
private theorem endpoint_13_54_window_10 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 10 2 254889067225486902 = some 254889067225486902 := by decide +kernel
private theorem endpoint_13_54_prefix_12 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 12 234570105138523015 = some 254889067225486902 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 10 2 234570105138523015 254889067225486902 254889067225486902 endpoint_13_54_prefix_10 endpoint_13_54_window_10

def endpoint_13_54 : CertifiedEndpoint :=
  ⟨⟨13, 54, 2863⟩, 254889067225486902, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_54_flag endpoint_13_54_sources 12 234570105138523015 254889067225486902 rfl endpoint_13_54_base endpoint_13_54_prefix_12) (by decide)⟩
private def endpoint_13_55_flag : Flag := ⟨13, 55, 2822⟩
private def endpoint_13_55_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_13_55_base : receiptBase endpoint_13_55_flag endpoint_13_55_sources = some 235813849359924127 := by decide +kernel
private theorem endpoint_13_55_window_0 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 2 235813849359924127 = some 250668459375165474 := by decide +kernel
private theorem endpoint_13_55_window_2 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 2 2 250668459375165474 = some 250668459375165474 := by decide +kernel
private theorem endpoint_13_55_prefix_4 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 4 235813849359924127 = some 250668459375165474 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 2 2 235813849359924127 250668459375165474 250668459375165474 endpoint_13_55_window_0 endpoint_13_55_window_2
private theorem endpoint_13_55_window_4 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 4 2 250668459375165474 = some 250668459375165474 := by decide +kernel
private theorem endpoint_13_55_prefix_6 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 6 235813849359924127 = some 250668459375165474 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 4 2 235813849359924127 250668459375165474 250668459375165474 endpoint_13_55_prefix_4 endpoint_13_55_window_4
private theorem endpoint_13_55_window_6 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 6 2 250668459375165474 = some 250668459375165474 := by decide +kernel
private theorem endpoint_13_55_prefix_8 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 8 235813849359924127 = some 250668459375165474 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 6 2 235813849359924127 250668459375165474 250668459375165474 endpoint_13_55_prefix_6 endpoint_13_55_window_6
private theorem endpoint_13_55_window_8 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 8 2 250668459375165474 = some 250668459375165474 := by decide +kernel
private theorem endpoint_13_55_prefix_10 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 10 235813849359924127 = some 250668459375165474 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 8 2 235813849359924127 250668459375165474 250668459375165474 endpoint_13_55_prefix_8 endpoint_13_55_window_8
private theorem endpoint_13_55_window_10 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 10 2 250668459375165474 = some 250668459375165474 := by decide +kernel
private theorem endpoint_13_55_prefix_12 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 12 235813849359924127 = some 250668459375165474 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 10 2 235813849359924127 250668459375165474 250668459375165474 endpoint_13_55_prefix_10 endpoint_13_55_window_10

def endpoint_13_55 : CertifiedEndpoint :=
  ⟨⟨13, 55, 2822⟩, 250668459375165474, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_13_55_flag endpoint_13_55_sources 12 235813849359924127 250668459375165474 rfl endpoint_13_55_base endpoint_13_55_prefix_12) (by decide)⟩
private def endpoint_13_56_flag : Flag := ⟨13, 56, 2779⟩
private def endpoint_13_56_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_13_56_base : receiptBase endpoint_13_56_flag endpoint_13_56_sources = some 235938142346747275 := by decide +kernel
private theorem endpoint_13_56_window_0 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 2 235938142346747275 = some 253855807664851466 := by decide +kernel
private theorem endpoint_13_56_window_2 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 2 2 253855807664851466 = some 253855807664851466 := by decide +kernel
private theorem endpoint_13_56_prefix_4 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 4 235938142346747275 = some 253855807664851466 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 2 2 235938142346747275 253855807664851466 253855807664851466 endpoint_13_56_window_0 endpoint_13_56_window_2
private theorem endpoint_13_56_window_4 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 4 2 253855807664851466 = some 253855807664851466 := by decide +kernel
private theorem endpoint_13_56_prefix_6 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 6 235938142346747275 = some 253855807664851466 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 4 2 235938142346747275 253855807664851466 253855807664851466 endpoint_13_56_prefix_4 endpoint_13_56_window_4
private theorem endpoint_13_56_window_6 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 6 2 253855807664851466 = some 253855807664851466 := by decide +kernel
private theorem endpoint_13_56_prefix_8 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 8 235938142346747275 = some 253855807664851466 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 6 2 235938142346747275 253855807664851466 253855807664851466 endpoint_13_56_prefix_6 endpoint_13_56_window_6
private theorem endpoint_13_56_window_8 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 8 2 253855807664851466 = some 253855807664851466 := by decide +kernel
private theorem endpoint_13_56_prefix_10 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 10 235938142346747275 = some 253855807664851466 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 8 2 235938142346747275 253855807664851466 253855807664851466 endpoint_13_56_prefix_8 endpoint_13_56_window_8
private theorem endpoint_13_56_window_10 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 10 2 253855807664851466 = some 253855807664851466 := by decide +kernel
private theorem endpoint_13_56_prefix_12 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 12 235938142346747275 = some 253855807664851466 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 10 2 235938142346747275 253855807664851466 253855807664851466 endpoint_13_56_prefix_10 endpoint_13_56_window_10

def endpoint_13_56 : CertifiedEndpoint :=
  ⟨⟨13, 56, 2779⟩, 253855807664851466, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_13_56_flag endpoint_13_56_sources 12 235938142346747275 253855807664851466 rfl endpoint_13_56_base endpoint_13_56_prefix_12) (by decide)⟩
private def endpoint_13_57_flag : Flag := ⟨13, 57, 2735⟩
private def endpoint_13_57_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_13_57_base : receiptBase endpoint_13_57_flag endpoint_13_57_sources = some 235864080240626504 := by decide +kernel
private theorem endpoint_13_57_window_0 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 2 235864080240626504 = some 256908874681959423 := by decide +kernel
private theorem endpoint_13_57_window_2 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 2 2 256908874681959423 = some 256908874681959423 := by decide +kernel
private theorem endpoint_13_57_prefix_4 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 4 235864080240626504 = some 256908874681959423 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 2 2 235864080240626504 256908874681959423 256908874681959423 endpoint_13_57_window_0 endpoint_13_57_window_2
private theorem endpoint_13_57_window_4 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 4 2 256908874681959423 = some 256908874681959423 := by decide +kernel
private theorem endpoint_13_57_prefix_6 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 6 235864080240626504 = some 256908874681959423 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 4 2 235864080240626504 256908874681959423 256908874681959423 endpoint_13_57_prefix_4 endpoint_13_57_window_4
private theorem endpoint_13_57_window_6 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 6 2 256908874681959423 = some 256908874681959423 := by decide +kernel
private theorem endpoint_13_57_prefix_8 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 8 235864080240626504 = some 256908874681959423 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 6 2 235864080240626504 256908874681959423 256908874681959423 endpoint_13_57_prefix_6 endpoint_13_57_window_6
private theorem endpoint_13_57_window_8 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 8 2 256908874681959423 = some 256908874681959423 := by decide +kernel
private theorem endpoint_13_57_prefix_10 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 10 235864080240626504 = some 256908874681959423 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 8 2 235864080240626504 256908874681959423 256908874681959423 endpoint_13_57_prefix_8 endpoint_13_57_window_8
private theorem endpoint_13_57_window_10 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 10 2 256908874681959423 = some 256908874681959423 := by decide +kernel
private theorem endpoint_13_57_prefix_12 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 12 235864080240626504 = some 256908874681959423 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 10 2 235864080240626504 256908874681959423 256908874681959423 endpoint_13_57_prefix_10 endpoint_13_57_window_10

def endpoint_13_57 : CertifiedEndpoint :=
  ⟨⟨13, 57, 2735⟩, 256908874681959423, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_13_57_flag endpoint_13_57_sources 12 235864080240626504 256908874681959423 rfl endpoint_13_57_base endpoint_13_57_prefix_12) (by decide)⟩
private def endpoint_13_58_flag : Flag := ⟨13, 58, 2689⟩
private def endpoint_13_58_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_13_58_base : receiptBase endpoint_13_58_flag endpoint_13_58_sources = some 236417225698163133 := by decide +kernel
private theorem endpoint_13_58_window_0 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 2 236417225698163133 = some 253880905936688178 := by decide +kernel
private theorem endpoint_13_58_window_2 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 2 2 253880905936688178 = some 253880905936688178 := by decide +kernel
private theorem endpoint_13_58_prefix_4 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 4 236417225698163133 = some 253880905936688178 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 2 2 236417225698163133 253880905936688178 253880905936688178 endpoint_13_58_window_0 endpoint_13_58_window_2
private theorem endpoint_13_58_window_4 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 4 2 253880905936688178 = some 253880905936688178 := by decide +kernel
private theorem endpoint_13_58_prefix_6 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 6 236417225698163133 = some 253880905936688178 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 4 2 236417225698163133 253880905936688178 253880905936688178 endpoint_13_58_prefix_4 endpoint_13_58_window_4
private theorem endpoint_13_58_window_6 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 6 2 253880905936688178 = some 253880905936688178 := by decide +kernel
private theorem endpoint_13_58_prefix_8 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 8 236417225698163133 = some 253880905936688178 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 6 2 236417225698163133 253880905936688178 253880905936688178 endpoint_13_58_prefix_6 endpoint_13_58_window_6
private theorem endpoint_13_58_window_8 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 8 2 253880905936688178 = some 253880905936688178 := by decide +kernel
private theorem endpoint_13_58_prefix_10 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 10 236417225698163133 = some 253880905936688178 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 8 2 236417225698163133 253880905936688178 253880905936688178 endpoint_13_58_prefix_8 endpoint_13_58_window_8
private theorem endpoint_13_58_window_10 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 10 2 253880905936688178 = some 253880905936688178 := by decide +kernel
private theorem endpoint_13_58_prefix_12 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 12 236417225698163133 = some 253880905936688178 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 10 2 236417225698163133 253880905936688178 253880905936688178 endpoint_13_58_prefix_10 endpoint_13_58_window_10

def endpoint_13_58 : CertifiedEndpoint :=
  ⟨⟨13, 58, 2689⟩, 253880905936688178, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_13_58_flag endpoint_13_58_sources 12 236417225698163133 253880905936688178 rfl endpoint_13_58_base endpoint_13_58_prefix_12) (by decide)⟩
private def endpoint_13_59_flag : Flag := ⟨13, 59, 2642⟩
private def endpoint_13_59_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_13_59_base : receiptBase endpoint_13_59_flag endpoint_13_59_sources = some 235846828785754071 := by decide +kernel
private theorem endpoint_13_59_window_0 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 2 235846828785754071 = some 256489844918323348 := by decide +kernel
private theorem endpoint_13_59_window_2 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 2 2 256489844918323348 = some 256489844918323348 := by decide +kernel
private theorem endpoint_13_59_prefix_4 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 4 235846828785754071 = some 256489844918323348 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 2 2 235846828785754071 256489844918323348 256489844918323348 endpoint_13_59_window_0 endpoint_13_59_window_2
private theorem endpoint_13_59_window_4 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 4 2 256489844918323348 = some 256489844918323348 := by decide +kernel
private theorem endpoint_13_59_prefix_6 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 6 235846828785754071 = some 256489844918323348 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 4 2 235846828785754071 256489844918323348 256489844918323348 endpoint_13_59_prefix_4 endpoint_13_59_window_4
private theorem endpoint_13_59_window_6 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 6 2 256489844918323348 = some 256489844918323348 := by decide +kernel
private theorem endpoint_13_59_prefix_8 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 8 235846828785754071 = some 256489844918323348 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 6 2 235846828785754071 256489844918323348 256489844918323348 endpoint_13_59_prefix_6 endpoint_13_59_window_6
private theorem endpoint_13_59_window_8 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 8 2 256489844918323348 = some 256489844918323348 := by decide +kernel
private theorem endpoint_13_59_prefix_10 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 10 235846828785754071 = some 256489844918323348 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 8 2 235846828785754071 256489844918323348 256489844918323348 endpoint_13_59_prefix_8 endpoint_13_59_window_8
private theorem endpoint_13_59_window_10 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 10 2 256489844918323348 = some 256489844918323348 := by decide +kernel
private theorem endpoint_13_59_prefix_12 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 12 235846828785754071 = some 256489844918323348 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 10 2 235846828785754071 256489844918323348 256489844918323348 endpoint_13_59_prefix_10 endpoint_13_59_window_10

def endpoint_13_59 : CertifiedEndpoint :=
  ⟨⟨13, 59, 2642⟩, 256489844918323348, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_13_59_flag endpoint_13_59_sources 12 235846828785754071 256489844918323348 rfl endpoint_13_59_base endpoint_13_59_prefix_12) (by decide)⟩
private def endpoint_13_60_flag : Flag := ⟨13, 60, 2592⟩
private def endpoint_13_60_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_13_60_base : receiptBase endpoint_13_60_flag endpoint_13_60_sources = some 235850906413280208 := by decide +kernel
private theorem endpoint_13_60_window_0 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 2 235850906413280208 = some 254732316239063972 := by decide +kernel
private theorem endpoint_13_60_window_2 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 2 2 254732316239063972 = some 254732316239063972 := by decide +kernel
private theorem endpoint_13_60_prefix_4 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 4 235850906413280208 = some 254732316239063972 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 2 2 235850906413280208 254732316239063972 254732316239063972 endpoint_13_60_window_0 endpoint_13_60_window_2
private theorem endpoint_13_60_window_4 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 4 2 254732316239063972 = some 254732316239063972 := by decide +kernel
private theorem endpoint_13_60_prefix_6 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 6 235850906413280208 = some 254732316239063972 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 4 2 235850906413280208 254732316239063972 254732316239063972 endpoint_13_60_prefix_4 endpoint_13_60_window_4
private theorem endpoint_13_60_window_6 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 6 2 254732316239063972 = some 254732316239063972 := by decide +kernel
private theorem endpoint_13_60_prefix_8 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 8 235850906413280208 = some 254732316239063972 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 6 2 235850906413280208 254732316239063972 254732316239063972 endpoint_13_60_prefix_6 endpoint_13_60_window_6
private theorem endpoint_13_60_window_8 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 8 2 254732316239063972 = some 254732316239063972 := by decide +kernel
private theorem endpoint_13_60_prefix_10 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 10 235850906413280208 = some 254732316239063972 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 8 2 235850906413280208 254732316239063972 254732316239063972 endpoint_13_60_prefix_8 endpoint_13_60_window_8
private theorem endpoint_13_60_window_10 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 10 2 254732316239063972 = some 254732316239063972 := by decide +kernel
private theorem endpoint_13_60_prefix_12 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 12 235850906413280208 = some 254732316239063972 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 10 2 235850906413280208 254732316239063972 254732316239063972 endpoint_13_60_prefix_10 endpoint_13_60_window_10

def endpoint_13_60 : CertifiedEndpoint :=
  ⟨⟨13, 60, 2592⟩, 254732316239063972, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_13_60_flag endpoint_13_60_sources 12 235850906413280208 254732316239063972 rfl endpoint_13_60_base endpoint_13_60_prefix_12) (by decide)⟩
private def endpoint_13_61_flag : Flag := ⟨13, 61, 2541⟩
private def endpoint_13_61_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_13_61_base : receiptBase endpoint_13_61_flag endpoint_13_61_sources = some 235667830460208549 := by decide +kernel
private theorem endpoint_13_61_window_0 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 2 235667830460208549 = some 254173920869842167 := by decide +kernel
private theorem endpoint_13_61_window_2 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 2 2 254173920869842167 = some 254173920869842167 := by decide +kernel
private theorem endpoint_13_61_prefix_4 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 4 235667830460208549 = some 254173920869842167 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 2 2 235667830460208549 254173920869842167 254173920869842167 endpoint_13_61_window_0 endpoint_13_61_window_2
private theorem endpoint_13_61_window_4 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 4 2 254173920869842167 = some 254173920869842167 := by decide +kernel
private theorem endpoint_13_61_prefix_6 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 6 235667830460208549 = some 254173920869842167 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 4 2 235667830460208549 254173920869842167 254173920869842167 endpoint_13_61_prefix_4 endpoint_13_61_window_4
private theorem endpoint_13_61_window_6 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 6 2 254173920869842167 = some 254173920869842167 := by decide +kernel
private theorem endpoint_13_61_prefix_8 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 8 235667830460208549 = some 254173920869842167 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 6 2 235667830460208549 254173920869842167 254173920869842167 endpoint_13_61_prefix_6 endpoint_13_61_window_6
private theorem endpoint_13_61_window_8 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 8 2 254173920869842167 = some 254173920869842167 := by decide +kernel
private theorem endpoint_13_61_prefix_10 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 10 235667830460208549 = some 254173920869842167 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 8 2 235667830460208549 254173920869842167 254173920869842167 endpoint_13_61_prefix_8 endpoint_13_61_window_8
private theorem endpoint_13_61_window_10 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 10 2 254173920869842167 = some 254173920869842167 := by decide +kernel
private theorem endpoint_13_61_prefix_12 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 12 235667830460208549 = some 254173920869842167 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 10 2 235667830460208549 254173920869842167 254173920869842167 endpoint_13_61_prefix_10 endpoint_13_61_window_10

def endpoint_13_61 : CertifiedEndpoint :=
  ⟨⟨13, 61, 2541⟩, 254173920869842167, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_13_61_flag endpoint_13_61_sources 12 235667830460208549 254173920869842167 rfl endpoint_13_61_base endpoint_13_61_prefix_12) (by decide)⟩
private def endpoint_13_62_flag : Flag := ⟨13, 62, 2487⟩
private def endpoint_13_62_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_62_base : receiptBase endpoint_13_62_flag endpoint_13_62_sources = some 234944146294063900 := by decide +kernel
private theorem endpoint_13_62_window_0 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 2 234944146294063900 = some 248431052297824446 := by decide +kernel
private theorem endpoint_13_62_window_2 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 2 2 248431052297824446 = some 248431052297824446 := by decide +kernel
private theorem endpoint_13_62_prefix_4 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 4 234944146294063900 = some 248431052297824446 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 2 2 234944146294063900 248431052297824446 248431052297824446 endpoint_13_62_window_0 endpoint_13_62_window_2
private theorem endpoint_13_62_window_4 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 4 2 248431052297824446 = some 248431052297824446 := by decide +kernel
private theorem endpoint_13_62_prefix_6 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 6 234944146294063900 = some 248431052297824446 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 4 2 234944146294063900 248431052297824446 248431052297824446 endpoint_13_62_prefix_4 endpoint_13_62_window_4
private theorem endpoint_13_62_window_6 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 6 2 248431052297824446 = some 248431052297824446 := by decide +kernel
private theorem endpoint_13_62_prefix_8 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 8 234944146294063900 = some 248431052297824446 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 6 2 234944146294063900 248431052297824446 248431052297824446 endpoint_13_62_prefix_6 endpoint_13_62_window_6
private theorem endpoint_13_62_window_8 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 8 2 248431052297824446 = some 248431052297824446 := by decide +kernel
private theorem endpoint_13_62_prefix_10 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 10 234944146294063900 = some 248431052297824446 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 8 2 234944146294063900 248431052297824446 248431052297824446 endpoint_13_62_prefix_8 endpoint_13_62_window_8
private theorem endpoint_13_62_window_10 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 10 2 248431052297824446 = some 248431052297824446 := by decide +kernel
private theorem endpoint_13_62_prefix_12 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 12 234944146294063900 = some 248431052297824446 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 10 2 234944146294063900 248431052297824446 248431052297824446 endpoint_13_62_prefix_10 endpoint_13_62_window_10

def endpoint_13_62 : CertifiedEndpoint :=
  ⟨⟨13, 62, 2487⟩, 248431052297824446, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_62_flag endpoint_13_62_sources 12 234944146294063900 248431052297824446 rfl endpoint_13_62_base endpoint_13_62_prefix_12) (by decide)⟩
private def endpoint_13_63_flag : Flag := ⟨13, 63, 2431⟩
private def endpoint_13_63_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_63_base : receiptBase endpoint_13_63_flag endpoint_13_63_sources = some 233000308087848819 := by decide +kernel
private theorem endpoint_13_63_window_0 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 2 233000308087848819 = some 249900447456984178 := by decide +kernel
private theorem endpoint_13_63_window_2 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 2 2 249900447456984178 = some 249900447456984178 := by decide +kernel
private theorem endpoint_13_63_prefix_4 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 4 233000308087848819 = some 249900447456984178 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 2 2 233000308087848819 249900447456984178 249900447456984178 endpoint_13_63_window_0 endpoint_13_63_window_2
private theorem endpoint_13_63_window_4 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 4 2 249900447456984178 = some 249900447456984178 := by decide +kernel
private theorem endpoint_13_63_prefix_6 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 6 233000308087848819 = some 249900447456984178 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 4 2 233000308087848819 249900447456984178 249900447456984178 endpoint_13_63_prefix_4 endpoint_13_63_window_4
private theorem endpoint_13_63_window_6 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 6 2 249900447456984178 = some 249900447456984178 := by decide +kernel
private theorem endpoint_13_63_prefix_8 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 8 233000308087848819 = some 249900447456984178 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 6 2 233000308087848819 249900447456984178 249900447456984178 endpoint_13_63_prefix_6 endpoint_13_63_window_6
private theorem endpoint_13_63_window_8 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 8 2 249900447456984178 = some 249900447456984178 := by decide +kernel
private theorem endpoint_13_63_prefix_10 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 10 233000308087848819 = some 249900447456984178 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 8 2 233000308087848819 249900447456984178 249900447456984178 endpoint_13_63_prefix_8 endpoint_13_63_window_8
private theorem endpoint_13_63_window_10 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 10 2 249900447456984178 = some 249900447456984178 := by decide +kernel
private theorem endpoint_13_63_prefix_12 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 12 233000308087848819 = some 249900447456984178 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 10 2 233000308087848819 249900447456984178 249900447456984178 endpoint_13_63_prefix_10 endpoint_13_63_window_10

def endpoint_13_63 : CertifiedEndpoint :=
  ⟨⟨13, 63, 2431⟩, 249900447456984178, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_63_flag endpoint_13_63_sources 12 233000308087848819 249900447456984178 rfl endpoint_13_63_base endpoint_13_63_prefix_12) (by decide)⟩
private def endpoint_13_64_flag : Flag := ⟨13, 64, 2373⟩
private def endpoint_13_64_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_64_base : receiptBase endpoint_13_64_flag endpoint_13_64_sources = some 230713304882468867 := by decide +kernel
private theorem endpoint_13_64_window_0 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 2 230713304882468867 = some 251148903873186912 := by decide +kernel
private theorem endpoint_13_64_window_2 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 2 2 251148903873186912 = some 251148903873186912 := by decide +kernel
private theorem endpoint_13_64_prefix_4 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 4 230713304882468867 = some 251148903873186912 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 2 2 230713304882468867 251148903873186912 251148903873186912 endpoint_13_64_window_0 endpoint_13_64_window_2
private theorem endpoint_13_64_window_4 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 4 2 251148903873186912 = some 251148903873186912 := by decide +kernel
private theorem endpoint_13_64_prefix_6 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 6 230713304882468867 = some 251148903873186912 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 4 2 230713304882468867 251148903873186912 251148903873186912 endpoint_13_64_prefix_4 endpoint_13_64_window_4
private theorem endpoint_13_64_window_6 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 6 2 251148903873186912 = some 251148903873186912 := by decide +kernel
private theorem endpoint_13_64_prefix_8 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 8 230713304882468867 = some 251148903873186912 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 6 2 230713304882468867 251148903873186912 251148903873186912 endpoint_13_64_prefix_6 endpoint_13_64_window_6
private theorem endpoint_13_64_window_8 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 8 2 251148903873186912 = some 251148903873186912 := by decide +kernel
private theorem endpoint_13_64_prefix_10 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 10 230713304882468867 = some 251148903873186912 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 8 2 230713304882468867 251148903873186912 251148903873186912 endpoint_13_64_prefix_8 endpoint_13_64_window_8
private theorem endpoint_13_64_window_10 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 10 2 251148903873186912 = some 251148903873186912 := by decide +kernel
private theorem endpoint_13_64_prefix_12 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 12 230713304882468867 = some 251148903873186912 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 10 2 230713304882468867 251148903873186912 251148903873186912 endpoint_13_64_prefix_10 endpoint_13_64_window_10

def endpoint_13_64 : CertifiedEndpoint :=
  ⟨⟨13, 64, 2373⟩, 251148903873186912, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_64_flag endpoint_13_64_sources 12 230713304882468867 251148903873186912 rfl endpoint_13_64_base endpoint_13_64_prefix_12) (by decide)⟩
private def endpoint_13_65_flag : Flag := ⟨13, 65, 2313⟩
private def endpoint_13_65_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_65_base : receiptBase endpoint_13_65_flag endpoint_13_65_sources = some 233570381112191564 := by decide +kernel
private theorem endpoint_13_65_window_0 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 2 233570381112191564 = some 239102239799036877 := by decide +kernel
private theorem endpoint_13_65_window_2 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 2 2 239102239799036877 = some 239102239799036877 := by decide +kernel
private theorem endpoint_13_65_prefix_4 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 4 233570381112191564 = some 239102239799036877 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 2 2 233570381112191564 239102239799036877 239102239799036877 endpoint_13_65_window_0 endpoint_13_65_window_2
private theorem endpoint_13_65_window_4 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 4 2 239102239799036877 = some 239102239799036877 := by decide +kernel
private theorem endpoint_13_65_prefix_6 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 6 233570381112191564 = some 239102239799036877 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 4 2 233570381112191564 239102239799036877 239102239799036877 endpoint_13_65_prefix_4 endpoint_13_65_window_4
private theorem endpoint_13_65_window_6 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 6 2 239102239799036877 = some 239102239799036877 := by decide +kernel
private theorem endpoint_13_65_prefix_8 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 8 233570381112191564 = some 239102239799036877 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 6 2 233570381112191564 239102239799036877 239102239799036877 endpoint_13_65_prefix_6 endpoint_13_65_window_6
private theorem endpoint_13_65_window_8 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 8 2 239102239799036877 = some 239102239799036877 := by decide +kernel
private theorem endpoint_13_65_prefix_10 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 10 233570381112191564 = some 239102239799036877 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 8 2 233570381112191564 239102239799036877 239102239799036877 endpoint_13_65_prefix_8 endpoint_13_65_window_8
private theorem endpoint_13_65_window_10 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 10 2 239102239799036877 = some 239102239799036877 := by decide +kernel
private theorem endpoint_13_65_prefix_12 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 12 233570381112191564 = some 239102239799036877 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 10 2 233570381112191564 239102239799036877 239102239799036877 endpoint_13_65_prefix_10 endpoint_13_65_window_10

def endpoint_13_65 : CertifiedEndpoint :=
  ⟨⟨13, 65, 2313⟩, 239102239799036877, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_65_flag endpoint_13_65_sources 12 233570381112191564 239102239799036877 rfl endpoint_13_65_base endpoint_13_65_prefix_12) (by decide)⟩
private def endpoint_13_66_flag : Flag := ⟨13, 66, 2251⟩
private def endpoint_13_66_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_66_base : receiptBase endpoint_13_66_flag endpoint_13_66_sources = some 230542420773765089 := by decide +kernel
private theorem endpoint_13_66_window_0 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 2 230542420773765089 = some 239665176351263078 := by decide +kernel
private theorem endpoint_13_66_window_2 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 2 2 239665176351263078 = some 239665176351263078 := by decide +kernel
private theorem endpoint_13_66_prefix_4 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 4 230542420773765089 = some 239665176351263078 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 2 2 230542420773765089 239665176351263078 239665176351263078 endpoint_13_66_window_0 endpoint_13_66_window_2
private theorem endpoint_13_66_window_4 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 4 2 239665176351263078 = some 239665176351263078 := by decide +kernel
private theorem endpoint_13_66_prefix_6 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 6 230542420773765089 = some 239665176351263078 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 4 2 230542420773765089 239665176351263078 239665176351263078 endpoint_13_66_prefix_4 endpoint_13_66_window_4
private theorem endpoint_13_66_window_6 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 6 2 239665176351263078 = some 239665176351263078 := by decide +kernel
private theorem endpoint_13_66_prefix_8 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 8 230542420773765089 = some 239665176351263078 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 6 2 230542420773765089 239665176351263078 239665176351263078 endpoint_13_66_prefix_6 endpoint_13_66_window_6
private theorem endpoint_13_66_window_8 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 8 2 239665176351263078 = some 239665176351263078 := by decide +kernel
private theorem endpoint_13_66_prefix_10 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 10 230542420773765089 = some 239665176351263078 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 8 2 230542420773765089 239665176351263078 239665176351263078 endpoint_13_66_prefix_8 endpoint_13_66_window_8
private theorem endpoint_13_66_window_10 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 10 2 239665176351263078 = some 239665176351263078 := by decide +kernel
private theorem endpoint_13_66_prefix_12 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 12 230542420773765089 = some 239665176351263078 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 10 2 230542420773765089 239665176351263078 239665176351263078 endpoint_13_66_prefix_10 endpoint_13_66_window_10

def endpoint_13_66 : CertifiedEndpoint :=
  ⟨⟨13, 66, 2251⟩, 239665176351263078, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_66_flag endpoint_13_66_sources 12 230542420773765089 239665176351263078 rfl endpoint_13_66_base endpoint_13_66_prefix_12) (by decide)⟩
private def endpoint_13_67_flag : Flag := ⟨13, 67, 2186⟩
private def endpoint_13_67_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_67_base : receiptBase endpoint_13_67_flag endpoint_13_67_sources = some 227043043221431759 := by decide +kernel
private theorem endpoint_13_67_window_0 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 2 227043043221431759 = some 239932164936373834 := by decide +kernel
private theorem endpoint_13_67_window_2 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 2 2 239932164936373834 = some 239932164936373834 := by decide +kernel
private theorem endpoint_13_67_prefix_4 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 4 227043043221431759 = some 239932164936373834 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 2 2 227043043221431759 239932164936373834 239932164936373834 endpoint_13_67_window_0 endpoint_13_67_window_2
private theorem endpoint_13_67_window_4 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 4 2 239932164936373834 = some 239932164936373834 := by decide +kernel
private theorem endpoint_13_67_prefix_6 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 6 227043043221431759 = some 239932164936373834 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 4 2 227043043221431759 239932164936373834 239932164936373834 endpoint_13_67_prefix_4 endpoint_13_67_window_4
private theorem endpoint_13_67_window_6 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 6 2 239932164936373834 = some 239932164936373834 := by decide +kernel
private theorem endpoint_13_67_prefix_8 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 8 227043043221431759 = some 239932164936373834 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 6 2 227043043221431759 239932164936373834 239932164936373834 endpoint_13_67_prefix_6 endpoint_13_67_window_6
private theorem endpoint_13_67_window_8 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 8 2 239932164936373834 = some 239932164936373834 := by decide +kernel
private theorem endpoint_13_67_prefix_10 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 10 227043043221431759 = some 239932164936373834 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 8 2 227043043221431759 239932164936373834 239932164936373834 endpoint_13_67_prefix_8 endpoint_13_67_window_8
private theorem endpoint_13_67_window_10 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 10 2 239932164936373834 = some 239932164936373834 := by decide +kernel
private theorem endpoint_13_67_prefix_12 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 12 227043043221431759 = some 239932164936373834 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 10 2 227043043221431759 239932164936373834 239932164936373834 endpoint_13_67_prefix_10 endpoint_13_67_window_10

def endpoint_13_67 : CertifiedEndpoint :=
  ⟨⟨13, 67, 2186⟩, 239932164936373834, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_67_flag endpoint_13_67_sources 12 227043043221431759 239932164936373834 rfl endpoint_13_67_base endpoint_13_67_prefix_12) (by decide)⟩
private def endpoint_13_68_flag : Flag := ⟨13, 68, 2118⟩
private def endpoint_13_68_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_68_base : receiptBase endpoint_13_68_flag endpoint_13_68_sources = some 223060174318872623 := by decide +kernel
private theorem endpoint_13_68_window_0 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 2 223060174318872623 = some 239894469369703758 := by decide +kernel
private theorem endpoint_13_68_window_2 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 2 2 239894469369703758 = some 239894469369703758 := by decide +kernel
private theorem endpoint_13_68_prefix_4 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 4 223060174318872623 = some 239894469369703758 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 2 2 223060174318872623 239894469369703758 239894469369703758 endpoint_13_68_window_0 endpoint_13_68_window_2
private theorem endpoint_13_68_window_4 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 4 2 239894469369703758 = some 239894469369703758 := by decide +kernel
private theorem endpoint_13_68_prefix_6 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 6 223060174318872623 = some 239894469369703758 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 4 2 223060174318872623 239894469369703758 239894469369703758 endpoint_13_68_prefix_4 endpoint_13_68_window_4
private theorem endpoint_13_68_window_6 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 6 2 239894469369703758 = some 239894469369703758 := by decide +kernel
private theorem endpoint_13_68_prefix_8 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 8 223060174318872623 = some 239894469369703758 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 6 2 223060174318872623 239894469369703758 239894469369703758 endpoint_13_68_prefix_6 endpoint_13_68_window_6
private theorem endpoint_13_68_window_8 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 8 2 239894469369703758 = some 239894469369703758 := by decide +kernel
private theorem endpoint_13_68_prefix_10 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 10 223060174318872623 = some 239894469369703758 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 8 2 223060174318872623 239894469369703758 239894469369703758 endpoint_13_68_prefix_8 endpoint_13_68_window_8
private theorem endpoint_13_68_window_10 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 10 2 239894469369703758 = some 239894469369703758 := by decide +kernel
private theorem endpoint_13_68_prefix_12 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 12 223060174318872623 = some 239894469369703758 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 10 2 223060174318872623 239894469369703758 239894469369703758 endpoint_13_68_prefix_10 endpoint_13_68_window_10

def endpoint_13_68 : CertifiedEndpoint :=
  ⟨⟨13, 68, 2118⟩, 239894469369703758, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_68_flag endpoint_13_68_sources 12 223060174318872623 239894469369703758 rfl endpoint_13_68_base endpoint_13_68_prefix_12) (by decide)⟩
private def endpoint_13_69_flag : Flag := ⟨13, 69, 2048⟩
private def endpoint_13_69_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_13_69_base : receiptBase endpoint_13_69_flag endpoint_13_69_sources = some 219872616561934441 := by decide +kernel
private theorem endpoint_13_69_window_0 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 2 219872616561934441 = some 227113656442860717 := by decide +kernel
private theorem endpoint_13_69_window_2 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 2 2 227113656442860717 = some 227113656442860717 := by decide +kernel
private theorem endpoint_13_69_prefix_4 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 4 219872616561934441 = some 227113656442860717 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 2 2 219872616561934441 227113656442860717 227113656442860717 endpoint_13_69_window_0 endpoint_13_69_window_2
private theorem endpoint_13_69_window_4 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 4 2 227113656442860717 = some 227113656442860717 := by decide +kernel
private theorem endpoint_13_69_prefix_6 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 6 219872616561934441 = some 227113656442860717 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 4 2 219872616561934441 227113656442860717 227113656442860717 endpoint_13_69_prefix_4 endpoint_13_69_window_4
private theorem endpoint_13_69_window_6 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 6 2 227113656442860717 = some 227113656442860717 := by decide +kernel
private theorem endpoint_13_69_prefix_8 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 8 219872616561934441 = some 227113656442860717 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 6 2 219872616561934441 227113656442860717 227113656442860717 endpoint_13_69_prefix_6 endpoint_13_69_window_6
private theorem endpoint_13_69_window_8 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 8 2 227113656442860717 = some 227113656442860717 := by decide +kernel
private theorem endpoint_13_69_prefix_10 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 10 219872616561934441 = some 227113656442860717 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 8 2 219872616561934441 227113656442860717 227113656442860717 endpoint_13_69_prefix_8 endpoint_13_69_window_8
private theorem endpoint_13_69_window_10 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 10 2 227113656442860717 = some 227113656442860717 := by decide +kernel
private theorem endpoint_13_69_prefix_12 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 12 219872616561934441 = some 227113656442860717 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 10 2 219872616561934441 227113656442860717 227113656442860717 endpoint_13_69_prefix_10 endpoint_13_69_window_10

def endpoint_13_69 : CertifiedEndpoint :=
  ⟨⟨13, 69, 2048⟩, 227113656442860717, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_13_69_flag endpoint_13_69_sources 12 219872616561934441 227113656442860717 rfl endpoint_13_69_base endpoint_13_69_prefix_12) (by decide)⟩
private def endpoint_13_70_flag : Flag := ⟨13, 70, 1976⟩
private def endpoint_13_70_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_13_70_base : receiptBase endpoint_13_70_flag endpoint_13_70_sources = some 215005951072886641 := by decide +kernel
private theorem endpoint_13_70_window_0 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 2 215005951072886641 = some 226360100583876312 := by decide +kernel
private theorem endpoint_13_70_window_2 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 2 2 226360100583876312 = some 226360100583876312 := by decide +kernel
private theorem endpoint_13_70_prefix_4 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 4 215005951072886641 = some 226360100583876312 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 2 2 215005951072886641 226360100583876312 226360100583876312 endpoint_13_70_window_0 endpoint_13_70_window_2
private theorem endpoint_13_70_window_4 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 4 2 226360100583876312 = some 226360100583876312 := by decide +kernel
private theorem endpoint_13_70_prefix_6 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 6 215005951072886641 = some 226360100583876312 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 4 2 215005951072886641 226360100583876312 226360100583876312 endpoint_13_70_prefix_4 endpoint_13_70_window_4
private theorem endpoint_13_70_window_6 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 6 2 226360100583876312 = some 226360100583876312 := by decide +kernel
private theorem endpoint_13_70_prefix_8 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 8 215005951072886641 = some 226360100583876312 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 6 2 215005951072886641 226360100583876312 226360100583876312 endpoint_13_70_prefix_6 endpoint_13_70_window_6
private theorem endpoint_13_70_window_8 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 8 2 226360100583876312 = some 226360100583876312 := by decide +kernel
private theorem endpoint_13_70_prefix_10 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 10 215005951072886641 = some 226360100583876312 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 8 2 215005951072886641 226360100583876312 226360100583876312 endpoint_13_70_prefix_8 endpoint_13_70_window_8
private theorem endpoint_13_70_window_10 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 10 2 226360100583876312 = some 226360100583876312 := by decide +kernel
private theorem endpoint_13_70_prefix_12 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 12 215005951072886641 = some 226360100583876312 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 10 2 215005951072886641 226360100583876312 226360100583876312 endpoint_13_70_prefix_10 endpoint_13_70_window_10

def endpoint_13_70 : CertifiedEndpoint :=
  ⟨⟨13, 70, 1976⟩, 226360100583876312, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_13_70_flag endpoint_13_70_sources 12 215005951072886641 226360100583876312 rfl endpoint_13_70_base endpoint_13_70_prefix_12) (by decide)⟩
private def endpoint_13_71_flag : Flag := ⟨13, 71, 1901⟩
private def endpoint_13_71_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_13_71_base : receiptBase endpoint_13_71_flag endpoint_13_71_sources = some 210980601298698896 := by decide +kernel
private theorem endpoint_13_71_window_0 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 2 210980601298698896 = some 218896624291449736 := by decide +kernel
private theorem endpoint_13_71_window_2 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 2 2 218896624291449736 = some 218896624291449736 := by decide +kernel
private theorem endpoint_13_71_prefix_4 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 4 210980601298698896 = some 218896624291449736 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 2 2 210980601298698896 218896624291449736 218896624291449736 endpoint_13_71_window_0 endpoint_13_71_window_2
private theorem endpoint_13_71_window_4 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 4 2 218896624291449736 = some 218896624291449736 := by decide +kernel
private theorem endpoint_13_71_prefix_6 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 6 210980601298698896 = some 218896624291449736 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 4 2 210980601298698896 218896624291449736 218896624291449736 endpoint_13_71_prefix_4 endpoint_13_71_window_4
private theorem endpoint_13_71_window_6 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 6 2 218896624291449736 = some 218896624291449736 := by decide +kernel
private theorem endpoint_13_71_prefix_8 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 8 210980601298698896 = some 218896624291449736 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 6 2 210980601298698896 218896624291449736 218896624291449736 endpoint_13_71_prefix_6 endpoint_13_71_window_6
private theorem endpoint_13_71_window_8 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 8 2 218896624291449736 = some 218896624291449736 := by decide +kernel
private theorem endpoint_13_71_prefix_10 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 10 210980601298698896 = some 218896624291449736 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 8 2 210980601298698896 218896624291449736 218896624291449736 endpoint_13_71_prefix_8 endpoint_13_71_window_8
private theorem endpoint_13_71_window_10 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 10 2 218896624291449736 = some 218896624291449736 := by decide +kernel
private theorem endpoint_13_71_prefix_12 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 12 210980601298698896 = some 218896624291449736 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 10 2 210980601298698896 218896624291449736 218896624291449736 endpoint_13_71_prefix_10 endpoint_13_71_window_10

def endpoint_13_71 : CertifiedEndpoint :=
  ⟨⟨13, 71, 1901⟩, 218896624291449736, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_13_71_flag endpoint_13_71_sources 12 210980601298698896 218896624291449736 rfl endpoint_13_71_base endpoint_13_71_prefix_12) (by decide)⟩
private def endpoint_13_72_flag : Flag := ⟨13, 72, 1824⟩
private def endpoint_13_72_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_13_72_base : receiptBase endpoint_13_72_flag endpoint_13_72_sources = some 205089348661636858 := by decide +kernel
private theorem endpoint_13_72_window_0 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 2 205089348661636858 = some 217442627399376640 := by decide +kernel
private theorem endpoint_13_72_window_2 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 2 2 217442627399376640 = some 217442627399376640 := by decide +kernel
private theorem endpoint_13_72_prefix_4 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 4 205089348661636858 = some 217442627399376640 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 2 2 205089348661636858 217442627399376640 217442627399376640 endpoint_13_72_window_0 endpoint_13_72_window_2
private theorem endpoint_13_72_window_4 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 4 2 217442627399376640 = some 217442627399376640 := by decide +kernel
private theorem endpoint_13_72_prefix_6 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 6 205089348661636858 = some 217442627399376640 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 4 2 205089348661636858 217442627399376640 217442627399376640 endpoint_13_72_prefix_4 endpoint_13_72_window_4
private theorem endpoint_13_72_window_6 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 6 2 217442627399376640 = some 217442627399376640 := by decide +kernel
private theorem endpoint_13_72_prefix_8 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 8 205089348661636858 = some 217442627399376640 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 6 2 205089348661636858 217442627399376640 217442627399376640 endpoint_13_72_prefix_6 endpoint_13_72_window_6
private theorem endpoint_13_72_window_8 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 8 2 217442627399376640 = some 217442627399376640 := by decide +kernel
private theorem endpoint_13_72_prefix_10 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 10 205089348661636858 = some 217442627399376640 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 8 2 205089348661636858 217442627399376640 217442627399376640 endpoint_13_72_prefix_8 endpoint_13_72_window_8
private theorem endpoint_13_72_window_10 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 10 2 217442627399376640 = some 217442627399376640 := by decide +kernel
private theorem endpoint_13_72_prefix_12 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 12 205089348661636858 = some 217442627399376640 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 10 2 205089348661636858 217442627399376640 217442627399376640 endpoint_13_72_prefix_10 endpoint_13_72_window_10

def endpoint_13_72 : CertifiedEndpoint :=
  ⟨⟨13, 72, 1824⟩, 217442627399376640, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_13_72_flag endpoint_13_72_sources 12 205089348661636858 217442627399376640 rfl endpoint_13_72_base endpoint_13_72_prefix_12) (by decide)⟩
private def endpoint_13_73_flag : Flag := ⟨13, 73, 1744⟩
private def endpoint_13_73_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_13_73_base : receiptBase endpoint_13_73_flag endpoint_13_73_sources = some 200080482791626322 := by decide +kernel
private theorem endpoint_13_73_window_0 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 2 200080482791626322 = some 200900033079698627 := by decide +kernel
private theorem endpoint_13_73_window_2 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 2 2 200900033079698627 = some 200900033079698627 := by decide +kernel
private theorem endpoint_13_73_prefix_4 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 4 200080482791626322 = some 200900033079698627 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 2 2 200080482791626322 200900033079698627 200900033079698627 endpoint_13_73_window_0 endpoint_13_73_window_2
private theorem endpoint_13_73_window_4 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 4 2 200900033079698627 = some 200900033079698627 := by decide +kernel
private theorem endpoint_13_73_prefix_6 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 6 200080482791626322 = some 200900033079698627 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 4 2 200080482791626322 200900033079698627 200900033079698627 endpoint_13_73_prefix_4 endpoint_13_73_window_4
private theorem endpoint_13_73_window_6 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 6 2 200900033079698627 = some 200900033079698627 := by decide +kernel
private theorem endpoint_13_73_prefix_8 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 8 200080482791626322 = some 200900033079698627 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 6 2 200080482791626322 200900033079698627 200900033079698627 endpoint_13_73_prefix_6 endpoint_13_73_window_6
private theorem endpoint_13_73_window_8 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 8 2 200900033079698627 = some 200900033079698627 := by decide +kernel
private theorem endpoint_13_73_prefix_10 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 10 200080482791626322 = some 200900033079698627 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 8 2 200080482791626322 200900033079698627 200900033079698627 endpoint_13_73_prefix_8 endpoint_13_73_window_8
private theorem endpoint_13_73_window_10 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 10 2 200900033079698627 = some 200900033079698627 := by decide +kernel
private theorem endpoint_13_73_prefix_12 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 12 200080482791626322 = some 200900033079698627 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 10 2 200080482791626322 200900033079698627 200900033079698627 endpoint_13_73_prefix_10 endpoint_13_73_window_10

def endpoint_13_73 : CertifiedEndpoint :=
  ⟨⟨13, 73, 1744⟩, 200900033079698627, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_13_73_flag endpoint_13_73_sources 12 200080482791626322 200900033079698627 rfl endpoint_13_73_base endpoint_13_73_prefix_12) (by decide)⟩
private def endpoint_13_74_flag : Flag := ⟨13, 74, 1662⟩
private def endpoint_13_74_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_13_74_base : receiptBase endpoint_13_74_flag endpoint_13_74_sources = some 193103818477281927 := by decide +kernel
private theorem endpoint_13_74_window_0 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 2 193103818477281927 = some 198592381259858388 := by decide +kernel
private theorem endpoint_13_74_window_2 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 2 2 198592381259858388 = some 198592381259858388 := by decide +kernel
private theorem endpoint_13_74_prefix_4 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 4 193103818477281927 = some 198592381259858388 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 2 2 193103818477281927 198592381259858388 198592381259858388 endpoint_13_74_window_0 endpoint_13_74_window_2
private theorem endpoint_13_74_window_4 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 4 2 198592381259858388 = some 198592381259858388 := by decide +kernel
private theorem endpoint_13_74_prefix_6 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 6 193103818477281927 = some 198592381259858388 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 4 2 193103818477281927 198592381259858388 198592381259858388 endpoint_13_74_prefix_4 endpoint_13_74_window_4
private theorem endpoint_13_74_window_6 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 6 2 198592381259858388 = some 198592381259858388 := by decide +kernel
private theorem endpoint_13_74_prefix_8 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 8 193103818477281927 = some 198592381259858388 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 6 2 193103818477281927 198592381259858388 198592381259858388 endpoint_13_74_prefix_6 endpoint_13_74_window_6
private theorem endpoint_13_74_window_8 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 8 2 198592381259858388 = some 198592381259858388 := by decide +kernel
private theorem endpoint_13_74_prefix_10 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 10 193103818477281927 = some 198592381259858388 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 8 2 193103818477281927 198592381259858388 198592381259858388 endpoint_13_74_prefix_8 endpoint_13_74_window_8
private theorem endpoint_13_74_window_10 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 10 2 198592381259858388 = some 198592381259858388 := by decide +kernel
private theorem endpoint_13_74_prefix_12 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 12 193103818477281927 = some 198592381259858388 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 10 2 193103818477281927 198592381259858388 198592381259858388 endpoint_13_74_prefix_10 endpoint_13_74_window_10

def endpoint_13_74 : CertifiedEndpoint :=
  ⟨⟨13, 74, 1662⟩, 198592381259858388, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_13_74_flag endpoint_13_74_sources 12 193103818477281927 198592381259858388 rfl endpoint_13_74_base endpoint_13_74_prefix_12) (by decide)⟩
private def endpoint_13_75_flag : Flag := ⟨13, 75, 1577⟩
private def endpoint_13_75_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_13_75_base : receiptBase endpoint_13_75_flag endpoint_13_75_sources = some 185550039378606038 := by decide +kernel
private theorem endpoint_13_75_window_0 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 2 185550039378606038 = some 195926657493059952 := by decide +kernel
private theorem endpoint_13_75_window_2 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 2 2 195926657493059952 = some 195926657493059952 := by decide +kernel
private theorem endpoint_13_75_prefix_4 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 4 185550039378606038 = some 195926657493059952 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 2 2 185550039378606038 195926657493059952 195926657493059952 endpoint_13_75_window_0 endpoint_13_75_window_2
private theorem endpoint_13_75_window_4 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 4 2 195926657493059952 = some 195926657493059952 := by decide +kernel
private theorem endpoint_13_75_prefix_6 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 6 185550039378606038 = some 195926657493059952 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 4 2 185550039378606038 195926657493059952 195926657493059952 endpoint_13_75_prefix_4 endpoint_13_75_window_4
private theorem endpoint_13_75_window_6 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 6 2 195926657493059952 = some 195926657493059952 := by decide +kernel
private theorem endpoint_13_75_prefix_8 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 8 185550039378606038 = some 195926657493059952 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 6 2 185550039378606038 195926657493059952 195926657493059952 endpoint_13_75_prefix_6 endpoint_13_75_window_6
private theorem endpoint_13_75_window_8 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 8 2 195926657493059952 = some 195926657493059952 := by decide +kernel
private theorem endpoint_13_75_prefix_10 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 10 185550039378606038 = some 195926657493059952 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 8 2 185550039378606038 195926657493059952 195926657493059952 endpoint_13_75_prefix_8 endpoint_13_75_window_8
private theorem endpoint_13_75_window_10 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 10 2 195926657493059952 = some 195926657493059952 := by decide +kernel
private theorem endpoint_13_75_prefix_12 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 12 185550039378606038 = some 195926657493059952 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 10 2 185550039378606038 195926657493059952 195926657493059952 endpoint_13_75_prefix_10 endpoint_13_75_window_10

def endpoint_13_75 : CertifiedEndpoint :=
  ⟨⟨13, 75, 1577⟩, 195926657493059952, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_13_75_flag endpoint_13_75_sources 12 185550039378606038 195926657493059952 rfl endpoint_13_75_base endpoint_13_75_prefix_12) (by decide)⟩
private def endpoint_13_76_flag : Flag := ⟨13, 76, 1490⟩
private def endpoint_13_76_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_13_76_base : receiptBase endpoint_13_76_flag endpoint_13_76_sources = some 180257963428938958 := by decide +kernel
private theorem endpoint_13_76_window_0 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 2 180257963428938958 = some 180257963428938958 := by decide +kernel
private theorem endpoint_13_76_window_2 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 2 2 180257963428938958 = some 180257963428938958 := by decide +kernel
private theorem endpoint_13_76_prefix_4 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 4 180257963428938958 = some 180257963428938958 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 2 2 180257963428938958 180257963428938958 180257963428938958 endpoint_13_76_window_0 endpoint_13_76_window_2
private theorem endpoint_13_76_window_4 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 4 2 180257963428938958 = some 180257963428938958 := by decide +kernel
private theorem endpoint_13_76_prefix_6 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 6 180257963428938958 = some 180257963428938958 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 4 2 180257963428938958 180257963428938958 180257963428938958 endpoint_13_76_prefix_4 endpoint_13_76_window_4
private theorem endpoint_13_76_window_6 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 6 2 180257963428938958 = some 180257963428938958 := by decide +kernel
private theorem endpoint_13_76_prefix_8 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 8 180257963428938958 = some 180257963428938958 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 6 2 180257963428938958 180257963428938958 180257963428938958 endpoint_13_76_prefix_6 endpoint_13_76_window_6
private theorem endpoint_13_76_window_8 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 8 2 180257963428938958 = some 180257963428938958 := by decide +kernel
private theorem endpoint_13_76_prefix_10 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 10 180257963428938958 = some 180257963428938958 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 8 2 180257963428938958 180257963428938958 180257963428938958 endpoint_13_76_prefix_8 endpoint_13_76_window_8
private theorem endpoint_13_76_window_10 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 10 2 180257963428938958 = some 180257963428938958 := by decide +kernel
private theorem endpoint_13_76_prefix_12 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 12 180257963428938958 = some 180257963428938958 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 10 2 180257963428938958 180257963428938958 180257963428938958 endpoint_13_76_prefix_10 endpoint_13_76_window_10

def endpoint_13_76 : CertifiedEndpoint :=
  ⟨⟨13, 76, 1490⟩, 180257963428938958, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_13_76_flag endpoint_13_76_sources 12 180257963428938958 180257963428938958 rfl endpoint_13_76_base endpoint_13_76_prefix_12) (by decide)⟩
private def endpoint_13_77_flag : Flag := ⟨13, 77, 1399⟩
private def endpoint_13_77_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_13_77_base : receiptBase endpoint_13_77_flag endpoint_13_77_sources = some 171315343506764498 := by decide +kernel
private theorem endpoint_13_77_window_0 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 2 171315343506764498 = some 174050229850619201 := by decide +kernel
private theorem endpoint_13_77_window_2 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 2 2 174050229850619201 = some 174050229850619201 := by decide +kernel
private theorem endpoint_13_77_prefix_4 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 4 171315343506764498 = some 174050229850619201 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 2 2 171315343506764498 174050229850619201 174050229850619201 endpoint_13_77_window_0 endpoint_13_77_window_2
private theorem endpoint_13_77_window_4 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 4 2 174050229850619201 = some 174050229850619201 := by decide +kernel
private theorem endpoint_13_77_prefix_6 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 6 171315343506764498 = some 174050229850619201 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 4 2 171315343506764498 174050229850619201 174050229850619201 endpoint_13_77_prefix_4 endpoint_13_77_window_4
private theorem endpoint_13_77_window_6 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 6 2 174050229850619201 = some 174050229850619201 := by decide +kernel
private theorem endpoint_13_77_prefix_8 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 8 171315343506764498 = some 174050229850619201 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 6 2 171315343506764498 174050229850619201 174050229850619201 endpoint_13_77_prefix_6 endpoint_13_77_window_6
private theorem endpoint_13_77_window_8 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 8 2 174050229850619201 = some 174050229850619201 := by decide +kernel
private theorem endpoint_13_77_prefix_10 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 10 171315343506764498 = some 174050229850619201 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 8 2 171315343506764498 174050229850619201 174050229850619201 endpoint_13_77_prefix_8 endpoint_13_77_window_8
private theorem endpoint_13_77_window_10 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 10 2 174050229850619201 = some 174050229850619201 := by decide +kernel
private theorem endpoint_13_77_prefix_12 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 12 171315343506764498 = some 174050229850619201 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 10 2 171315343506764498 174050229850619201 174050229850619201 endpoint_13_77_prefix_10 endpoint_13_77_window_10

def endpoint_13_77 : CertifiedEndpoint :=
  ⟨⟨13, 77, 1399⟩, 174050229850619201, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_13_77_flag endpoint_13_77_sources 12 171315343506764498 174050229850619201 rfl endpoint_13_77_base endpoint_13_77_prefix_12) (by decide)⟩

def endpointBlock08 : List CertifiedEndpoint := [
  endpoint_12_76, endpoint_12_77, endpoint_12_78, endpoint_12_79, endpoint_12_80, endpoint_12_81,
  endpoint_12_82, endpoint_12_83, endpoint_12_84, endpoint_12_85, endpoint_12_86, endpoint_12_87,
  endpoint_12_88, endpoint_12_89, endpoint_12_90, endpoint_13_13, endpoint_13_14, endpoint_13_15,
  endpoint_13_16, endpoint_13_17, endpoint_13_18, endpoint_13_19, endpoint_13_20, endpoint_13_21,
  endpoint_13_22, endpoint_13_23, endpoint_13_24, endpoint_13_25, endpoint_13_26, endpoint_13_27,
  endpoint_13_28, endpoint_13_29, endpoint_13_30, endpoint_13_31, endpoint_13_32, endpoint_13_33,
  endpoint_13_34, endpoint_13_35, endpoint_13_36, endpoint_13_37, endpoint_13_38, endpoint_13_39,
  endpoint_13_40, endpoint_13_41, endpoint_13_42, endpoint_13_43, endpoint_13_44, endpoint_13_45,
  endpoint_13_46, endpoint_13_47, endpoint_13_48, endpoint_13_49, endpoint_13_50, endpoint_13_51,
  endpoint_13_52, endpoint_13_53, endpoint_13_54, endpoint_13_55, endpoint_13_56, endpoint_13_57,
  endpoint_13_58, endpoint_13_59, endpoint_13_60, endpoint_13_61, endpoint_13_62, endpoint_13_63,
  endpoint_13_64, endpoint_13_65, endpoint_13_66, endpoint_13_67, endpoint_13_68, endpoint_13_69,
  endpoint_13_70, endpoint_13_71, endpoint_13_72, endpoint_13_73, endpoint_13_74, endpoint_13_75,
  endpoint_13_76, endpoint_13_77
]

end ProximityPrize.SubmissionLower.Koala6844Receipts
