import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


private def endpoint_16_40_flag : Flag := ⟨16, 40, 2850⟩
private def endpoint_16_40_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_40_base : receiptBase endpoint_16_40_flag endpoint_16_40_sources = some 208882130502348889 := by decide +kernel
private theorem endpoint_16_40_window_0 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 2 208882130502348889 = some 208882130502348889 := by decide +kernel
private theorem endpoint_16_40_window_2 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 2 2 208882130502348889 = some 208882130502348889 := by decide +kernel
private theorem endpoint_16_40_prefix_4 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 4 208882130502348889 = some 208882130502348889 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 2 2 208882130502348889 208882130502348889 208882130502348889 endpoint_16_40_window_0 endpoint_16_40_window_2
private theorem endpoint_16_40_window_4 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 4 2 208882130502348889 = some 208882130502348889 := by decide +kernel
private theorem endpoint_16_40_prefix_6 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 6 208882130502348889 = some 208882130502348889 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 4 2 208882130502348889 208882130502348889 208882130502348889 endpoint_16_40_prefix_4 endpoint_16_40_window_4
private theorem endpoint_16_40_window_6 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 6 2 208882130502348889 = some 208882130502348889 := by decide +kernel
private theorem endpoint_16_40_prefix_8 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 8 208882130502348889 = some 208882130502348889 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 6 2 208882130502348889 208882130502348889 208882130502348889 endpoint_16_40_prefix_6 endpoint_16_40_window_6
private theorem endpoint_16_40_window_8 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 8 2 208882130502348889 = some 208882130502348889 := by decide +kernel
private theorem endpoint_16_40_prefix_10 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 10 208882130502348889 = some 208882130502348889 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 8 2 208882130502348889 208882130502348889 208882130502348889 endpoint_16_40_prefix_8 endpoint_16_40_window_8
private theorem endpoint_16_40_window_10 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 10 2 208882130502348889 = some 208882130502348889 := by decide +kernel
private theorem endpoint_16_40_prefix_12 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 12 208882130502348889 = some 208882130502348889 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 10 2 208882130502348889 208882130502348889 208882130502348889 endpoint_16_40_prefix_10 endpoint_16_40_window_10
private theorem endpoint_16_40_window_12 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 12 2 208882130502348889 = some 208882130502348889 := by decide +kernel
private theorem endpoint_16_40_prefix_14 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 14 208882130502348889 = some 208882130502348889 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 12 2 208882130502348889 208882130502348889 208882130502348889 endpoint_16_40_prefix_12 endpoint_16_40_window_12
private theorem endpoint_16_40_window_14 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 14 1 208882130502348889 = some 208882130502348889 := by decide +kernel
private theorem endpoint_16_40_prefix_15 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 15 208882130502348889 = some 208882130502348889 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 14 1 208882130502348889 208882130502348889 208882130502348889 endpoint_16_40_prefix_14 endpoint_16_40_window_14

def endpoint_16_40 : CertifiedEndpoint :=
  ⟨⟨16, 40, 2850⟩, 208882130502348889, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_40_flag endpoint_16_40_sources 15 208882130502348889 208882130502348889 rfl endpoint_16_40_base endpoint_16_40_prefix_15) (by decide)⟩
private def endpoint_16_41_flag : Flag := ⟨16, 41, 2814⟩
private def endpoint_16_41_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_41_base : receiptBase endpoint_16_41_flag endpoint_16_41_sources = some 210631528704440905 := by decide +kernel
private theorem endpoint_16_41_window_0 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 2 210631528704440905 = some 210631528704440905 := by decide +kernel
private theorem endpoint_16_41_window_2 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 2 2 210631528704440905 = some 210631528704440905 := by decide +kernel
private theorem endpoint_16_41_prefix_4 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 4 210631528704440905 = some 210631528704440905 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 2 2 210631528704440905 210631528704440905 210631528704440905 endpoint_16_41_window_0 endpoint_16_41_window_2
private theorem endpoint_16_41_window_4 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 4 2 210631528704440905 = some 210631528704440905 := by decide +kernel
private theorem endpoint_16_41_prefix_6 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 6 210631528704440905 = some 210631528704440905 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 4 2 210631528704440905 210631528704440905 210631528704440905 endpoint_16_41_prefix_4 endpoint_16_41_window_4
private theorem endpoint_16_41_window_6 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 6 2 210631528704440905 = some 210631528704440905 := by decide +kernel
private theorem endpoint_16_41_prefix_8 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 8 210631528704440905 = some 210631528704440905 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 6 2 210631528704440905 210631528704440905 210631528704440905 endpoint_16_41_prefix_6 endpoint_16_41_window_6
private theorem endpoint_16_41_window_8 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 8 2 210631528704440905 = some 210631528704440905 := by decide +kernel
private theorem endpoint_16_41_prefix_10 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 10 210631528704440905 = some 210631528704440905 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 8 2 210631528704440905 210631528704440905 210631528704440905 endpoint_16_41_prefix_8 endpoint_16_41_window_8
private theorem endpoint_16_41_window_10 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 10 2 210631528704440905 = some 210631528704440905 := by decide +kernel
private theorem endpoint_16_41_prefix_12 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 12 210631528704440905 = some 210631528704440905 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 10 2 210631528704440905 210631528704440905 210631528704440905 endpoint_16_41_prefix_10 endpoint_16_41_window_10
private theorem endpoint_16_41_window_12 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 12 2 210631528704440905 = some 210631528704440905 := by decide +kernel
private theorem endpoint_16_41_prefix_14 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 14 210631528704440905 = some 210631528704440905 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 12 2 210631528704440905 210631528704440905 210631528704440905 endpoint_16_41_prefix_12 endpoint_16_41_window_12
private theorem endpoint_16_41_window_14 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 14 1 210631528704440905 = some 210631528704440905 := by decide +kernel
private theorem endpoint_16_41_prefix_15 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 15 210631528704440905 = some 210631528704440905 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 14 1 210631528704440905 210631528704440905 210631528704440905 endpoint_16_41_prefix_14 endpoint_16_41_window_14

def endpoint_16_41 : CertifiedEndpoint :=
  ⟨⟨16, 41, 2814⟩, 210631528704440905, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_41_flag endpoint_16_41_sources 15 210631528704440905 210631528704440905 rfl endpoint_16_41_base endpoint_16_41_prefix_15) (by decide)⟩
private def endpoint_16_42_flag : Flag := ⟨16, 42, 2777⟩
private def endpoint_16_42_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_42_base : receiptBase endpoint_16_42_flag endpoint_16_42_sources = some 212194778496498006 := by decide +kernel
private theorem endpoint_16_42_window_0 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 2 212194778496498006 = some 213688664785021904 := by decide +kernel
private theorem endpoint_16_42_window_2 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 2 2 213688664785021904 = some 213688664785021904 := by decide +kernel
private theorem endpoint_16_42_prefix_4 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 4 212194778496498006 = some 213688664785021904 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 2 2 212194778496498006 213688664785021904 213688664785021904 endpoint_16_42_window_0 endpoint_16_42_window_2
private theorem endpoint_16_42_window_4 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 4 2 213688664785021904 = some 213688664785021904 := by decide +kernel
private theorem endpoint_16_42_prefix_6 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 6 212194778496498006 = some 213688664785021904 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 4 2 212194778496498006 213688664785021904 213688664785021904 endpoint_16_42_prefix_4 endpoint_16_42_window_4
private theorem endpoint_16_42_window_6 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 6 2 213688664785021904 = some 213688664785021904 := by decide +kernel
private theorem endpoint_16_42_prefix_8 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 8 212194778496498006 = some 213688664785021904 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 6 2 212194778496498006 213688664785021904 213688664785021904 endpoint_16_42_prefix_6 endpoint_16_42_window_6
private theorem endpoint_16_42_window_8 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 8 2 213688664785021904 = some 213688664785021904 := by decide +kernel
private theorem endpoint_16_42_prefix_10 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 10 212194778496498006 = some 213688664785021904 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 8 2 212194778496498006 213688664785021904 213688664785021904 endpoint_16_42_prefix_8 endpoint_16_42_window_8
private theorem endpoint_16_42_window_10 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 10 2 213688664785021904 = some 213688664785021904 := by decide +kernel
private theorem endpoint_16_42_prefix_12 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 12 212194778496498006 = some 213688664785021904 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 10 2 212194778496498006 213688664785021904 213688664785021904 endpoint_16_42_prefix_10 endpoint_16_42_window_10
private theorem endpoint_16_42_window_12 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 12 2 213688664785021904 = some 213688664785021904 := by decide +kernel
private theorem endpoint_16_42_prefix_14 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 14 212194778496498006 = some 213688664785021904 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 12 2 212194778496498006 213688664785021904 213688664785021904 endpoint_16_42_prefix_12 endpoint_16_42_window_12
private theorem endpoint_16_42_window_14 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 14 1 213688664785021904 = some 213688664785021904 := by decide +kernel
private theorem endpoint_16_42_prefix_15 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 15 212194778496498006 = some 213688664785021904 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 14 1 212194778496498006 213688664785021904 213688664785021904 endpoint_16_42_prefix_14 endpoint_16_42_window_14

def endpoint_16_42 : CertifiedEndpoint :=
  ⟨⟨16, 42, 2777⟩, 213688664785021904, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_42_flag endpoint_16_42_sources 15 212194778496498006 213688664785021904 rfl endpoint_16_42_base endpoint_16_42_prefix_15) (by decide)⟩
private def endpoint_16_43_flag : Flag := ⟨16, 43, 2739⟩
private def endpoint_16_43_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_16_43_base : receiptBase endpoint_16_43_flag endpoint_16_43_sources = some 214143076161148887 := by decide +kernel
private theorem endpoint_16_43_window_0 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 2 214143076161148887 = some 215161264118763482 := by decide +kernel
private theorem endpoint_16_43_window_2 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 2 2 215161264118763482 = some 215161264118763482 := by decide +kernel
private theorem endpoint_16_43_prefix_4 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 4 214143076161148887 = some 215161264118763482 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 2 2 214143076161148887 215161264118763482 215161264118763482 endpoint_16_43_window_0 endpoint_16_43_window_2
private theorem endpoint_16_43_window_4 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 4 2 215161264118763482 = some 215161264118763482 := by decide +kernel
private theorem endpoint_16_43_prefix_6 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 6 214143076161148887 = some 215161264118763482 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 4 2 214143076161148887 215161264118763482 215161264118763482 endpoint_16_43_prefix_4 endpoint_16_43_window_4
private theorem endpoint_16_43_window_6 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 6 2 215161264118763482 = some 215161264118763482 := by decide +kernel
private theorem endpoint_16_43_prefix_8 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 8 214143076161148887 = some 215161264118763482 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 6 2 214143076161148887 215161264118763482 215161264118763482 endpoint_16_43_prefix_6 endpoint_16_43_window_6
private theorem endpoint_16_43_window_8 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 8 2 215161264118763482 = some 215161264118763482 := by decide +kernel
private theorem endpoint_16_43_prefix_10 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 10 214143076161148887 = some 215161264118763482 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 8 2 214143076161148887 215161264118763482 215161264118763482 endpoint_16_43_prefix_8 endpoint_16_43_window_8
private theorem endpoint_16_43_window_10 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 10 2 215161264118763482 = some 215161264118763482 := by decide +kernel
private theorem endpoint_16_43_prefix_12 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 12 214143076161148887 = some 215161264118763482 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 10 2 214143076161148887 215161264118763482 215161264118763482 endpoint_16_43_prefix_10 endpoint_16_43_window_10
private theorem endpoint_16_43_window_12 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 12 2 215161264118763482 = some 215161264118763482 := by decide +kernel
private theorem endpoint_16_43_prefix_14 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 14 214143076161148887 = some 215161264118763482 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 12 2 214143076161148887 215161264118763482 215161264118763482 endpoint_16_43_prefix_12 endpoint_16_43_window_12
private theorem endpoint_16_43_window_14 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 14 1 215161264118763482 = some 215161264118763482 := by decide +kernel
private theorem endpoint_16_43_prefix_15 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 15 214143076161148887 = some 215161264118763482 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 14 1 214143076161148887 215161264118763482 215161264118763482 endpoint_16_43_prefix_14 endpoint_16_43_window_14

def endpoint_16_43 : CertifiedEndpoint :=
  ⟨⟨16, 43, 2739⟩, 215161264118763482, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_16_43_flag endpoint_16_43_sources 15 214143076161148887 215161264118763482 rfl endpoint_16_43_base endpoint_16_43_prefix_15) (by decide)⟩
private def endpoint_16_44_flag : Flag := ⟨16, 44, 2701⟩
private def endpoint_16_44_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_16_44_base : receiptBase endpoint_16_44_flag endpoint_16_44_sources = some 215410694383646008 := by decide +kernel
private theorem endpoint_16_44_window_0 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 2 215410694383646008 = some 219800484684712424 := by decide +kernel
private theorem endpoint_16_44_window_2 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 2 2 219800484684712424 = some 219800484684712424 := by decide +kernel
private theorem endpoint_16_44_prefix_4 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 4 215410694383646008 = some 219800484684712424 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 2 2 215410694383646008 219800484684712424 219800484684712424 endpoint_16_44_window_0 endpoint_16_44_window_2
private theorem endpoint_16_44_window_4 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 4 2 219800484684712424 = some 219800484684712424 := by decide +kernel
private theorem endpoint_16_44_prefix_6 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 6 215410694383646008 = some 219800484684712424 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 4 2 215410694383646008 219800484684712424 219800484684712424 endpoint_16_44_prefix_4 endpoint_16_44_window_4
private theorem endpoint_16_44_window_6 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 6 2 219800484684712424 = some 219800484684712424 := by decide +kernel
private theorem endpoint_16_44_prefix_8 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 8 215410694383646008 = some 219800484684712424 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 6 2 215410694383646008 219800484684712424 219800484684712424 endpoint_16_44_prefix_6 endpoint_16_44_window_6
private theorem endpoint_16_44_window_8 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 8 2 219800484684712424 = some 219800484684712424 := by decide +kernel
private theorem endpoint_16_44_prefix_10 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 10 215410694383646008 = some 219800484684712424 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 8 2 215410694383646008 219800484684712424 219800484684712424 endpoint_16_44_prefix_8 endpoint_16_44_window_8
private theorem endpoint_16_44_window_10 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 10 2 219800484684712424 = some 219800484684712424 := by decide +kernel
private theorem endpoint_16_44_prefix_12 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 12 215410694383646008 = some 219800484684712424 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 10 2 215410694383646008 219800484684712424 219800484684712424 endpoint_16_44_prefix_10 endpoint_16_44_window_10
private theorem endpoint_16_44_window_12 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 12 2 219800484684712424 = some 219800484684712424 := by decide +kernel
private theorem endpoint_16_44_prefix_14 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 14 215410694383646008 = some 219800484684712424 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 12 2 215410694383646008 219800484684712424 219800484684712424 endpoint_16_44_prefix_12 endpoint_16_44_window_12
private theorem endpoint_16_44_window_14 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 14 1 219800484684712424 = some 219800484684712424 := by decide +kernel
private theorem endpoint_16_44_prefix_15 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 15 215410694383646008 = some 219800484684712424 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 14 1 215410694383646008 219800484684712424 219800484684712424 endpoint_16_44_prefix_14 endpoint_16_44_window_14

def endpoint_16_44 : CertifiedEndpoint :=
  ⟨⟨16, 44, 2701⟩, 219800484684712424, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_16_44_flag endpoint_16_44_sources 15 215410694383646008 219800484684712424 rfl endpoint_16_44_base endpoint_16_44_prefix_15) (by decide)⟩
private def endpoint_16_45_flag : Flag := ⟨16, 45, 2661⟩
private def endpoint_16_45_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_16_45_base : receiptBase endpoint_16_45_flag endpoint_16_45_sources = some 216400475509760397 := by decide +kernel
private theorem endpoint_16_45_window_0 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 2 216400475509760397 = some 224254724910946034 := by decide +kernel
private theorem endpoint_16_45_window_2 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 2 2 224254724910946034 = some 224254724910946034 := by decide +kernel
private theorem endpoint_16_45_prefix_4 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 4 216400475509760397 = some 224254724910946034 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 2 2 216400475509760397 224254724910946034 224254724910946034 endpoint_16_45_window_0 endpoint_16_45_window_2
private theorem endpoint_16_45_window_4 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 4 2 224254724910946034 = some 224254724910946034 := by decide +kernel
private theorem endpoint_16_45_prefix_6 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 6 216400475509760397 = some 224254724910946034 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 4 2 216400475509760397 224254724910946034 224254724910946034 endpoint_16_45_prefix_4 endpoint_16_45_window_4
private theorem endpoint_16_45_window_6 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 6 2 224254724910946034 = some 224254724910946034 := by decide +kernel
private theorem endpoint_16_45_prefix_8 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 8 216400475509760397 = some 224254724910946034 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 6 2 216400475509760397 224254724910946034 224254724910946034 endpoint_16_45_prefix_6 endpoint_16_45_window_6
private theorem endpoint_16_45_window_8 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 8 2 224254724910946034 = some 224254724910946034 := by decide +kernel
private theorem endpoint_16_45_prefix_10 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 10 216400475509760397 = some 224254724910946034 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 8 2 216400475509760397 224254724910946034 224254724910946034 endpoint_16_45_prefix_8 endpoint_16_45_window_8
private theorem endpoint_16_45_window_10 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 10 2 224254724910946034 = some 224254724910946034 := by decide +kernel
private theorem endpoint_16_45_prefix_12 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 12 216400475509760397 = some 224254724910946034 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 10 2 216400475509760397 224254724910946034 224254724910946034 endpoint_16_45_prefix_10 endpoint_16_45_window_10
private theorem endpoint_16_45_window_12 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 12 2 224254724910946034 = some 224254724910946034 := by decide +kernel
private theorem endpoint_16_45_prefix_14 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 14 216400475509760397 = some 224254724910946034 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 12 2 216400475509760397 224254724910946034 224254724910946034 endpoint_16_45_prefix_12 endpoint_16_45_window_12
private theorem endpoint_16_45_window_14 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 14 1 224254724910946034 = some 224254724910946034 := by decide +kernel
private theorem endpoint_16_45_prefix_15 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 15 216400475509760397 = some 224254724910946034 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 14 1 216400475509760397 224254724910946034 224254724910946034 endpoint_16_45_prefix_14 endpoint_16_45_window_14

def endpoint_16_45 : CertifiedEndpoint :=
  ⟨⟨16, 45, 2661⟩, 224254724910946034, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_16_45_flag endpoint_16_45_sources 15 216400475509760397 224254724910946034 rfl endpoint_16_45_base endpoint_16_45_prefix_15) (by decide)⟩
private def endpoint_16_46_flag : Flag := ⟨16, 46, 2621⟩
private def endpoint_16_46_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_16_46_base : receiptBase endpoint_16_46_flag endpoint_16_46_sources = some 217864517488515842 := by decide +kernel
private theorem endpoint_16_46_window_0 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 2 217864517488515842 = some 227294408038791630 := by decide +kernel
private theorem endpoint_16_46_window_2 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 2 2 227294408038791630 = some 227294408038791630 := by decide +kernel
private theorem endpoint_16_46_prefix_4 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 4 217864517488515842 = some 227294408038791630 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 2 2 217864517488515842 227294408038791630 227294408038791630 endpoint_16_46_window_0 endpoint_16_46_window_2
private theorem endpoint_16_46_window_4 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 4 2 227294408038791630 = some 227294408038791630 := by decide +kernel
private theorem endpoint_16_46_prefix_6 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 6 217864517488515842 = some 227294408038791630 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 4 2 217864517488515842 227294408038791630 227294408038791630 endpoint_16_46_prefix_4 endpoint_16_46_window_4
private theorem endpoint_16_46_window_6 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 6 2 227294408038791630 = some 227294408038791630 := by decide +kernel
private theorem endpoint_16_46_prefix_8 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 8 217864517488515842 = some 227294408038791630 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 6 2 217864517488515842 227294408038791630 227294408038791630 endpoint_16_46_prefix_6 endpoint_16_46_window_6
private theorem endpoint_16_46_window_8 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 8 2 227294408038791630 = some 227294408038791630 := by decide +kernel
private theorem endpoint_16_46_prefix_10 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 10 217864517488515842 = some 227294408038791630 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 8 2 217864517488515842 227294408038791630 227294408038791630 endpoint_16_46_prefix_8 endpoint_16_46_window_8
private theorem endpoint_16_46_window_10 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 10 2 227294408038791630 = some 227294408038791630 := by decide +kernel
private theorem endpoint_16_46_prefix_12 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 12 217864517488515842 = some 227294408038791630 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 10 2 217864517488515842 227294408038791630 227294408038791630 endpoint_16_46_prefix_10 endpoint_16_46_window_10
private theorem endpoint_16_46_window_12 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 12 2 227294408038791630 = some 227294408038791630 := by decide +kernel
private theorem endpoint_16_46_prefix_14 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 14 217864517488515842 = some 227294408038791630 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 12 2 217864517488515842 227294408038791630 227294408038791630 endpoint_16_46_prefix_12 endpoint_16_46_window_12
private theorem endpoint_16_46_window_14 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 14 1 227294408038791630 = some 227294408038791630 := by decide +kernel
private theorem endpoint_16_46_prefix_15 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 15 217864517488515842 = some 227294408038791630 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 14 1 217864517488515842 227294408038791630 227294408038791630 endpoint_16_46_prefix_14 endpoint_16_46_window_14

def endpoint_16_46 : CertifiedEndpoint :=
  ⟨⟨16, 46, 2621⟩, 227294408038791630, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_16_46_flag endpoint_16_46_sources 15 217864517488515842 227294408038791630 rfl endpoint_16_46_base endpoint_16_46_prefix_15) (by decide)⟩
private def endpoint_16_47_flag : Flag := ⟨16, 47, 2580⟩
private def endpoint_16_47_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_16_47_base : receiptBase endpoint_16_47_flag endpoint_16_47_sources = some 218552591107238913 := by decide +kernel
private theorem endpoint_16_47_window_0 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 2 218552591107238913 = some 231462982806134949 := by decide +kernel
private theorem endpoint_16_47_window_2 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 2 2 231462982806134949 = some 231462982806134949 := by decide +kernel
private theorem endpoint_16_47_prefix_4 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 4 218552591107238913 = some 231462982806134949 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 2 2 218552591107238913 231462982806134949 231462982806134949 endpoint_16_47_window_0 endpoint_16_47_window_2
private theorem endpoint_16_47_window_4 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 4 2 231462982806134949 = some 231462982806134949 := by decide +kernel
private theorem endpoint_16_47_prefix_6 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 6 218552591107238913 = some 231462982806134949 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 4 2 218552591107238913 231462982806134949 231462982806134949 endpoint_16_47_prefix_4 endpoint_16_47_window_4
private theorem endpoint_16_47_window_6 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 6 2 231462982806134949 = some 231462982806134949 := by decide +kernel
private theorem endpoint_16_47_prefix_8 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 8 218552591107238913 = some 231462982806134949 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 6 2 218552591107238913 231462982806134949 231462982806134949 endpoint_16_47_prefix_6 endpoint_16_47_window_6
private theorem endpoint_16_47_window_8 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 8 2 231462982806134949 = some 231462982806134949 := by decide +kernel
private theorem endpoint_16_47_prefix_10 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 10 218552591107238913 = some 231462982806134949 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 8 2 218552591107238913 231462982806134949 231462982806134949 endpoint_16_47_prefix_8 endpoint_16_47_window_8
private theorem endpoint_16_47_window_10 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 10 2 231462982806134949 = some 231462982806134949 := by decide +kernel
private theorem endpoint_16_47_prefix_12 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 12 218552591107238913 = some 231462982806134949 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 10 2 218552591107238913 231462982806134949 231462982806134949 endpoint_16_47_prefix_10 endpoint_16_47_window_10
private theorem endpoint_16_47_window_12 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 12 2 231462982806134949 = some 231462982806134949 := by decide +kernel
private theorem endpoint_16_47_prefix_14 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 14 218552591107238913 = some 231462982806134949 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 12 2 218552591107238913 231462982806134949 231462982806134949 endpoint_16_47_prefix_12 endpoint_16_47_window_12
private theorem endpoint_16_47_window_14 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 14 1 231462982806134949 = some 231462982806134949 := by decide +kernel
private theorem endpoint_16_47_prefix_15 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 15 218552591107238913 = some 231462982806134949 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 14 1 218552591107238913 231462982806134949 231462982806134949 endpoint_16_47_prefix_14 endpoint_16_47_window_14

def endpoint_16_47 : CertifiedEndpoint :=
  ⟨⟨16, 47, 2580⟩, 231462982806134949, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_16_47_flag endpoint_16_47_sources 15 218552591107238913 231462982806134949 rfl endpoint_16_47_base endpoint_16_47_prefix_15) (by decide)⟩
private def endpoint_16_48_flag : Flag := ⟨16, 48, 2537⟩
private def endpoint_16_48_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_48_base : receiptBase endpoint_16_48_flag endpoint_16_48_sources = some 219505392926942200 := by decide +kernel
private theorem endpoint_16_48_window_0 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 2 219505392926942200 = some 227528899158076516 := by decide +kernel
private theorem endpoint_16_48_window_2 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 2 2 227528899158076516 = some 227528899158076516 := by decide +kernel
private theorem endpoint_16_48_prefix_4 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 4 219505392926942200 = some 227528899158076516 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 2 2 219505392926942200 227528899158076516 227528899158076516 endpoint_16_48_window_0 endpoint_16_48_window_2
private theorem endpoint_16_48_window_4 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 4 2 227528899158076516 = some 227528899158076516 := by decide +kernel
private theorem endpoint_16_48_prefix_6 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 6 219505392926942200 = some 227528899158076516 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 4 2 219505392926942200 227528899158076516 227528899158076516 endpoint_16_48_prefix_4 endpoint_16_48_window_4
private theorem endpoint_16_48_window_6 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 6 2 227528899158076516 = some 227528899158076516 := by decide +kernel
private theorem endpoint_16_48_prefix_8 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 8 219505392926942200 = some 227528899158076516 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 6 2 219505392926942200 227528899158076516 227528899158076516 endpoint_16_48_prefix_6 endpoint_16_48_window_6
private theorem endpoint_16_48_window_8 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 8 2 227528899158076516 = some 227528899158076516 := by decide +kernel
private theorem endpoint_16_48_prefix_10 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 10 219505392926942200 = some 227528899158076516 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 8 2 219505392926942200 227528899158076516 227528899158076516 endpoint_16_48_prefix_8 endpoint_16_48_window_8
private theorem endpoint_16_48_window_10 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 10 2 227528899158076516 = some 227528899158076516 := by decide +kernel
private theorem endpoint_16_48_prefix_12 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 12 219505392926942200 = some 227528899158076516 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 10 2 219505392926942200 227528899158076516 227528899158076516 endpoint_16_48_prefix_10 endpoint_16_48_window_10
private theorem endpoint_16_48_window_12 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 12 2 227528899158076516 = some 227528899158076516 := by decide +kernel
private theorem endpoint_16_48_prefix_14 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 14 219505392926942200 = some 227528899158076516 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 12 2 219505392926942200 227528899158076516 227528899158076516 endpoint_16_48_prefix_12 endpoint_16_48_window_12
private theorem endpoint_16_48_window_14 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 14 1 227528899158076516 = some 227528899158076516 := by decide +kernel
private theorem endpoint_16_48_prefix_15 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 15 219505392926942200 = some 227528899158076516 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 14 1 219505392926942200 227528899158076516 227528899158076516 endpoint_16_48_prefix_14 endpoint_16_48_window_14

def endpoint_16_48 : CertifiedEndpoint :=
  ⟨⟨16, 48, 2537⟩, 227528899158076516, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_48_flag endpoint_16_48_sources 15 219505392926942200 227528899158076516 rfl endpoint_16_48_base endpoint_16_48_prefix_15) (by decide)⟩
private def endpoint_16_49_flag : Flag := ⟨16, 49, 2494⟩
private def endpoint_16_49_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_49_base : receiptBase endpoint_16_49_flag endpoint_16_49_sources = some 219748318741014141 := by decide +kernel
private theorem endpoint_16_49_window_0 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 2 219748318741014141 = some 231187012859784343 := by decide +kernel
private theorem endpoint_16_49_window_2 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 2 2 231187012859784343 = some 231187012859784343 := by decide +kernel
private theorem endpoint_16_49_prefix_4 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 4 219748318741014141 = some 231187012859784343 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 2 2 219748318741014141 231187012859784343 231187012859784343 endpoint_16_49_window_0 endpoint_16_49_window_2
private theorem endpoint_16_49_window_4 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 4 2 231187012859784343 = some 231187012859784343 := by decide +kernel
private theorem endpoint_16_49_prefix_6 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 6 219748318741014141 = some 231187012859784343 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 4 2 219748318741014141 231187012859784343 231187012859784343 endpoint_16_49_prefix_4 endpoint_16_49_window_4
private theorem endpoint_16_49_window_6 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 6 2 231187012859784343 = some 231187012859784343 := by decide +kernel
private theorem endpoint_16_49_prefix_8 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 8 219748318741014141 = some 231187012859784343 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 6 2 219748318741014141 231187012859784343 231187012859784343 endpoint_16_49_prefix_6 endpoint_16_49_window_6
private theorem endpoint_16_49_window_8 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 8 2 231187012859784343 = some 231187012859784343 := by decide +kernel
private theorem endpoint_16_49_prefix_10 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 10 219748318741014141 = some 231187012859784343 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 8 2 219748318741014141 231187012859784343 231187012859784343 endpoint_16_49_prefix_8 endpoint_16_49_window_8
private theorem endpoint_16_49_window_10 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 10 2 231187012859784343 = some 231187012859784343 := by decide +kernel
private theorem endpoint_16_49_prefix_12 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 12 219748318741014141 = some 231187012859784343 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 10 2 219748318741014141 231187012859784343 231187012859784343 endpoint_16_49_prefix_10 endpoint_16_49_window_10
private theorem endpoint_16_49_window_12 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 12 2 231187012859784343 = some 231187012859784343 := by decide +kernel
private theorem endpoint_16_49_prefix_14 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 14 219748318741014141 = some 231187012859784343 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 12 2 219748318741014141 231187012859784343 231187012859784343 endpoint_16_49_prefix_12 endpoint_16_49_window_12
private theorem endpoint_16_49_window_14 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 14 1 231187012859784343 = some 231187012859784343 := by decide +kernel
private theorem endpoint_16_49_prefix_15 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 15 219748318741014141 = some 231187012859784343 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 14 1 219748318741014141 231187012859784343 231187012859784343 endpoint_16_49_prefix_14 endpoint_16_49_window_14

def endpoint_16_49 : CertifiedEndpoint :=
  ⟨⟨16, 49, 2494⟩, 231187012859784343, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_49_flag endpoint_16_49_sources 15 219748318741014141 231187012859784343 rfl endpoint_16_49_base endpoint_16_49_prefix_15) (by decide)⟩
private def endpoint_16_50_flag : Flag := ⟨16, 50, 2450⟩
private def endpoint_16_50_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_50_base : receiptBase endpoint_16_50_flag endpoint_16_50_sources = some 219768431118742075 := by decide +kernel
private theorem endpoint_16_50_window_0 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 2 219768431118742075 = some 234685658989039444 := by decide +kernel
private theorem endpoint_16_50_window_2 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 2 2 234685658989039444 = some 234685658989039444 := by decide +kernel
private theorem endpoint_16_50_prefix_4 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 4 219768431118742075 = some 234685658989039444 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 2 2 219768431118742075 234685658989039444 234685658989039444 endpoint_16_50_window_0 endpoint_16_50_window_2
private theorem endpoint_16_50_window_4 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 4 2 234685658989039444 = some 234685658989039444 := by decide +kernel
private theorem endpoint_16_50_prefix_6 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 6 219768431118742075 = some 234685658989039444 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 4 2 219768431118742075 234685658989039444 234685658989039444 endpoint_16_50_prefix_4 endpoint_16_50_window_4
private theorem endpoint_16_50_window_6 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 6 2 234685658989039444 = some 234685658989039444 := by decide +kernel
private theorem endpoint_16_50_prefix_8 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 8 219768431118742075 = some 234685658989039444 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 6 2 219768431118742075 234685658989039444 234685658989039444 endpoint_16_50_prefix_6 endpoint_16_50_window_6
private theorem endpoint_16_50_window_8 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 8 2 234685658989039444 = some 234685658989039444 := by decide +kernel
private theorem endpoint_16_50_prefix_10 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 10 219768431118742075 = some 234685658989039444 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 8 2 219768431118742075 234685658989039444 234685658989039444 endpoint_16_50_prefix_8 endpoint_16_50_window_8
private theorem endpoint_16_50_window_10 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 10 2 234685658989039444 = some 234685658989039444 := by decide +kernel
private theorem endpoint_16_50_prefix_12 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 12 219768431118742075 = some 234685658989039444 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 10 2 219768431118742075 234685658989039444 234685658989039444 endpoint_16_50_prefix_10 endpoint_16_50_window_10
private theorem endpoint_16_50_window_12 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 12 2 234685658989039444 = some 234685658989039444 := by decide +kernel
private theorem endpoint_16_50_prefix_14 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 14 219768431118742075 = some 234685658989039444 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 12 2 219768431118742075 234685658989039444 234685658989039444 endpoint_16_50_prefix_12 endpoint_16_50_window_12
private theorem endpoint_16_50_window_14 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 14 1 234685658989039444 = some 234685658989039444 := by decide +kernel
private theorem endpoint_16_50_prefix_15 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 15 219768431118742075 = some 234685658989039444 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 14 1 219768431118742075 234685658989039444 234685658989039444 endpoint_16_50_prefix_14 endpoint_16_50_window_14

def endpoint_16_50 : CertifiedEndpoint :=
  ⟨⟨16, 50, 2450⟩, 234685658989039444, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_50_flag endpoint_16_50_sources 15 219768431118742075 234685658989039444 rfl endpoint_16_50_base endpoint_16_50_prefix_15) (by decide)⟩
private def endpoint_16_51_flag : Flag := ⟨16, 51, 2405⟩
private def endpoint_16_51_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_51_base : receiptBase endpoint_16_51_flag endpoint_16_51_sources = some 219561093430422022 := by decide +kernel
private theorem endpoint_16_51_window_0 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 2 219561093430422022 = some 238021152371298934 := by decide +kernel
private theorem endpoint_16_51_window_2 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 2 2 238021152371298934 = some 238021152371298934 := by decide +kernel
private theorem endpoint_16_51_prefix_4 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 4 219561093430422022 = some 238021152371298934 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 2 2 219561093430422022 238021152371298934 238021152371298934 endpoint_16_51_window_0 endpoint_16_51_window_2
private theorem endpoint_16_51_window_4 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 4 2 238021152371298934 = some 238021152371298934 := by decide +kernel
private theorem endpoint_16_51_prefix_6 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 6 219561093430422022 = some 238021152371298934 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 4 2 219561093430422022 238021152371298934 238021152371298934 endpoint_16_51_prefix_4 endpoint_16_51_window_4
private theorem endpoint_16_51_window_6 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 6 2 238021152371298934 = some 238021152371298934 := by decide +kernel
private theorem endpoint_16_51_prefix_8 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 8 219561093430422022 = some 238021152371298934 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 6 2 219561093430422022 238021152371298934 238021152371298934 endpoint_16_51_prefix_6 endpoint_16_51_window_6
private theorem endpoint_16_51_window_8 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 8 2 238021152371298934 = some 238021152371298934 := by decide +kernel
private theorem endpoint_16_51_prefix_10 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 10 219561093430422022 = some 238021152371298934 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 8 2 219561093430422022 238021152371298934 238021152371298934 endpoint_16_51_prefix_8 endpoint_16_51_window_8
private theorem endpoint_16_51_window_10 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 10 2 238021152371298934 = some 238021152371298934 := by decide +kernel
private theorem endpoint_16_51_prefix_12 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 12 219561093430422022 = some 238021152371298934 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 10 2 219561093430422022 238021152371298934 238021152371298934 endpoint_16_51_prefix_10 endpoint_16_51_window_10
private theorem endpoint_16_51_window_12 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 12 2 238021152371298934 = some 238021152371298934 := by decide +kernel
private theorem endpoint_16_51_prefix_14 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 14 219561093430422022 = some 238021152371298934 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 12 2 219561093430422022 238021152371298934 238021152371298934 endpoint_16_51_prefix_12 endpoint_16_51_window_12
private theorem endpoint_16_51_window_14 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 14 1 238021152371298934 = some 238021152371298934 := by decide +kernel
private theorem endpoint_16_51_prefix_15 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 15 219561093430422022 = some 238021152371298934 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 14 1 219561093430422022 238021152371298934 238021152371298934 endpoint_16_51_prefix_14 endpoint_16_51_window_14

def endpoint_16_51 : CertifiedEndpoint :=
  ⟨⟨16, 51, 2405⟩, 238021152371298934, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_51_flag endpoint_16_51_sources 15 219561093430422022 238021152371298934 rfl endpoint_16_51_base endpoint_16_51_prefix_15) (by decide)⟩
private def endpoint_16_52_flag : Flag := ⟨16, 52, 2358⟩
private def endpoint_16_52_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_52_base : receiptBase endpoint_16_52_flag endpoint_16_52_sources = some 219030226784952129 := by decide +kernel
private theorem endpoint_16_52_window_0 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 2 219030226784952129 = some 241137270451442832 := by decide +kernel
private theorem endpoint_16_52_window_2 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 2 2 241137270451442832 = some 241137270451442832 := by decide +kernel
private theorem endpoint_16_52_prefix_4 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 4 219030226784952129 = some 241137270451442832 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 2 2 219030226784952129 241137270451442832 241137270451442832 endpoint_16_52_window_0 endpoint_16_52_window_2
private theorem endpoint_16_52_window_4 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 4 2 241137270451442832 = some 241137270451442832 := by decide +kernel
private theorem endpoint_16_52_prefix_6 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 6 219030226784952129 = some 241137270451442832 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 4 2 219030226784952129 241137270451442832 241137270451442832 endpoint_16_52_prefix_4 endpoint_16_52_window_4
private theorem endpoint_16_52_window_6 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 6 2 241137270451442832 = some 241137270451442832 := by decide +kernel
private theorem endpoint_16_52_prefix_8 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 8 219030226784952129 = some 241137270451442832 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 6 2 219030226784952129 241137270451442832 241137270451442832 endpoint_16_52_prefix_6 endpoint_16_52_window_6
private theorem endpoint_16_52_window_8 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 8 2 241137270451442832 = some 241137270451442832 := by decide +kernel
private theorem endpoint_16_52_prefix_10 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 10 219030226784952129 = some 241137270451442832 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 8 2 219030226784952129 241137270451442832 241137270451442832 endpoint_16_52_prefix_8 endpoint_16_52_window_8
private theorem endpoint_16_52_window_10 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 10 2 241137270451442832 = some 241137270451442832 := by decide +kernel
private theorem endpoint_16_52_prefix_12 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 12 219030226784952129 = some 241137270451442832 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 10 2 219030226784952129 241137270451442832 241137270451442832 endpoint_16_52_prefix_10 endpoint_16_52_window_10
private theorem endpoint_16_52_window_12 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 12 2 241137270451442832 = some 241137270451442832 := by decide +kernel
private theorem endpoint_16_52_prefix_14 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 14 219030226784952129 = some 241137270451442832 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 12 2 219030226784952129 241137270451442832 241137270451442832 endpoint_16_52_prefix_12 endpoint_16_52_window_12
private theorem endpoint_16_52_window_14 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 14 1 241137270451442832 = some 241137270451442832 := by decide +kernel
private theorem endpoint_16_52_prefix_15 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 15 219030226784952129 = some 241137270451442832 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 14 1 219030226784952129 241137270451442832 241137270451442832 endpoint_16_52_prefix_14 endpoint_16_52_window_14

def endpoint_16_52 : CertifiedEndpoint :=
  ⟨⟨16, 52, 2358⟩, 241137270451442832, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_52_flag endpoint_16_52_sources 15 219030226784952129 241137270451442832 rfl endpoint_16_52_base endpoint_16_52_prefix_15) (by decide)⟩
private def endpoint_16_53_flag : Flag := ⟨16, 53, 2311⟩
private def endpoint_16_53_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_53_base : receiptBase endpoint_16_53_flag endpoint_16_53_sources = some 218352533532189495 := by decide +kernel
private theorem endpoint_16_53_window_0 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 2 218352533532189495 = some 244134174424568150 := by decide +kernel
private theorem endpoint_16_53_window_2 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 2 2 244134174424568150 = some 244134174424568150 := by decide +kernel
private theorem endpoint_16_53_prefix_4 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 4 218352533532189495 = some 244134174424568150 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 2 2 218352533532189495 244134174424568150 244134174424568150 endpoint_16_53_window_0 endpoint_16_53_window_2
private theorem endpoint_16_53_window_4 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 4 2 244134174424568150 = some 244134174424568150 := by decide +kernel
private theorem endpoint_16_53_prefix_6 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 6 218352533532189495 = some 244134174424568150 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 4 2 218352533532189495 244134174424568150 244134174424568150 endpoint_16_53_prefix_4 endpoint_16_53_window_4
private theorem endpoint_16_53_window_6 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 6 2 244134174424568150 = some 244134174424568150 := by decide +kernel
private theorem endpoint_16_53_prefix_8 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 8 218352533532189495 = some 244134174424568150 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 6 2 218352533532189495 244134174424568150 244134174424568150 endpoint_16_53_prefix_6 endpoint_16_53_window_6
private theorem endpoint_16_53_window_8 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 8 2 244134174424568150 = some 244134174424568150 := by decide +kernel
private theorem endpoint_16_53_prefix_10 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 10 218352533532189495 = some 244134174424568150 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 8 2 218352533532189495 244134174424568150 244134174424568150 endpoint_16_53_prefix_8 endpoint_16_53_window_8
private theorem endpoint_16_53_window_10 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 10 2 244134174424568150 = some 244134174424568150 := by decide +kernel
private theorem endpoint_16_53_prefix_12 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 12 218352533532189495 = some 244134174424568150 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 10 2 218352533532189495 244134174424568150 244134174424568150 endpoint_16_53_prefix_10 endpoint_16_53_window_10
private theorem endpoint_16_53_window_12 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 12 2 244134174424568150 = some 244134174424568150 := by decide +kernel
private theorem endpoint_16_53_prefix_14 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 14 218352533532189495 = some 244134174424568150 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 12 2 218352533532189495 244134174424568150 244134174424568150 endpoint_16_53_prefix_12 endpoint_16_53_window_12
private theorem endpoint_16_53_window_14 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 14 1 244134174424568150 = some 244134174424568150 := by decide +kernel
private theorem endpoint_16_53_prefix_15 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 15 218352533532189495 = some 244134174424568150 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 14 1 218352533532189495 244134174424568150 244134174424568150 endpoint_16_53_prefix_14 endpoint_16_53_window_14

def endpoint_16_53 : CertifiedEndpoint :=
  ⟨⟨16, 53, 2311⟩, 244134174424568150, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_53_flag endpoint_16_53_sources 15 218352533532189495 244134174424568150 rfl endpoint_16_53_base endpoint_16_53_prefix_15) (by decide)⟩
private def endpoint_16_54_flag : Flag := ⟨16, 54, 2262⟩
private def endpoint_16_54_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_54_base : receiptBase endpoint_16_54_flag endpoint_16_54_sources = some 217338946976399739 := by decide +kernel
private theorem endpoint_16_54_window_0 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 2 217338946976399739 = some 246901875963463516 := by decide +kernel
private theorem endpoint_16_54_window_2 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 2 2 246901875963463516 = some 246901875963463516 := by decide +kernel
private theorem endpoint_16_54_prefix_4 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 4 217338946976399739 = some 246901875963463516 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 2 2 217338946976399739 246901875963463516 246901875963463516 endpoint_16_54_window_0 endpoint_16_54_window_2
private theorem endpoint_16_54_window_4 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 4 2 246901875963463516 = some 246901875963463516 := by decide +kernel
private theorem endpoint_16_54_prefix_6 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 6 217338946976399739 = some 246901875963463516 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 4 2 217338946976399739 246901875963463516 246901875963463516 endpoint_16_54_prefix_4 endpoint_16_54_window_4
private theorem endpoint_16_54_window_6 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 6 2 246901875963463516 = some 246901875963463516 := by decide +kernel
private theorem endpoint_16_54_prefix_8 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 8 217338946976399739 = some 246901875963463516 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 6 2 217338946976399739 246901875963463516 246901875963463516 endpoint_16_54_prefix_6 endpoint_16_54_window_6
private theorem endpoint_16_54_window_8 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 8 2 246901875963463516 = some 246901875963463516 := by decide +kernel
private theorem endpoint_16_54_prefix_10 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 10 217338946976399739 = some 246901875963463516 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 8 2 217338946976399739 246901875963463516 246901875963463516 endpoint_16_54_prefix_8 endpoint_16_54_window_8
private theorem endpoint_16_54_window_10 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 10 2 246901875963463516 = some 246901875963463516 := by decide +kernel
private theorem endpoint_16_54_prefix_12 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 12 217338946976399739 = some 246901875963463516 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 10 2 217338946976399739 246901875963463516 246901875963463516 endpoint_16_54_prefix_10 endpoint_16_54_window_10
private theorem endpoint_16_54_window_12 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 12 2 246901875963463516 = some 246901875963463516 := by decide +kernel
private theorem endpoint_16_54_prefix_14 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 14 217338946976399739 = some 246901875963463516 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 12 2 217338946976399739 246901875963463516 246901875963463516 endpoint_16_54_prefix_12 endpoint_16_54_window_12
private theorem endpoint_16_54_window_14 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 14 1 246901875963463516 = some 246901875963463516 := by decide +kernel
private theorem endpoint_16_54_prefix_15 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 15 217338946976399739 = some 246901875963463516 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 14 1 217338946976399739 246901875963463516 246901875963463516 endpoint_16_54_prefix_14 endpoint_16_54_window_14

def endpoint_16_54 : CertifiedEndpoint :=
  ⟨⟨16, 54, 2262⟩, 246901875963463516, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_54_flag endpoint_16_54_sources 15 217338946976399739 246901875963463516 rfl endpoint_16_54_base endpoint_16_54_prefix_15) (by decide)⟩
private def endpoint_16_55_flag : Flag := ⟨16, 55, 2212⟩
private def endpoint_16_55_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_16_55_base : receiptBase endpoint_16_55_flag endpoint_16_55_sources = some 221672611222073737 := by decide +kernel
private theorem endpoint_16_55_window_0 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 2 221672611222073737 = some 241108059401480029 := by decide +kernel
private theorem endpoint_16_55_window_2 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 2 2 241108059401480029 = some 241108059401480029 := by decide +kernel
private theorem endpoint_16_55_prefix_4 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 4 221672611222073737 = some 241108059401480029 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 2 2 221672611222073737 241108059401480029 241108059401480029 endpoint_16_55_window_0 endpoint_16_55_window_2
private theorem endpoint_16_55_window_4 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 4 2 241108059401480029 = some 241108059401480029 := by decide +kernel
private theorem endpoint_16_55_prefix_6 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 6 221672611222073737 = some 241108059401480029 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 4 2 221672611222073737 241108059401480029 241108059401480029 endpoint_16_55_prefix_4 endpoint_16_55_window_4
private theorem endpoint_16_55_window_6 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 6 2 241108059401480029 = some 241108059401480029 := by decide +kernel
private theorem endpoint_16_55_prefix_8 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 8 221672611222073737 = some 241108059401480029 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 6 2 221672611222073737 241108059401480029 241108059401480029 endpoint_16_55_prefix_6 endpoint_16_55_window_6
private theorem endpoint_16_55_window_8 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 8 2 241108059401480029 = some 241108059401480029 := by decide +kernel
private theorem endpoint_16_55_prefix_10 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 10 221672611222073737 = some 241108059401480029 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 8 2 221672611222073737 241108059401480029 241108059401480029 endpoint_16_55_prefix_8 endpoint_16_55_window_8
private theorem endpoint_16_55_window_10 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 10 2 241108059401480029 = some 241108059401480029 := by decide +kernel
private theorem endpoint_16_55_prefix_12 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 12 221672611222073737 = some 241108059401480029 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 10 2 221672611222073737 241108059401480029 241108059401480029 endpoint_16_55_prefix_10 endpoint_16_55_window_10
private theorem endpoint_16_55_window_12 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 12 2 241108059401480029 = some 241108059401480029 := by decide +kernel
private theorem endpoint_16_55_prefix_14 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 14 221672611222073737 = some 241108059401480029 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 12 2 221672611222073737 241108059401480029 241108059401480029 endpoint_16_55_prefix_12 endpoint_16_55_window_12
private theorem endpoint_16_55_window_14 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 14 1 241108059401480029 = some 241108059401480029 := by decide +kernel
private theorem endpoint_16_55_prefix_15 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 15 221672611222073737 = some 241108059401480029 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 14 1 221672611222073737 241108059401480029 241108059401480029 endpoint_16_55_prefix_14 endpoint_16_55_window_14

def endpoint_16_55 : CertifiedEndpoint :=
  ⟨⟨16, 55, 2212⟩, 241108059401480029, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_16_55_flag endpoint_16_55_sources 15 221672611222073737 241108059401480029 rfl endpoint_16_55_base endpoint_16_55_prefix_15) (by decide)⟩
private def endpoint_16_56_flag : Flag := ⟨16, 56, 2161⟩
private def endpoint_16_56_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_16_56_base : receiptBase endpoint_16_56_flag endpoint_16_56_sources = some 220189639679085764 := by decide +kernel
private theorem endpoint_16_56_window_0 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 2 220189639679085764 = some 243330157561881068 := by decide +kernel
private theorem endpoint_16_56_window_2 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 2 2 243330157561881068 = some 243330157561881068 := by decide +kernel
private theorem endpoint_16_56_prefix_4 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 4 220189639679085764 = some 243330157561881068 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 2 2 220189639679085764 243330157561881068 243330157561881068 endpoint_16_56_window_0 endpoint_16_56_window_2
private theorem endpoint_16_56_window_4 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 4 2 243330157561881068 = some 243330157561881068 := by decide +kernel
private theorem endpoint_16_56_prefix_6 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 6 220189639679085764 = some 243330157561881068 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 4 2 220189639679085764 243330157561881068 243330157561881068 endpoint_16_56_prefix_4 endpoint_16_56_window_4
private theorem endpoint_16_56_window_6 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 6 2 243330157561881068 = some 243330157561881068 := by decide +kernel
private theorem endpoint_16_56_prefix_8 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 8 220189639679085764 = some 243330157561881068 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 6 2 220189639679085764 243330157561881068 243330157561881068 endpoint_16_56_prefix_6 endpoint_16_56_window_6
private theorem endpoint_16_56_window_8 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 8 2 243330157561881068 = some 243330157561881068 := by decide +kernel
private theorem endpoint_16_56_prefix_10 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 10 220189639679085764 = some 243330157561881068 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 8 2 220189639679085764 243330157561881068 243330157561881068 endpoint_16_56_prefix_8 endpoint_16_56_window_8
private theorem endpoint_16_56_window_10 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 10 2 243330157561881068 = some 243330157561881068 := by decide +kernel
private theorem endpoint_16_56_prefix_12 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 12 220189639679085764 = some 243330157561881068 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 10 2 220189639679085764 243330157561881068 243330157561881068 endpoint_16_56_prefix_10 endpoint_16_56_window_10
private theorem endpoint_16_56_window_12 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 12 2 243330157561881068 = some 243330157561881068 := by decide +kernel
private theorem endpoint_16_56_prefix_14 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 14 220189639679085764 = some 243330157561881068 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 12 2 220189639679085764 243330157561881068 243330157561881068 endpoint_16_56_prefix_12 endpoint_16_56_window_12
private theorem endpoint_16_56_window_14 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 14 1 243330157561881068 = some 243330157561881068 := by decide +kernel
private theorem endpoint_16_56_prefix_15 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 15 220189639679085764 = some 243330157561881068 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 14 1 220189639679085764 243330157561881068 243330157561881068 endpoint_16_56_prefix_14 endpoint_16_56_window_14

def endpoint_16_56 : CertifiedEndpoint :=
  ⟨⟨16, 56, 2161⟩, 243330157561881068, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_16_56_flag endpoint_16_56_sources 15 220189639679085764 243330157561881068 rfl endpoint_16_56_base endpoint_16_56_prefix_15) (by decide)⟩
private def endpoint_16_57_flag : Flag := ⟨16, 57, 2108⟩
private def endpoint_16_57_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_57_base : receiptBase endpoint_16_57_flag endpoint_16_57_sources = some 219264794967891842 := by decide +kernel
private theorem endpoint_16_57_window_0 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 2 219264794967891842 = some 228061526942573823 := by decide +kernel
private theorem endpoint_16_57_window_2 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 2 2 228061526942573823 = some 228061526942573823 := by decide +kernel
private theorem endpoint_16_57_prefix_4 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 4 219264794967891842 = some 228061526942573823 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 2 2 219264794967891842 228061526942573823 228061526942573823 endpoint_16_57_window_0 endpoint_16_57_window_2
private theorem endpoint_16_57_window_4 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 4 2 228061526942573823 = some 228061526942573823 := by decide +kernel
private theorem endpoint_16_57_prefix_6 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 6 219264794967891842 = some 228061526942573823 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 4 2 219264794967891842 228061526942573823 228061526942573823 endpoint_16_57_prefix_4 endpoint_16_57_window_4
private theorem endpoint_16_57_window_6 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 6 2 228061526942573823 = some 228061526942573823 := by decide +kernel
private theorem endpoint_16_57_prefix_8 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 8 219264794967891842 = some 228061526942573823 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 6 2 219264794967891842 228061526942573823 228061526942573823 endpoint_16_57_prefix_6 endpoint_16_57_window_6
private theorem endpoint_16_57_window_8 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 8 2 228061526942573823 = some 228061526942573823 := by decide +kernel
private theorem endpoint_16_57_prefix_10 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 10 219264794967891842 = some 228061526942573823 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 8 2 219264794967891842 228061526942573823 228061526942573823 endpoint_16_57_prefix_8 endpoint_16_57_window_8
private theorem endpoint_16_57_window_10 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 10 2 228061526942573823 = some 228061526942573823 := by decide +kernel
private theorem endpoint_16_57_prefix_12 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 12 219264794967891842 = some 228061526942573823 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 10 2 219264794967891842 228061526942573823 228061526942573823 endpoint_16_57_prefix_10 endpoint_16_57_window_10
private theorem endpoint_16_57_window_12 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 12 2 228061526942573823 = some 228061526942573823 := by decide +kernel
private theorem endpoint_16_57_prefix_14 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 14 219264794967891842 = some 228061526942573823 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 12 2 219264794967891842 228061526942573823 228061526942573823 endpoint_16_57_prefix_12 endpoint_16_57_window_12
private theorem endpoint_16_57_window_14 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 14 1 228061526942573823 = some 228061526942573823 := by decide +kernel
private theorem endpoint_16_57_prefix_15 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 15 219264794967891842 = some 228061526942573823 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 14 1 219264794967891842 228061526942573823 228061526942573823 endpoint_16_57_prefix_14 endpoint_16_57_window_14

def endpoint_16_57 : CertifiedEndpoint :=
  ⟨⟨16, 57, 2108⟩, 228061526942573823, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_57_flag endpoint_16_57_sources 15 219264794967891842 228061526942573823 rfl endpoint_16_57_base endpoint_16_57_prefix_15) (by decide)⟩
private def endpoint_16_58_flag : Flag := ⟨16, 58, 2054⟩
private def endpoint_16_58_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_58_base : receiptBase endpoint_16_58_flag endpoint_16_58_sources = some 217085045152999652 := by decide +kernel
private theorem endpoint_16_58_window_0 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 2 217085045152999652 = some 229485960983892984 := by decide +kernel
private theorem endpoint_16_58_window_2 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 2 2 229485960983892984 = some 229485960983892984 := by decide +kernel
private theorem endpoint_16_58_prefix_4 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 4 217085045152999652 = some 229485960983892984 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 2 2 217085045152999652 229485960983892984 229485960983892984 endpoint_16_58_window_0 endpoint_16_58_window_2
private theorem endpoint_16_58_window_4 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 4 2 229485960983892984 = some 229485960983892984 := by decide +kernel
private theorem endpoint_16_58_prefix_6 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 6 217085045152999652 = some 229485960983892984 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 4 2 217085045152999652 229485960983892984 229485960983892984 endpoint_16_58_prefix_4 endpoint_16_58_window_4
private theorem endpoint_16_58_window_6 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 6 2 229485960983892984 = some 229485960983892984 := by decide +kernel
private theorem endpoint_16_58_prefix_8 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 8 217085045152999652 = some 229485960983892984 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 6 2 217085045152999652 229485960983892984 229485960983892984 endpoint_16_58_prefix_6 endpoint_16_58_window_6
private theorem endpoint_16_58_window_8 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 8 2 229485960983892984 = some 229485960983892984 := by decide +kernel
private theorem endpoint_16_58_prefix_10 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 10 217085045152999652 = some 229485960983892984 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 8 2 217085045152999652 229485960983892984 229485960983892984 endpoint_16_58_prefix_8 endpoint_16_58_window_8
private theorem endpoint_16_58_window_10 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 10 2 229485960983892984 = some 229485960983892984 := by decide +kernel
private theorem endpoint_16_58_prefix_12 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 12 217085045152999652 = some 229485960983892984 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 10 2 217085045152999652 229485960983892984 229485960983892984 endpoint_16_58_prefix_10 endpoint_16_58_window_10
private theorem endpoint_16_58_window_12 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 12 2 229485960983892984 = some 229485960983892984 := by decide +kernel
private theorem endpoint_16_58_prefix_14 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 14 217085045152999652 = some 229485960983892984 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 12 2 217085045152999652 229485960983892984 229485960983892984 endpoint_16_58_prefix_12 endpoint_16_58_window_12
private theorem endpoint_16_58_window_14 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 14 1 229485960983892984 = some 229485960983892984 := by decide +kernel
private theorem endpoint_16_58_prefix_15 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 15 217085045152999652 = some 229485960983892984 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 14 1 217085045152999652 229485960983892984 229485960983892984 endpoint_16_58_prefix_14 endpoint_16_58_window_14

def endpoint_16_58 : CertifiedEndpoint :=
  ⟨⟨16, 58, 2054⟩, 229485960983892984, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_58_flag endpoint_16_58_sources 15 217085045152999652 229485960983892984 rfl endpoint_16_58_base endpoint_16_58_prefix_15) (by decide)⟩
private def endpoint_16_59_flag : Flag := ⟨16, 59, 1999⟩
private def endpoint_16_59_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_59_base : receiptBase endpoint_16_59_flag endpoint_16_59_sources = some 214630366240582966 := by decide +kernel
private theorem endpoint_16_59_window_0 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 2 214630366240582966 = some 230712847315816274 := by decide +kernel
private theorem endpoint_16_59_window_2 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 2 2 230712847315816274 = some 230712847315816274 := by decide +kernel
private theorem endpoint_16_59_prefix_4 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 4 214630366240582966 = some 230712847315816274 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 2 2 214630366240582966 230712847315816274 230712847315816274 endpoint_16_59_window_0 endpoint_16_59_window_2
private theorem endpoint_16_59_window_4 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 4 2 230712847315816274 = some 230712847315816274 := by decide +kernel
private theorem endpoint_16_59_prefix_6 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 6 214630366240582966 = some 230712847315816274 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 4 2 214630366240582966 230712847315816274 230712847315816274 endpoint_16_59_prefix_4 endpoint_16_59_window_4
private theorem endpoint_16_59_window_6 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 6 2 230712847315816274 = some 230712847315816274 := by decide +kernel
private theorem endpoint_16_59_prefix_8 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 8 214630366240582966 = some 230712847315816274 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 6 2 214630366240582966 230712847315816274 230712847315816274 endpoint_16_59_prefix_6 endpoint_16_59_window_6
private theorem endpoint_16_59_window_8 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 8 2 230712847315816274 = some 230712847315816274 := by decide +kernel
private theorem endpoint_16_59_prefix_10 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 10 214630366240582966 = some 230712847315816274 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 8 2 214630366240582966 230712847315816274 230712847315816274 endpoint_16_59_prefix_8 endpoint_16_59_window_8
private theorem endpoint_16_59_window_10 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 10 2 230712847315816274 = some 230712847315816274 := by decide +kernel
private theorem endpoint_16_59_prefix_12 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 12 214630366240582966 = some 230712847315816274 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 10 2 214630366240582966 230712847315816274 230712847315816274 endpoint_16_59_prefix_10 endpoint_16_59_window_10
private theorem endpoint_16_59_window_12 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 12 2 230712847315816274 = some 230712847315816274 := by decide +kernel
private theorem endpoint_16_59_prefix_14 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 14 214630366240582966 = some 230712847315816274 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 12 2 214630366240582966 230712847315816274 230712847315816274 endpoint_16_59_prefix_12 endpoint_16_59_window_12
private theorem endpoint_16_59_window_14 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 14 1 230712847315816274 = some 230712847315816274 := by decide +kernel
private theorem endpoint_16_59_prefix_15 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 15 214630366240582966 = some 230712847315816274 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 14 1 214630366240582966 230712847315816274 230712847315816274 endpoint_16_59_prefix_14 endpoint_16_59_window_14

def endpoint_16_59 : CertifiedEndpoint :=
  ⟨⟨16, 59, 1999⟩, 230712847315816274, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_59_flag endpoint_16_59_sources 15 214630366240582966 230712847315816274 rfl endpoint_16_59_base endpoint_16_59_prefix_15) (by decide)⟩
private def endpoint_16_60_flag : Flag := ⟨16, 60, 1942⟩
private def endpoint_16_60_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_60_base : receiptBase endpoint_16_60_flag endpoint_16_60_sources = some 211789994786648063 := by decide +kernel
private theorem endpoint_16_60_window_0 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 2 211789994786648063 = some 231676136251109352 := by decide +kernel
private theorem endpoint_16_60_window_2 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 2 2 231676136251109352 = some 231676136251109352 := by decide +kernel
private theorem endpoint_16_60_prefix_4 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 4 211789994786648063 = some 231676136251109352 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 2 2 211789994786648063 231676136251109352 231676136251109352 endpoint_16_60_window_0 endpoint_16_60_window_2
private theorem endpoint_16_60_window_4 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 4 2 231676136251109352 = some 231676136251109352 := by decide +kernel
private theorem endpoint_16_60_prefix_6 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 6 211789994786648063 = some 231676136251109352 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 4 2 211789994786648063 231676136251109352 231676136251109352 endpoint_16_60_prefix_4 endpoint_16_60_window_4
private theorem endpoint_16_60_window_6 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 6 2 231676136251109352 = some 231676136251109352 := by decide +kernel
private theorem endpoint_16_60_prefix_8 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 8 211789994786648063 = some 231676136251109352 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 6 2 211789994786648063 231676136251109352 231676136251109352 endpoint_16_60_prefix_6 endpoint_16_60_window_6
private theorem endpoint_16_60_window_8 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 8 2 231676136251109352 = some 231676136251109352 := by decide +kernel
private theorem endpoint_16_60_prefix_10 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 10 211789994786648063 = some 231676136251109352 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 8 2 211789994786648063 231676136251109352 231676136251109352 endpoint_16_60_prefix_8 endpoint_16_60_window_8
private theorem endpoint_16_60_window_10 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 10 2 231676136251109352 = some 231676136251109352 := by decide +kernel
private theorem endpoint_16_60_prefix_12 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 12 211789994786648063 = some 231676136251109352 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 10 2 211789994786648063 231676136251109352 231676136251109352 endpoint_16_60_prefix_10 endpoint_16_60_window_10
private theorem endpoint_16_60_window_12 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 12 2 231676136251109352 = some 231676136251109352 := by decide +kernel
private theorem endpoint_16_60_prefix_14 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 14 211789994786648063 = some 231676136251109352 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 12 2 211789994786648063 231676136251109352 231676136251109352 endpoint_16_60_prefix_12 endpoint_16_60_window_12
private theorem endpoint_16_60_window_14 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 14 1 231676136251109352 = some 231676136251109352 := by decide +kernel
private theorem endpoint_16_60_prefix_15 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 15 211789994786648063 = some 231676136251109352 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 14 1 211789994786648063 231676136251109352 231676136251109352 endpoint_16_60_prefix_14 endpoint_16_60_window_14

def endpoint_16_60 : CertifiedEndpoint :=
  ⟨⟨16, 60, 1942⟩, 231676136251109352, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_60_flag endpoint_16_60_sources 15 211789994786648063 231676136251109352 rfl endpoint_16_60_base endpoint_16_60_prefix_15) (by decide)⟩
private def endpoint_16_61_flag : Flag := ⟨16, 61, 1884⟩
private def endpoint_16_61_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_61_base : receiptBase endpoint_16_61_flag endpoint_16_61_sources = some 208662186375872034 := by decide +kernel
private theorem endpoint_16_61_window_0 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 2 208662186375872034 = some 232432050344892199 := by decide +kernel
private theorem endpoint_16_61_window_2 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 2 2 232432050344892199 = some 232432050344892199 := by decide +kernel
private theorem endpoint_16_61_prefix_4 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 4 208662186375872034 = some 232432050344892199 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 2 2 208662186375872034 232432050344892199 232432050344892199 endpoint_16_61_window_0 endpoint_16_61_window_2
private theorem endpoint_16_61_window_4 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 4 2 232432050344892199 = some 232432050344892199 := by decide +kernel
private theorem endpoint_16_61_prefix_6 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 6 208662186375872034 = some 232432050344892199 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 4 2 208662186375872034 232432050344892199 232432050344892199 endpoint_16_61_prefix_4 endpoint_16_61_window_4
private theorem endpoint_16_61_window_6 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 6 2 232432050344892199 = some 232432050344892199 := by decide +kernel
private theorem endpoint_16_61_prefix_8 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 8 208662186375872034 = some 232432050344892199 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 6 2 208662186375872034 232432050344892199 232432050344892199 endpoint_16_61_prefix_6 endpoint_16_61_window_6
private theorem endpoint_16_61_window_8 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 8 2 232432050344892199 = some 232432050344892199 := by decide +kernel
private theorem endpoint_16_61_prefix_10 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 10 208662186375872034 = some 232432050344892199 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 8 2 208662186375872034 232432050344892199 232432050344892199 endpoint_16_61_prefix_8 endpoint_16_61_window_8
private theorem endpoint_16_61_window_10 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 10 2 232432050344892199 = some 232432050344892199 := by decide +kernel
private theorem endpoint_16_61_prefix_12 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 12 208662186375872034 = some 232432050344892199 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 10 2 208662186375872034 232432050344892199 232432050344892199 endpoint_16_61_prefix_10 endpoint_16_61_window_10
private theorem endpoint_16_61_window_12 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 12 2 232432050344892199 = some 232432050344892199 := by decide +kernel
private theorem endpoint_16_61_prefix_14 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 14 208662186375872034 = some 232432050344892199 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 12 2 208662186375872034 232432050344892199 232432050344892199 endpoint_16_61_prefix_12 endpoint_16_61_window_12
private theorem endpoint_16_61_window_14 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 14 1 232432050344892199 = some 232432050344892199 := by decide +kernel
private theorem endpoint_16_61_prefix_15 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 15 208662186375872034 = some 232432050344892199 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 14 1 208662186375872034 232432050344892199 232432050344892199 endpoint_16_61_prefix_14 endpoint_16_61_window_14

def endpoint_16_61 : CertifiedEndpoint :=
  ⟨⟨16, 61, 1884⟩, 232432050344892199, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_61_flag endpoint_16_61_sources 15 208662186375872034 232432050344892199 rfl endpoint_16_61_base endpoint_16_61_prefix_15) (by decide)⟩
private def endpoint_16_62_flag : Flag := ⟨16, 62, 1824⟩
private def endpoint_16_62_sources : Sources := ⟨contact15, contact15, contact12⟩
private theorem endpoint_16_62_base : receiptBase endpoint_16_62_flag endpoint_16_62_sources = some 206130684053390692 := by decide +kernel
private theorem endpoint_16_62_window_0 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 2 206130684053390692 = some 226210908053566584 := by decide +kernel
private theorem endpoint_16_62_window_2 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 2 2 226210908053566584 = some 226210908053566584 := by decide +kernel
private theorem endpoint_16_62_prefix_4 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 4 206130684053390692 = some 226210908053566584 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 2 2 206130684053390692 226210908053566584 226210908053566584 endpoint_16_62_window_0 endpoint_16_62_window_2
private theorem endpoint_16_62_window_4 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 4 2 226210908053566584 = some 226210908053566584 := by decide +kernel
private theorem endpoint_16_62_prefix_6 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 6 206130684053390692 = some 226210908053566584 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 4 2 206130684053390692 226210908053566584 226210908053566584 endpoint_16_62_prefix_4 endpoint_16_62_window_4
private theorem endpoint_16_62_window_6 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 6 2 226210908053566584 = some 226210908053566584 := by decide +kernel
private theorem endpoint_16_62_prefix_8 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 8 206130684053390692 = some 226210908053566584 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 6 2 206130684053390692 226210908053566584 226210908053566584 endpoint_16_62_prefix_6 endpoint_16_62_window_6
private theorem endpoint_16_62_window_8 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 8 2 226210908053566584 = some 226210908053566584 := by decide +kernel
private theorem endpoint_16_62_prefix_10 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 10 206130684053390692 = some 226210908053566584 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 8 2 206130684053390692 226210908053566584 226210908053566584 endpoint_16_62_prefix_8 endpoint_16_62_window_8
private theorem endpoint_16_62_window_10 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 10 2 226210908053566584 = some 226210908053566584 := by decide +kernel
private theorem endpoint_16_62_prefix_12 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 12 206130684053390692 = some 226210908053566584 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 10 2 206130684053390692 226210908053566584 226210908053566584 endpoint_16_62_prefix_10 endpoint_16_62_window_10
private theorem endpoint_16_62_window_12 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 12 2 226210908053566584 = some 226210908053566584 := by decide +kernel
private theorem endpoint_16_62_prefix_14 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 14 206130684053390692 = some 226210908053566584 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 12 2 206130684053390692 226210908053566584 226210908053566584 endpoint_16_62_prefix_12 endpoint_16_62_window_12
private theorem endpoint_16_62_window_14 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 14 1 226210908053566584 = some 226210908053566584 := by decide +kernel
private theorem endpoint_16_62_prefix_15 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 15 206130684053390692 = some 226210908053566584 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 14 1 206130684053390692 226210908053566584 226210908053566584 endpoint_16_62_prefix_14 endpoint_16_62_window_14

def endpoint_16_62 : CertifiedEndpoint :=
  ⟨⟨16, 62, 1824⟩, 226210908053566584, .terminal ⟨contact15, contact15, contact12⟩ (finish_receipt_window endpoint_16_62_flag endpoint_16_62_sources 15 206130684053390692 226210908053566584 rfl endpoint_16_62_base endpoint_16_62_prefix_15) (by decide)⟩
private def endpoint_16_63_flag : Flag := ⟨16, 63, 1762⟩
private def endpoint_16_63_sources : Sources := ⟨contact29, contact16, contact13⟩
private theorem endpoint_16_63_base : receiptBase endpoint_16_63_flag endpoint_16_63_sources = some 202707295468783562 := by decide +kernel
private theorem endpoint_16_63_window_0 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 2 202707295468783562 = some 224916439370416977 := by decide +kernel
private theorem endpoint_16_63_window_2 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 2 2 224916439370416977 = some 224916439370416977 := by decide +kernel
private theorem endpoint_16_63_prefix_4 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 4 202707295468783562 = some 224916439370416977 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 2 2 202707295468783562 224916439370416977 224916439370416977 endpoint_16_63_window_0 endpoint_16_63_window_2
private theorem endpoint_16_63_window_4 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 4 2 224916439370416977 = some 224916439370416977 := by decide +kernel
private theorem endpoint_16_63_prefix_6 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 6 202707295468783562 = some 224916439370416977 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 4 2 202707295468783562 224916439370416977 224916439370416977 endpoint_16_63_prefix_4 endpoint_16_63_window_4
private theorem endpoint_16_63_window_6 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 6 2 224916439370416977 = some 224916439370416977 := by decide +kernel
private theorem endpoint_16_63_prefix_8 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 8 202707295468783562 = some 224916439370416977 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 6 2 202707295468783562 224916439370416977 224916439370416977 endpoint_16_63_prefix_6 endpoint_16_63_window_6
private theorem endpoint_16_63_window_8 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 8 2 224916439370416977 = some 224916439370416977 := by decide +kernel
private theorem endpoint_16_63_prefix_10 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 10 202707295468783562 = some 224916439370416977 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 8 2 202707295468783562 224916439370416977 224916439370416977 endpoint_16_63_prefix_8 endpoint_16_63_window_8
private theorem endpoint_16_63_window_10 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 10 2 224916439370416977 = some 224916439370416977 := by decide +kernel
private theorem endpoint_16_63_prefix_12 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 12 202707295468783562 = some 224916439370416977 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 10 2 202707295468783562 224916439370416977 224916439370416977 endpoint_16_63_prefix_10 endpoint_16_63_window_10
private theorem endpoint_16_63_window_12 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 12 2 224916439370416977 = some 224916439370416977 := by decide +kernel
private theorem endpoint_16_63_prefix_14 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 14 202707295468783562 = some 224916439370416977 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 12 2 202707295468783562 224916439370416977 224916439370416977 endpoint_16_63_prefix_12 endpoint_16_63_window_12
private theorem endpoint_16_63_window_14 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 14 1 224916439370416977 = some 224916439370416977 := by decide +kernel
private theorem endpoint_16_63_prefix_15 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 15 202707295468783562 = some 224916439370416977 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 14 1 202707295468783562 224916439370416977 224916439370416977 endpoint_16_63_prefix_14 endpoint_16_63_window_14

def endpoint_16_63 : CertifiedEndpoint :=
  ⟨⟨16, 63, 1762⟩, 224916439370416977, .terminal ⟨contact29, contact16, contact13⟩ (finish_receipt_window endpoint_16_63_flag endpoint_16_63_sources 15 202707295468783562 224916439370416977 rfl endpoint_16_63_base endpoint_16_63_prefix_15) (by decide)⟩
private def endpoint_16_64_flag : Flag := ⟨16, 64, 1699⟩
private def endpoint_16_64_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_16_64_base : receiptBase endpoint_16_64_flag endpoint_16_64_sources = some 200010243739964885 := by decide +kernel
private theorem endpoint_16_64_window_0 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 2 200010243739964885 = some 209581613041866420 := by decide +kernel
private theorem endpoint_16_64_window_2 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 2 2 209581613041866420 = some 209581613041866420 := by decide +kernel
private theorem endpoint_16_64_prefix_4 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 4 200010243739964885 = some 209581613041866420 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 2 2 200010243739964885 209581613041866420 209581613041866420 endpoint_16_64_window_0 endpoint_16_64_window_2
private theorem endpoint_16_64_window_4 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 4 2 209581613041866420 = some 209581613041866420 := by decide +kernel
private theorem endpoint_16_64_prefix_6 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 6 200010243739964885 = some 209581613041866420 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 4 2 200010243739964885 209581613041866420 209581613041866420 endpoint_16_64_prefix_4 endpoint_16_64_window_4
private theorem endpoint_16_64_window_6 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 6 2 209581613041866420 = some 209581613041866420 := by decide +kernel
private theorem endpoint_16_64_prefix_8 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 8 200010243739964885 = some 209581613041866420 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 6 2 200010243739964885 209581613041866420 209581613041866420 endpoint_16_64_prefix_6 endpoint_16_64_window_6
private theorem endpoint_16_64_window_8 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 8 2 209581613041866420 = some 209581613041866420 := by decide +kernel
private theorem endpoint_16_64_prefix_10 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 10 200010243739964885 = some 209581613041866420 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 8 2 200010243739964885 209581613041866420 209581613041866420 endpoint_16_64_prefix_8 endpoint_16_64_window_8
private theorem endpoint_16_64_window_10 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 10 2 209581613041866420 = some 209581613041866420 := by decide +kernel
private theorem endpoint_16_64_prefix_12 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 12 200010243739964885 = some 209581613041866420 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 10 2 200010243739964885 209581613041866420 209581613041866420 endpoint_16_64_prefix_10 endpoint_16_64_window_10
private theorem endpoint_16_64_window_12 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 12 2 209581613041866420 = some 209581613041866420 := by decide +kernel
private theorem endpoint_16_64_prefix_14 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 14 200010243739964885 = some 209581613041866420 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 12 2 200010243739964885 209581613041866420 209581613041866420 endpoint_16_64_prefix_12 endpoint_16_64_window_12
private theorem endpoint_16_64_window_14 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 14 1 209581613041866420 = some 209581613041866420 := by decide +kernel
private theorem endpoint_16_64_prefix_15 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 15 200010243739964885 = some 209581613041866420 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 14 1 200010243739964885 209581613041866420 209581613041866420 endpoint_16_64_prefix_14 endpoint_16_64_window_14

def endpoint_16_64 : CertifiedEndpoint :=
  ⟨⟨16, 64, 1699⟩, 209581613041866420, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_16_64_flag endpoint_16_64_sources 15 200010243739964885 209581613041866420 rfl endpoint_16_64_base endpoint_16_64_prefix_15) (by decide)⟩
private def endpoint_16_65_flag : Flag := ⟨16, 65, 1634⟩
private def endpoint_16_65_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_16_65_base : receiptBase endpoint_16_65_flag endpoint_16_65_sources = some 195097800614641080 := by decide +kernel
private theorem endpoint_16_65_window_0 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 2 195097800614641080 = some 208834156331685430 := by decide +kernel
private theorem endpoint_16_65_window_2 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 2 2 208834156331685430 = some 208834156331685430 := by decide +kernel
private theorem endpoint_16_65_prefix_4 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 4 195097800614641080 = some 208834156331685430 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 2 2 195097800614641080 208834156331685430 208834156331685430 endpoint_16_65_window_0 endpoint_16_65_window_2
private theorem endpoint_16_65_window_4 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 4 2 208834156331685430 = some 208834156331685430 := by decide +kernel
private theorem endpoint_16_65_prefix_6 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 6 195097800614641080 = some 208834156331685430 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 4 2 195097800614641080 208834156331685430 208834156331685430 endpoint_16_65_prefix_4 endpoint_16_65_window_4
private theorem endpoint_16_65_window_6 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 6 2 208834156331685430 = some 208834156331685430 := by decide +kernel
private theorem endpoint_16_65_prefix_8 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 8 195097800614641080 = some 208834156331685430 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 6 2 195097800614641080 208834156331685430 208834156331685430 endpoint_16_65_prefix_6 endpoint_16_65_window_6
private theorem endpoint_16_65_window_8 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 8 2 208834156331685430 = some 208834156331685430 := by decide +kernel
private theorem endpoint_16_65_prefix_10 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 10 195097800614641080 = some 208834156331685430 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 8 2 195097800614641080 208834156331685430 208834156331685430 endpoint_16_65_prefix_8 endpoint_16_65_window_8
private theorem endpoint_16_65_window_10 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 10 2 208834156331685430 = some 208834156331685430 := by decide +kernel
private theorem endpoint_16_65_prefix_12 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 12 195097800614641080 = some 208834156331685430 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 10 2 195097800614641080 208834156331685430 208834156331685430 endpoint_16_65_prefix_10 endpoint_16_65_window_10
private theorem endpoint_16_65_window_12 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 12 2 208834156331685430 = some 208834156331685430 := by decide +kernel
private theorem endpoint_16_65_prefix_14 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 14 195097800614641080 = some 208834156331685430 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 12 2 195097800614641080 208834156331685430 208834156331685430 endpoint_16_65_prefix_12 endpoint_16_65_window_12
private theorem endpoint_16_65_window_14 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 14 1 208834156331685430 = some 208834156331685430 := by decide +kernel
private theorem endpoint_16_65_prefix_15 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 15 195097800614641080 = some 208834156331685430 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 14 1 195097800614641080 208834156331685430 208834156331685430 endpoint_16_65_prefix_14 endpoint_16_65_window_14

def endpoint_16_65 : CertifiedEndpoint :=
  ⟨⟨16, 65, 1634⟩, 208834156331685430, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_16_65_flag endpoint_16_65_sources 15 195097800614641080 208834156331685430 rfl endpoint_16_65_base endpoint_16_65_prefix_15) (by decide)⟩
private def endpoint_16_66_flag : Flag := ⟨16, 66, 1567⟩
private def endpoint_16_66_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_16_66_base : receiptBase endpoint_16_66_flag endpoint_16_66_sources = some 189734221298004828 := by decide +kernel
private theorem endpoint_16_66_window_0 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 2 189734221298004828 = some 207783793696416788 := by decide +kernel
private theorem endpoint_16_66_window_2 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 2 2 207783793696416788 = some 207783793696416788 := by decide +kernel
private theorem endpoint_16_66_prefix_4 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 4 189734221298004828 = some 207783793696416788 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 2 2 189734221298004828 207783793696416788 207783793696416788 endpoint_16_66_window_0 endpoint_16_66_window_2
private theorem endpoint_16_66_window_4 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 4 2 207783793696416788 = some 207783793696416788 := by decide +kernel
private theorem endpoint_16_66_prefix_6 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 6 189734221298004828 = some 207783793696416788 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 4 2 189734221298004828 207783793696416788 207783793696416788 endpoint_16_66_prefix_4 endpoint_16_66_window_4
private theorem endpoint_16_66_window_6 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 6 2 207783793696416788 = some 207783793696416788 := by decide +kernel
private theorem endpoint_16_66_prefix_8 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 8 189734221298004828 = some 207783793696416788 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 6 2 189734221298004828 207783793696416788 207783793696416788 endpoint_16_66_prefix_6 endpoint_16_66_window_6
private theorem endpoint_16_66_window_8 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 8 2 207783793696416788 = some 207783793696416788 := by decide +kernel
private theorem endpoint_16_66_prefix_10 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 10 189734221298004828 = some 207783793696416788 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 8 2 189734221298004828 207783793696416788 207783793696416788 endpoint_16_66_prefix_8 endpoint_16_66_window_8
private theorem endpoint_16_66_window_10 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 10 2 207783793696416788 = some 207783793696416788 := by decide +kernel
private theorem endpoint_16_66_prefix_12 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 12 189734221298004828 = some 207783793696416788 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 10 2 189734221298004828 207783793696416788 207783793696416788 endpoint_16_66_prefix_10 endpoint_16_66_window_10
private theorem endpoint_16_66_window_12 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 12 2 207783793696416788 = some 207783793696416788 := by decide +kernel
private theorem endpoint_16_66_prefix_14 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 14 189734221298004828 = some 207783793696416788 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 12 2 189734221298004828 207783793696416788 207783793696416788 endpoint_16_66_prefix_12 endpoint_16_66_window_12
private theorem endpoint_16_66_window_14 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 14 1 207783793696416788 = some 207783793696416788 := by decide +kernel
private theorem endpoint_16_66_prefix_15 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 15 189734221298004828 = some 207783793696416788 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 14 1 189734221298004828 207783793696416788 207783793696416788 endpoint_16_66_prefix_14 endpoint_16_66_window_14

def endpoint_16_66 : CertifiedEndpoint :=
  ⟨⟨16, 66, 1567⟩, 207783793696416788, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_16_66_flag endpoint_16_66_sources 15 189734221298004828 207783793696416788 rfl endpoint_16_66_base endpoint_16_66_prefix_15) (by decide)⟩
private def endpoint_16_67_flag : Flag := ⟨16, 67, 1498⟩
private def endpoint_16_67_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_16_67_base : receiptBase endpoint_16_67_flag endpoint_16_67_sources = some 185385974093511729 := by decide +kernel
private theorem endpoint_16_67_window_0 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 2 185385974093511729 = some 191175915790948700 := by decide +kernel
private theorem endpoint_16_67_window_2 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 2 2 191175915790948700 = some 191175915790948700 := by decide +kernel
private theorem endpoint_16_67_prefix_4 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 4 185385974093511729 = some 191175915790948700 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 2 2 185385974093511729 191175915790948700 191175915790948700 endpoint_16_67_window_0 endpoint_16_67_window_2
private theorem endpoint_16_67_window_4 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 4 2 191175915790948700 = some 191175915790948700 := by decide +kernel
private theorem endpoint_16_67_prefix_6 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 6 185385974093511729 = some 191175915790948700 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 4 2 185385974093511729 191175915790948700 191175915790948700 endpoint_16_67_prefix_4 endpoint_16_67_window_4
private theorem endpoint_16_67_window_6 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 6 2 191175915790948700 = some 191175915790948700 := by decide +kernel
private theorem endpoint_16_67_prefix_8 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 8 185385974093511729 = some 191175915790948700 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 6 2 185385974093511729 191175915790948700 191175915790948700 endpoint_16_67_prefix_6 endpoint_16_67_window_6
private theorem endpoint_16_67_window_8 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 8 2 191175915790948700 = some 191175915790948700 := by decide +kernel
private theorem endpoint_16_67_prefix_10 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 10 185385974093511729 = some 191175915790948700 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 8 2 185385974093511729 191175915790948700 191175915790948700 endpoint_16_67_prefix_8 endpoint_16_67_window_8
private theorem endpoint_16_67_window_10 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 10 2 191175915790948700 = some 191175915790948700 := by decide +kernel
private theorem endpoint_16_67_prefix_12 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 12 185385974093511729 = some 191175915790948700 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 10 2 185385974093511729 191175915790948700 191175915790948700 endpoint_16_67_prefix_10 endpoint_16_67_window_10
private theorem endpoint_16_67_window_12 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 12 2 191175915790948700 = some 191175915790948700 := by decide +kernel
private theorem endpoint_16_67_prefix_14 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 14 185385974093511729 = some 191175915790948700 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 12 2 185385974093511729 191175915790948700 191175915790948700 endpoint_16_67_prefix_12 endpoint_16_67_window_12
private theorem endpoint_16_67_window_14 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 14 1 191175915790948700 = some 191175915790948700 := by decide +kernel
private theorem endpoint_16_67_prefix_15 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 15 185385974093511729 = some 191175915790948700 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 14 1 185385974093511729 191175915790948700 191175915790948700 endpoint_16_67_prefix_14 endpoint_16_67_window_14

def endpoint_16_67 : CertifiedEndpoint :=
  ⟨⟨16, 67, 1498⟩, 191175915790948700, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_16_67_flag endpoint_16_67_sources 15 185385974093511729 191175915790948700 rfl endpoint_16_67_base endpoint_16_67_prefix_15) (by decide)⟩
private def endpoint_16_68_flag : Flag := ⟨16, 68, 1426⟩
private def endpoint_16_68_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_16_68_base : receiptBase endpoint_16_68_flag endpoint_16_68_sources = some 178903581275489626 := by decide +kernel
private theorem endpoint_16_68_window_0 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 2 178903581275489626 = some 189163679644743908 := by decide +kernel
private theorem endpoint_16_68_window_2 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 2 2 189163679644743908 = some 189163679644743908 := by decide +kernel
private theorem endpoint_16_68_prefix_4 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 4 178903581275489626 = some 189163679644743908 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 2 2 178903581275489626 189163679644743908 189163679644743908 endpoint_16_68_window_0 endpoint_16_68_window_2
private theorem endpoint_16_68_window_4 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 4 2 189163679644743908 = some 189163679644743908 := by decide +kernel
private theorem endpoint_16_68_prefix_6 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 6 178903581275489626 = some 189163679644743908 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 4 2 178903581275489626 189163679644743908 189163679644743908 endpoint_16_68_prefix_4 endpoint_16_68_window_4
private theorem endpoint_16_68_window_6 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 6 2 189163679644743908 = some 189163679644743908 := by decide +kernel
private theorem endpoint_16_68_prefix_8 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 8 178903581275489626 = some 189163679644743908 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 6 2 178903581275489626 189163679644743908 189163679644743908 endpoint_16_68_prefix_6 endpoint_16_68_window_6
private theorem endpoint_16_68_window_8 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 8 2 189163679644743908 = some 189163679644743908 := by decide +kernel
private theorem endpoint_16_68_prefix_10 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 10 178903581275489626 = some 189163679644743908 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 8 2 178903581275489626 189163679644743908 189163679644743908 endpoint_16_68_prefix_8 endpoint_16_68_window_8
private theorem endpoint_16_68_window_10 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 10 2 189163679644743908 = some 189163679644743908 := by decide +kernel
private theorem endpoint_16_68_prefix_12 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 12 178903581275489626 = some 189163679644743908 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 10 2 178903581275489626 189163679644743908 189163679644743908 endpoint_16_68_prefix_10 endpoint_16_68_window_10
private theorem endpoint_16_68_window_12 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 12 2 189163679644743908 = some 189163679644743908 := by decide +kernel
private theorem endpoint_16_68_prefix_14 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 14 178903581275489626 = some 189163679644743908 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 12 2 178903581275489626 189163679644743908 189163679644743908 endpoint_16_68_prefix_12 endpoint_16_68_window_12
private theorem endpoint_16_68_window_14 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 14 1 189163679644743908 = some 189163679644743908 := by decide +kernel
private theorem endpoint_16_68_prefix_15 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 15 178903581275489626 = some 189163679644743908 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 14 1 178903581275489626 189163679644743908 189163679644743908 endpoint_16_68_prefix_14 endpoint_16_68_window_14

def endpoint_16_68 : CertifiedEndpoint :=
  ⟨⟨16, 68, 1426⟩, 189163679644743908, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_16_68_flag endpoint_16_68_sources 15 178903581275489626 189163679644743908 rfl endpoint_16_68_base endpoint_16_68_prefix_15) (by decide)⟩
private def endpoint_16_69_flag : Flag := ⟨16, 69, 1353⟩
private def endpoint_16_69_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_16_69_base : receiptBase endpoint_16_69_flag endpoint_16_69_sources = some 172059891129239276 := by decide +kernel
private theorem endpoint_16_69_window_0 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 2 172059891129239276 = some 186897389779485675 := by decide +kernel
private theorem endpoint_16_69_window_2 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 2 2 186897389779485675 = some 186897389779485675 := by decide +kernel
private theorem endpoint_16_69_prefix_4 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 4 172059891129239276 = some 186897389779485675 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 2 2 172059891129239276 186897389779485675 186897389779485675 endpoint_16_69_window_0 endpoint_16_69_window_2
private theorem endpoint_16_69_window_4 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 4 2 186897389779485675 = some 186897389779485675 := by decide +kernel
private theorem endpoint_16_69_prefix_6 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 6 172059891129239276 = some 186897389779485675 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 4 2 172059891129239276 186897389779485675 186897389779485675 endpoint_16_69_prefix_4 endpoint_16_69_window_4
private theorem endpoint_16_69_window_6 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 6 2 186897389779485675 = some 186897389779485675 := by decide +kernel
private theorem endpoint_16_69_prefix_8 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 8 172059891129239276 = some 186897389779485675 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 6 2 172059891129239276 186897389779485675 186897389779485675 endpoint_16_69_prefix_6 endpoint_16_69_window_6
private theorem endpoint_16_69_window_8 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 8 2 186897389779485675 = some 186897389779485675 := by decide +kernel
private theorem endpoint_16_69_prefix_10 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 10 172059891129239276 = some 186897389779485675 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 8 2 172059891129239276 186897389779485675 186897389779485675 endpoint_16_69_prefix_8 endpoint_16_69_window_8
private theorem endpoint_16_69_window_10 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 10 2 186897389779485675 = some 186897389779485675 := by decide +kernel
private theorem endpoint_16_69_prefix_12 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 12 172059891129239276 = some 186897389779485675 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 10 2 172059891129239276 186897389779485675 186897389779485675 endpoint_16_69_prefix_10 endpoint_16_69_window_10
private theorem endpoint_16_69_window_12 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 12 2 186897389779485675 = some 186897389779485675 := by decide +kernel
private theorem endpoint_16_69_prefix_14 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 14 172059891129239276 = some 186897389779485675 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 12 2 172059891129239276 186897389779485675 186897389779485675 endpoint_16_69_prefix_12 endpoint_16_69_window_12
private theorem endpoint_16_69_window_14 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 14 1 186897389779485675 = some 186897389779485675 := by decide +kernel
private theorem endpoint_16_69_prefix_15 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 15 172059891129239276 = some 186897389779485675 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 14 1 172059891129239276 186897389779485675 186897389779485675 endpoint_16_69_prefix_14 endpoint_16_69_window_14

def endpoint_16_69 : CertifiedEndpoint :=
  ⟨⟨16, 69, 1353⟩, 186897389779485675, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_16_69_flag endpoint_16_69_sources 15 172059891129239276 186897389779485675 rfl endpoint_16_69_base endpoint_16_69_prefix_15) (by decide)⟩
private def endpoint_16_70_flag : Flag := ⟨16, 70, 1278⟩
private def endpoint_16_70_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_16_70_base : receiptBase endpoint_16_70_flag endpoint_16_70_sources = some 165122325908008164 := by decide +kernel
private theorem endpoint_16_70_window_0 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 2 165122325908008164 = some 181061377651022644 := by decide +kernel
private theorem endpoint_16_70_window_2 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 2 2 181061377651022644 = some 181061377651022644 := by decide +kernel
private theorem endpoint_16_70_prefix_4 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 4 165122325908008164 = some 181061377651022644 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 2 2 165122325908008164 181061377651022644 181061377651022644 endpoint_16_70_window_0 endpoint_16_70_window_2
private theorem endpoint_16_70_window_4 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 4 2 181061377651022644 = some 181061377651022644 := by decide +kernel
private theorem endpoint_16_70_prefix_6 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 6 165122325908008164 = some 181061377651022644 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 4 2 165122325908008164 181061377651022644 181061377651022644 endpoint_16_70_prefix_4 endpoint_16_70_window_4
private theorem endpoint_16_70_window_6 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 6 2 181061377651022644 = some 181061377651022644 := by decide +kernel
private theorem endpoint_16_70_prefix_8 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 8 165122325908008164 = some 181061377651022644 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 6 2 165122325908008164 181061377651022644 181061377651022644 endpoint_16_70_prefix_6 endpoint_16_70_window_6
private theorem endpoint_16_70_window_8 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 8 2 181061377651022644 = some 181061377651022644 := by decide +kernel
private theorem endpoint_16_70_prefix_10 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 10 165122325908008164 = some 181061377651022644 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 8 2 165122325908008164 181061377651022644 181061377651022644 endpoint_16_70_prefix_8 endpoint_16_70_window_8
private theorem endpoint_16_70_window_10 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 10 2 181061377651022644 = some 181061377651022644 := by decide +kernel
private theorem endpoint_16_70_prefix_12 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 12 165122325908008164 = some 181061377651022644 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 10 2 165122325908008164 181061377651022644 181061377651022644 endpoint_16_70_prefix_10 endpoint_16_70_window_10
private theorem endpoint_16_70_window_12 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 12 2 181061377651022644 = some 181061377651022644 := by decide +kernel
private theorem endpoint_16_70_prefix_14 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 14 165122325908008164 = some 181061377651022644 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 12 2 165122325908008164 181061377651022644 181061377651022644 endpoint_16_70_prefix_12 endpoint_16_70_window_12
private theorem endpoint_16_70_window_14 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 14 1 181061377651022644 = some 181061377651022644 := by decide +kernel
private theorem endpoint_16_70_prefix_15 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 15 165122325908008164 = some 181061377651022644 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 14 1 165122325908008164 181061377651022644 181061377651022644 endpoint_16_70_prefix_14 endpoint_16_70_window_14

def endpoint_16_70 : CertifiedEndpoint :=
  ⟨⟨16, 70, 1278⟩, 181061377651022644, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_16_70_flag endpoint_16_70_sources 15 165122325908008164 181061377651022644 rfl endpoint_16_70_base endpoint_16_70_prefix_15) (by decide)⟩
private def endpoint_16_71_flag : Flag := ⟨16, 71, 1200⟩
private def endpoint_16_71_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_16_71_base : receiptBase endpoint_16_71_flag endpoint_16_71_sources = some 158220640480744335 := by decide +kernel
private theorem endpoint_16_71_window_0 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 2 158220640480744335 = some 170317100522423472 := by decide +kernel
private theorem endpoint_16_71_window_2 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 2 2 170317100522423472 = some 170317100522423472 := by decide +kernel
private theorem endpoint_16_71_prefix_4 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 4 158220640480744335 = some 170317100522423472 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 2 2 158220640480744335 170317100522423472 170317100522423472 endpoint_16_71_window_0 endpoint_16_71_window_2
private theorem endpoint_16_71_window_4 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 4 2 170317100522423472 = some 170317100522423472 := by decide +kernel
private theorem endpoint_16_71_prefix_6 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 6 158220640480744335 = some 170317100522423472 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 4 2 158220640480744335 170317100522423472 170317100522423472 endpoint_16_71_prefix_4 endpoint_16_71_window_4
private theorem endpoint_16_71_window_6 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 6 2 170317100522423472 = some 170317100522423472 := by decide +kernel
private theorem endpoint_16_71_prefix_8 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 8 158220640480744335 = some 170317100522423472 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 6 2 158220640480744335 170317100522423472 170317100522423472 endpoint_16_71_prefix_6 endpoint_16_71_window_6
private theorem endpoint_16_71_window_8 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 8 2 170317100522423472 = some 170317100522423472 := by decide +kernel
private theorem endpoint_16_71_prefix_10 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 10 158220640480744335 = some 170317100522423472 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 8 2 158220640480744335 170317100522423472 170317100522423472 endpoint_16_71_prefix_8 endpoint_16_71_window_8
private theorem endpoint_16_71_window_10 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 10 2 170317100522423472 = some 170317100522423472 := by decide +kernel
private theorem endpoint_16_71_prefix_12 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 12 158220640480744335 = some 170317100522423472 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 10 2 158220640480744335 170317100522423472 170317100522423472 endpoint_16_71_prefix_10 endpoint_16_71_window_10
private theorem endpoint_16_71_window_12 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 12 2 170317100522423472 = some 170317100522423472 := by decide +kernel
private theorem endpoint_16_71_prefix_14 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 14 158220640480744335 = some 170317100522423472 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 12 2 158220640480744335 170317100522423472 170317100522423472 endpoint_16_71_prefix_12 endpoint_16_71_window_12
private theorem endpoint_16_71_window_14 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 14 1 170317100522423472 = some 170317100522423472 := by decide +kernel
private theorem endpoint_16_71_prefix_15 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 15 158220640480744335 = some 170317100522423472 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 14 1 158220640480744335 170317100522423472 170317100522423472 endpoint_16_71_prefix_14 endpoint_16_71_window_14

def endpoint_16_71 : CertifiedEndpoint :=
  ⟨⟨16, 71, 1200⟩, 170317100522423472, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_16_71_flag endpoint_16_71_sources 15 158220640480744335 170317100522423472 rfl endpoint_16_71_base endpoint_16_71_prefix_15) (by decide)⟩
private def endpoint_16_72_flag : Flag := ⟨16, 72, 1119⟩
private def endpoint_16_72_sources : Sources := ⟨contact31, contact21, contact22⟩
private theorem endpoint_16_72_base : receiptBase endpoint_16_72_flag endpoint_16_72_sources = some 150178001786791419 := by decide +kernel
private theorem endpoint_16_72_window_0 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 2 150178001786791419 = some 164948795947341780 := by decide +kernel
private theorem endpoint_16_72_window_2 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 2 2 164948795947341780 = some 164948795947341780 := by decide +kernel
private theorem endpoint_16_72_prefix_4 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 4 150178001786791419 = some 164948795947341780 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 2 2 150178001786791419 164948795947341780 164948795947341780 endpoint_16_72_window_0 endpoint_16_72_window_2
private theorem endpoint_16_72_window_4 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 4 2 164948795947341780 = some 164948795947341780 := by decide +kernel
private theorem endpoint_16_72_prefix_6 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 6 150178001786791419 = some 164948795947341780 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 4 2 150178001786791419 164948795947341780 164948795947341780 endpoint_16_72_prefix_4 endpoint_16_72_window_4
private theorem endpoint_16_72_window_6 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 6 2 164948795947341780 = some 164948795947341780 := by decide +kernel
private theorem endpoint_16_72_prefix_8 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 8 150178001786791419 = some 164948795947341780 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 6 2 150178001786791419 164948795947341780 164948795947341780 endpoint_16_72_prefix_6 endpoint_16_72_window_6
private theorem endpoint_16_72_window_8 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 8 2 164948795947341780 = some 164948795947341780 := by decide +kernel
private theorem endpoint_16_72_prefix_10 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 10 150178001786791419 = some 164948795947341780 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 8 2 150178001786791419 164948795947341780 164948795947341780 endpoint_16_72_prefix_8 endpoint_16_72_window_8
private theorem endpoint_16_72_window_10 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 10 2 164948795947341780 = some 164948795947341780 := by decide +kernel
private theorem endpoint_16_72_prefix_12 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 12 150178001786791419 = some 164948795947341780 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 10 2 150178001786791419 164948795947341780 164948795947341780 endpoint_16_72_prefix_10 endpoint_16_72_window_10
private theorem endpoint_16_72_window_12 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 12 2 164948795947341780 = some 164948795947341780 := by decide +kernel
private theorem endpoint_16_72_prefix_14 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 14 150178001786791419 = some 164948795947341780 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 12 2 150178001786791419 164948795947341780 164948795947341780 endpoint_16_72_prefix_12 endpoint_16_72_window_12
private theorem endpoint_16_72_window_14 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 14 1 164948795947341780 = some 164948795947341780 := by decide +kernel
private theorem endpoint_16_72_prefix_15 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 15 150178001786791419 = some 164948795947341780 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 14 1 150178001786791419 164948795947341780 164948795947341780 endpoint_16_72_prefix_14 endpoint_16_72_window_14

def endpoint_16_72 : CertifiedEndpoint :=
  ⟨⟨16, 72, 1119⟩, 164948795947341780, .terminal ⟨contact31, contact21, contact22⟩ (finish_receipt_window endpoint_16_72_flag endpoint_16_72_sources 15 150178001786791419 164948795947341780 rfl endpoint_16_72_base endpoint_16_72_prefix_15) (by decide)⟩
private def endpoint_16_73_flag : Flag := ⟨16, 73, 1036⟩
private def endpoint_16_73_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_16_73_base : receiptBase endpoint_16_73_flag endpoint_16_73_sources = some 141546056493875086 := by decide +kernel
private theorem endpoint_16_73_window_0 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 2 141546056493875086 = some 153182454137368649 := by decide +kernel
private theorem endpoint_16_73_window_2 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 2 2 153182454137368649 = some 153182454137368649 := by decide +kernel
private theorem endpoint_16_73_prefix_4 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 4 141546056493875086 = some 153182454137368649 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 2 2 141546056493875086 153182454137368649 153182454137368649 endpoint_16_73_window_0 endpoint_16_73_window_2
private theorem endpoint_16_73_window_4 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 4 2 153182454137368649 = some 153182454137368649 := by decide +kernel
private theorem endpoint_16_73_prefix_6 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 6 141546056493875086 = some 153182454137368649 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 4 2 141546056493875086 153182454137368649 153182454137368649 endpoint_16_73_prefix_4 endpoint_16_73_window_4
private theorem endpoint_16_73_window_6 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 6 2 153182454137368649 = some 153182454137368649 := by decide +kernel
private theorem endpoint_16_73_prefix_8 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 8 141546056493875086 = some 153182454137368649 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 6 2 141546056493875086 153182454137368649 153182454137368649 endpoint_16_73_prefix_6 endpoint_16_73_window_6
private theorem endpoint_16_73_window_8 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 8 2 153182454137368649 = some 153182454137368649 := by decide +kernel
private theorem endpoint_16_73_prefix_10 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 10 141546056493875086 = some 153182454137368649 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 8 2 141546056493875086 153182454137368649 153182454137368649 endpoint_16_73_prefix_8 endpoint_16_73_window_8
private theorem endpoint_16_73_window_10 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 10 2 153182454137368649 = some 153182454137368649 := by decide +kernel
private theorem endpoint_16_73_prefix_12 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 12 141546056493875086 = some 153182454137368649 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 10 2 141546056493875086 153182454137368649 153182454137368649 endpoint_16_73_prefix_10 endpoint_16_73_window_10
private theorem endpoint_16_73_window_12 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 12 2 153182454137368649 = some 153182454137368649 := by decide +kernel
private theorem endpoint_16_73_prefix_14 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 14 141546056493875086 = some 153182454137368649 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 12 2 141546056493875086 153182454137368649 153182454137368649 endpoint_16_73_prefix_12 endpoint_16_73_window_12
private theorem endpoint_16_73_window_14 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 14 1 153182454137368649 = some 153182454137368649 := by decide +kernel
private theorem endpoint_16_73_prefix_15 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 15 141546056493875086 = some 153182454137368649 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 14 1 141546056493875086 153182454137368649 153182454137368649 endpoint_16_73_prefix_14 endpoint_16_73_window_14

def endpoint_16_73 : CertifiedEndpoint :=
  ⟨⟨16, 73, 1036⟩, 153182454137368649, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_16_73_flag endpoint_16_73_sources 15 141546056493875086 153182454137368649 rfl endpoint_16_73_base endpoint_16_73_prefix_15) (by decide)⟩
def endpoint_16_74 : CertifiedEndpoint :=
  ⟨⟨16, 74, 951⟩, 238582127587885413, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_75 : CertifiedEndpoint :=
  ⟨⟨16, 75, 863⟩, 218664396428953880, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_76 : CertifiedEndpoint :=
  ⟨⟨16, 76, 772⟩, 197227497448680796, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_77 : CertifiedEndpoint :=
  ⟨⟨16, 77, 679⟩, 174509618317571844, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_78 : CertifiedEndpoint :=
  ⟨⟨16, 78, 583⟩, 150208523221055709, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_79 : CertifiedEndpoint :=
  ⟨⟨16, 79, 484⟩, 124288185078095473, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_80 : CertifiedEndpoint :=
  ⟨⟨16, 80, 383⟩, 96998800586209125, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_81 : CertifiedEndpoint :=
  ⟨⟨16, 81, 279⟩, 68026124903813044, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_82 : CertifiedEndpoint :=
  ⟨⟨16, 82, 172⟩, 37334130949870312, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_17 : CertifiedEndpoint :=
  ⟨⟨17, 17, 3349⟩, 132846810143858834, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_18 : CertifiedEndpoint :=
  ⟨⟨17, 18, 3323⟩, 136437852508068760, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_19 : CertifiedEndpoint :=
  ⟨⟨17, 19, 3296⟩, 139913468992541383, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_20 : CertifiedEndpoint :=
  ⟨⟨17, 20, 3269⟩, 152608031154618077, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_21 : CertifiedEndpoint :=
  ⟨⟨17, 21, 3242⟩, 165068254083360301, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_22 : CertifiedEndpoint :=
  ⟨⟨17, 22, 3214⟩, 177238739867854766, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_23 : CertifiedEndpoint :=
  ⟨⟨17, 23, 3185⟩, 189106706368101410, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_24 : CertifiedEndpoint :=
  ⟨⟨17, 24, 3157⟩, 200787210119260165, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_25 : CertifiedEndpoint :=
  ⟨⟨17, 25, 3127⟩, 212088493108591040, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_26 : CertifiedEndpoint :=
  ⟨⟨17, 26, 3098⟩, 223202313348834026, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_27 : CertifiedEndpoint :=
  ⟨⟨17, 27, 3067⟩, 233911348547249008, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_28 : CertifiedEndpoint :=
  ⟨⟨17, 28, 3036⟩, 244351958805662688, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_17_29_flag : Flag := ⟨17, 29, 3005⟩
private def endpoint_17_29_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_29_base : receiptBase endpoint_17_29_flag endpoint_17_29_sources = some 175630319435822327 := by decide +kernel
private theorem endpoint_17_29_window_0 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 2 175630319435822327 = some 175630319435822327 := by decide +kernel
private theorem endpoint_17_29_window_2 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 2 2 175630319435822327 = some 175630319435822327 := by decide +kernel
private theorem endpoint_17_29_prefix_4 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 4 175630319435822327 = some 175630319435822327 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 2 2 175630319435822327 175630319435822327 175630319435822327 endpoint_17_29_window_0 endpoint_17_29_window_2
private theorem endpoint_17_29_window_4 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 4 2 175630319435822327 = some 175630319435822327 := by decide +kernel
private theorem endpoint_17_29_prefix_6 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 6 175630319435822327 = some 175630319435822327 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 4 2 175630319435822327 175630319435822327 175630319435822327 endpoint_17_29_prefix_4 endpoint_17_29_window_4
private theorem endpoint_17_29_window_6 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 6 2 175630319435822327 = some 175630319435822327 := by decide +kernel
private theorem endpoint_17_29_prefix_8 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 8 175630319435822327 = some 175630319435822327 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 6 2 175630319435822327 175630319435822327 175630319435822327 endpoint_17_29_prefix_6 endpoint_17_29_window_6
private theorem endpoint_17_29_window_8 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 8 2 175630319435822327 = some 175630319435822327 := by decide +kernel
private theorem endpoint_17_29_prefix_10 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 10 175630319435822327 = some 175630319435822327 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 8 2 175630319435822327 175630319435822327 175630319435822327 endpoint_17_29_prefix_8 endpoint_17_29_window_8
private theorem endpoint_17_29_window_10 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 10 2 175630319435822327 = some 175630319435822327 := by decide +kernel
private theorem endpoint_17_29_prefix_12 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 12 175630319435822327 = some 175630319435822327 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 10 2 175630319435822327 175630319435822327 175630319435822327 endpoint_17_29_prefix_10 endpoint_17_29_window_10
private theorem endpoint_17_29_window_12 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 12 2 175630319435822327 = some 175630319435822327 := by decide +kernel
private theorem endpoint_17_29_prefix_14 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 14 175630319435822327 = some 175630319435822327 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 12 2 175630319435822327 175630319435822327 175630319435822327 endpoint_17_29_prefix_12 endpoint_17_29_window_12
private theorem endpoint_17_29_window_14 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 14 2 175630319435822327 = some 175630319435822327 := by decide +kernel
private theorem endpoint_17_29_prefix_16 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 16 175630319435822327 = some 175630319435822327 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 14 2 175630319435822327 175630319435822327 175630319435822327 endpoint_17_29_prefix_14 endpoint_17_29_window_14

def endpoint_17_29 : CertifiedEndpoint :=
  ⟨⟨17, 29, 3005⟩, 175630319435822327, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_29_flag endpoint_17_29_sources 16 175630319435822327 175630319435822327 rfl endpoint_17_29_base endpoint_17_29_prefix_16) (by decide)⟩
private def endpoint_17_30_flag : Flag := ⟨17, 30, 2973⟩
private def endpoint_17_30_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_30_base : receiptBase endpoint_17_30_flag endpoint_17_30_sources = some 178670670067935005 := by decide +kernel
private theorem endpoint_17_30_window_0 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 2 178670670067935005 = some 178670670067935005 := by decide +kernel
private theorem endpoint_17_30_window_2 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 2 2 178670670067935005 = some 178670670067935005 := by decide +kernel
private theorem endpoint_17_30_prefix_4 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 4 178670670067935005 = some 178670670067935005 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 2 2 178670670067935005 178670670067935005 178670670067935005 endpoint_17_30_window_0 endpoint_17_30_window_2
private theorem endpoint_17_30_window_4 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 4 2 178670670067935005 = some 178670670067935005 := by decide +kernel
private theorem endpoint_17_30_prefix_6 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 6 178670670067935005 = some 178670670067935005 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 4 2 178670670067935005 178670670067935005 178670670067935005 endpoint_17_30_prefix_4 endpoint_17_30_window_4
private theorem endpoint_17_30_window_6 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 6 2 178670670067935005 = some 178670670067935005 := by decide +kernel
private theorem endpoint_17_30_prefix_8 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 8 178670670067935005 = some 178670670067935005 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 6 2 178670670067935005 178670670067935005 178670670067935005 endpoint_17_30_prefix_6 endpoint_17_30_window_6
private theorem endpoint_17_30_window_8 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 8 2 178670670067935005 = some 178670670067935005 := by decide +kernel
private theorem endpoint_17_30_prefix_10 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 10 178670670067935005 = some 178670670067935005 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 8 2 178670670067935005 178670670067935005 178670670067935005 endpoint_17_30_prefix_8 endpoint_17_30_window_8
private theorem endpoint_17_30_window_10 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 10 2 178670670067935005 = some 178670670067935005 := by decide +kernel
private theorem endpoint_17_30_prefix_12 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 12 178670670067935005 = some 178670670067935005 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 10 2 178670670067935005 178670670067935005 178670670067935005 endpoint_17_30_prefix_10 endpoint_17_30_window_10
private theorem endpoint_17_30_window_12 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 12 2 178670670067935005 = some 178670670067935005 := by decide +kernel
private theorem endpoint_17_30_prefix_14 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 14 178670670067935005 = some 178670670067935005 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 12 2 178670670067935005 178670670067935005 178670670067935005 endpoint_17_30_prefix_12 endpoint_17_30_window_12
private theorem endpoint_17_30_window_14 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 14 2 178670670067935005 = some 178670670067935005 := by decide +kernel
private theorem endpoint_17_30_prefix_16 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 16 178670670067935005 = some 178670670067935005 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 14 2 178670670067935005 178670670067935005 178670670067935005 endpoint_17_30_prefix_14 endpoint_17_30_window_14

def endpoint_17_30 : CertifiedEndpoint :=
  ⟨⟨17, 30, 2973⟩, 178670670067935005, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_30_flag endpoint_17_30_sources 16 178670670067935005 178670670067935005 rfl endpoint_17_30_base endpoint_17_30_prefix_16) (by decide)⟩
private def endpoint_17_31_flag : Flag := ⟨17, 31, 2941⟩
private def endpoint_17_31_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_31_base : receiptBase endpoint_17_31_flag endpoint_17_31_sources = some 181606204234614118 := by decide +kernel
private theorem endpoint_17_31_window_0 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 2 181606204234614118 = some 181606204234614118 := by decide +kernel
private theorem endpoint_17_31_window_2 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 2 2 181606204234614118 = some 181606204234614118 := by decide +kernel
private theorem endpoint_17_31_prefix_4 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 4 181606204234614118 = some 181606204234614118 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 2 2 181606204234614118 181606204234614118 181606204234614118 endpoint_17_31_window_0 endpoint_17_31_window_2
private theorem endpoint_17_31_window_4 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 4 2 181606204234614118 = some 181606204234614118 := by decide +kernel
private theorem endpoint_17_31_prefix_6 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 6 181606204234614118 = some 181606204234614118 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 4 2 181606204234614118 181606204234614118 181606204234614118 endpoint_17_31_prefix_4 endpoint_17_31_window_4
private theorem endpoint_17_31_window_6 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 6 2 181606204234614118 = some 181606204234614118 := by decide +kernel
private theorem endpoint_17_31_prefix_8 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 8 181606204234614118 = some 181606204234614118 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 6 2 181606204234614118 181606204234614118 181606204234614118 endpoint_17_31_prefix_6 endpoint_17_31_window_6
private theorem endpoint_17_31_window_8 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 8 2 181606204234614118 = some 181606204234614118 := by decide +kernel
private theorem endpoint_17_31_prefix_10 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 10 181606204234614118 = some 181606204234614118 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 8 2 181606204234614118 181606204234614118 181606204234614118 endpoint_17_31_prefix_8 endpoint_17_31_window_8
private theorem endpoint_17_31_window_10 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 10 2 181606204234614118 = some 181606204234614118 := by decide +kernel
private theorem endpoint_17_31_prefix_12 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 12 181606204234614118 = some 181606204234614118 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 10 2 181606204234614118 181606204234614118 181606204234614118 endpoint_17_31_prefix_10 endpoint_17_31_window_10
private theorem endpoint_17_31_window_12 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 12 2 181606204234614118 = some 181606204234614118 := by decide +kernel
private theorem endpoint_17_31_prefix_14 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 14 181606204234614118 = some 181606204234614118 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 12 2 181606204234614118 181606204234614118 181606204234614118 endpoint_17_31_prefix_12 endpoint_17_31_window_12
private theorem endpoint_17_31_window_14 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 14 2 181606204234614118 = some 181606204234614118 := by decide +kernel
private theorem endpoint_17_31_prefix_16 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 16 181606204234614118 = some 181606204234614118 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 14 2 181606204234614118 181606204234614118 181606204234614118 endpoint_17_31_prefix_14 endpoint_17_31_window_14

def endpoint_17_31 : CertifiedEndpoint :=
  ⟨⟨17, 31, 2941⟩, 181606204234614118, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_31_flag endpoint_17_31_sources 16 181606204234614118 181606204234614118 rfl endpoint_17_31_base endpoint_17_31_prefix_16) (by decide)⟩
private def endpoint_17_32_flag : Flag := ⟨17, 32, 2907⟩
private def endpoint_17_32_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_32_base : receiptBase endpoint_17_32_flag endpoint_17_32_sources = some 184311683496758591 := by decide +kernel
private theorem endpoint_17_32_window_0 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 2 184311683496758591 = some 184311683496758591 := by decide +kernel
private theorem endpoint_17_32_window_2 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 2 2 184311683496758591 = some 184311683496758591 := by decide +kernel
private theorem endpoint_17_32_prefix_4 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 4 184311683496758591 = some 184311683496758591 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 2 2 184311683496758591 184311683496758591 184311683496758591 endpoint_17_32_window_0 endpoint_17_32_window_2
private theorem endpoint_17_32_window_4 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 4 2 184311683496758591 = some 184311683496758591 := by decide +kernel
private theorem endpoint_17_32_prefix_6 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 6 184311683496758591 = some 184311683496758591 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 4 2 184311683496758591 184311683496758591 184311683496758591 endpoint_17_32_prefix_4 endpoint_17_32_window_4
private theorem endpoint_17_32_window_6 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 6 2 184311683496758591 = some 184311683496758591 := by decide +kernel
private theorem endpoint_17_32_prefix_8 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 8 184311683496758591 = some 184311683496758591 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 6 2 184311683496758591 184311683496758591 184311683496758591 endpoint_17_32_prefix_6 endpoint_17_32_window_6
private theorem endpoint_17_32_window_8 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 8 2 184311683496758591 = some 184311683496758591 := by decide +kernel
private theorem endpoint_17_32_prefix_10 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 10 184311683496758591 = some 184311683496758591 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 8 2 184311683496758591 184311683496758591 184311683496758591 endpoint_17_32_prefix_8 endpoint_17_32_window_8
private theorem endpoint_17_32_window_10 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 10 2 184311683496758591 = some 184311683496758591 := by decide +kernel
private theorem endpoint_17_32_prefix_12 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 12 184311683496758591 = some 184311683496758591 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 10 2 184311683496758591 184311683496758591 184311683496758591 endpoint_17_32_prefix_10 endpoint_17_32_window_10
private theorem endpoint_17_32_window_12 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 12 2 184311683496758591 = some 184311683496758591 := by decide +kernel
private theorem endpoint_17_32_prefix_14 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 14 184311683496758591 = some 184311683496758591 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 12 2 184311683496758591 184311683496758591 184311683496758591 endpoint_17_32_prefix_12 endpoint_17_32_window_12
private theorem endpoint_17_32_window_14 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 14 2 184311683496758591 = some 184311683496758591 := by decide +kernel
private theorem endpoint_17_32_prefix_16 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 16 184311683496758591 = some 184311683496758591 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 14 2 184311683496758591 184311683496758591 184311683496758591 endpoint_17_32_prefix_14 endpoint_17_32_window_14

def endpoint_17_32 : CertifiedEndpoint :=
  ⟨⟨17, 32, 2907⟩, 184311683496758591, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_32_flag endpoint_17_32_sources 16 184311683496758591 184311683496758591 rfl endpoint_17_32_base endpoint_17_32_prefix_16) (by decide)⟩
private def endpoint_17_33_flag : Flag := ⟨17, 33, 2874⟩
private def endpoint_17_33_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_33_base : receiptBase endpoint_17_33_flag endpoint_17_33_sources = some 186970128162278550 := by decide +kernel
private theorem endpoint_17_33_window_0 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 2 186970128162278550 = some 186970128162278550 := by decide +kernel
private theorem endpoint_17_33_window_2 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 2 2 186970128162278550 = some 186970128162278550 := by decide +kernel
private theorem endpoint_17_33_prefix_4 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 4 186970128162278550 = some 186970128162278550 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 2 2 186970128162278550 186970128162278550 186970128162278550 endpoint_17_33_window_0 endpoint_17_33_window_2
private theorem endpoint_17_33_window_4 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 4 2 186970128162278550 = some 186970128162278550 := by decide +kernel
private theorem endpoint_17_33_prefix_6 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 6 186970128162278550 = some 186970128162278550 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 4 2 186970128162278550 186970128162278550 186970128162278550 endpoint_17_33_prefix_4 endpoint_17_33_window_4
private theorem endpoint_17_33_window_6 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 6 2 186970128162278550 = some 186970128162278550 := by decide +kernel
private theorem endpoint_17_33_prefix_8 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 8 186970128162278550 = some 186970128162278550 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 6 2 186970128162278550 186970128162278550 186970128162278550 endpoint_17_33_prefix_6 endpoint_17_33_window_6
private theorem endpoint_17_33_window_8 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 8 2 186970128162278550 = some 186970128162278550 := by decide +kernel
private theorem endpoint_17_33_prefix_10 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 10 186970128162278550 = some 186970128162278550 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 8 2 186970128162278550 186970128162278550 186970128162278550 endpoint_17_33_prefix_8 endpoint_17_33_window_8
private theorem endpoint_17_33_window_10 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 10 2 186970128162278550 = some 186970128162278550 := by decide +kernel
private theorem endpoint_17_33_prefix_12 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 12 186970128162278550 = some 186970128162278550 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 10 2 186970128162278550 186970128162278550 186970128162278550 endpoint_17_33_prefix_10 endpoint_17_33_window_10
private theorem endpoint_17_33_window_12 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 12 2 186970128162278550 = some 186970128162278550 := by decide +kernel
private theorem endpoint_17_33_prefix_14 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 14 186970128162278550 = some 186970128162278550 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 12 2 186970128162278550 186970128162278550 186970128162278550 endpoint_17_33_prefix_12 endpoint_17_33_window_12
private theorem endpoint_17_33_window_14 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 14 2 186970128162278550 = some 186970128162278550 := by decide +kernel
private theorem endpoint_17_33_prefix_16 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 16 186970128162278550 = some 186970128162278550 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 14 2 186970128162278550 186970128162278550 186970128162278550 endpoint_17_33_prefix_14 endpoint_17_33_window_14

def endpoint_17_33 : CertifiedEndpoint :=
  ⟨⟨17, 33, 2874⟩, 186970128162278550, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_33_flag endpoint_17_33_sources 16 186970128162278550 186970128162278550 rfl endpoint_17_33_base endpoint_17_33_prefix_16) (by decide)⟩
private def endpoint_17_34_flag : Flag := ⟨17, 34, 2839⟩
private def endpoint_17_34_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_17_34_base : receiptBase endpoint_17_34_flag endpoint_17_34_sources = some 188972220901145423 := by decide +kernel
private theorem endpoint_17_34_window_0 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 2 188972220901145423 = some 188972220901145423 := by decide +kernel
private theorem endpoint_17_34_window_2 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 2 2 188972220901145423 = some 188972220901145423 := by decide +kernel
private theorem endpoint_17_34_prefix_4 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 4 188972220901145423 = some 188972220901145423 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 2 2 188972220901145423 188972220901145423 188972220901145423 endpoint_17_34_window_0 endpoint_17_34_window_2
private theorem endpoint_17_34_window_4 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 4 2 188972220901145423 = some 188972220901145423 := by decide +kernel
private theorem endpoint_17_34_prefix_6 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 6 188972220901145423 = some 188972220901145423 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 4 2 188972220901145423 188972220901145423 188972220901145423 endpoint_17_34_prefix_4 endpoint_17_34_window_4
private theorem endpoint_17_34_window_6 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 6 2 188972220901145423 = some 188972220901145423 := by decide +kernel
private theorem endpoint_17_34_prefix_8 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 8 188972220901145423 = some 188972220901145423 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 6 2 188972220901145423 188972220901145423 188972220901145423 endpoint_17_34_prefix_6 endpoint_17_34_window_6
private theorem endpoint_17_34_window_8 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 8 2 188972220901145423 = some 188972220901145423 := by decide +kernel
private theorem endpoint_17_34_prefix_10 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 10 188972220901145423 = some 188972220901145423 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 8 2 188972220901145423 188972220901145423 188972220901145423 endpoint_17_34_prefix_8 endpoint_17_34_window_8
private theorem endpoint_17_34_window_10 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 10 2 188972220901145423 = some 188972220901145423 := by decide +kernel
private theorem endpoint_17_34_prefix_12 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 12 188972220901145423 = some 188972220901145423 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 10 2 188972220901145423 188972220901145423 188972220901145423 endpoint_17_34_prefix_10 endpoint_17_34_window_10
private theorem endpoint_17_34_window_12 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 12 2 188972220901145423 = some 188972220901145423 := by decide +kernel
private theorem endpoint_17_34_prefix_14 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 14 188972220901145423 = some 188972220901145423 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 12 2 188972220901145423 188972220901145423 188972220901145423 endpoint_17_34_prefix_12 endpoint_17_34_window_12
private theorem endpoint_17_34_window_14 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 14 2 188972220901145423 = some 188972220901145423 := by decide +kernel
private theorem endpoint_17_34_prefix_16 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 16 188972220901145423 = some 188972220901145423 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 14 2 188972220901145423 188972220901145423 188972220901145423 endpoint_17_34_prefix_14 endpoint_17_34_window_14

def endpoint_17_34 : CertifiedEndpoint :=
  ⟨⟨17, 34, 2839⟩, 188972220901145423, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_17_34_flag endpoint_17_34_sources 16 188972220901145423 188972220901145423 rfl endpoint_17_34_base endpoint_17_34_prefix_16) (by decide)⟩
private def endpoint_17_35_flag : Flag := ⟨17, 35, 2804⟩
private def endpoint_17_35_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_35_base : receiptBase endpoint_17_35_flag endpoint_17_35_sources = some 191693067114366705 := by decide +kernel
private theorem endpoint_17_35_window_0 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 2 191693067114366705 = some 191693067114366705 := by decide +kernel
private theorem endpoint_17_35_window_2 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 2 2 191693067114366705 = some 191693067114366705 := by decide +kernel
private theorem endpoint_17_35_prefix_4 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 4 191693067114366705 = some 191693067114366705 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 2 2 191693067114366705 191693067114366705 191693067114366705 endpoint_17_35_window_0 endpoint_17_35_window_2
private theorem endpoint_17_35_window_4 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 4 2 191693067114366705 = some 191693067114366705 := by decide +kernel
private theorem endpoint_17_35_prefix_6 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 6 191693067114366705 = some 191693067114366705 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 4 2 191693067114366705 191693067114366705 191693067114366705 endpoint_17_35_prefix_4 endpoint_17_35_window_4
private theorem endpoint_17_35_window_6 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 6 2 191693067114366705 = some 191693067114366705 := by decide +kernel
private theorem endpoint_17_35_prefix_8 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 8 191693067114366705 = some 191693067114366705 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 6 2 191693067114366705 191693067114366705 191693067114366705 endpoint_17_35_prefix_6 endpoint_17_35_window_6
private theorem endpoint_17_35_window_8 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 8 2 191693067114366705 = some 191693067114366705 := by decide +kernel
private theorem endpoint_17_35_prefix_10 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 10 191693067114366705 = some 191693067114366705 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 8 2 191693067114366705 191693067114366705 191693067114366705 endpoint_17_35_prefix_8 endpoint_17_35_window_8
private theorem endpoint_17_35_window_10 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 10 2 191693067114366705 = some 191693067114366705 := by decide +kernel
private theorem endpoint_17_35_prefix_12 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 12 191693067114366705 = some 191693067114366705 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 10 2 191693067114366705 191693067114366705 191693067114366705 endpoint_17_35_prefix_10 endpoint_17_35_window_10
private theorem endpoint_17_35_window_12 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 12 2 191693067114366705 = some 191693067114366705 := by decide +kernel
private theorem endpoint_17_35_prefix_14 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 14 191693067114366705 = some 191693067114366705 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 12 2 191693067114366705 191693067114366705 191693067114366705 endpoint_17_35_prefix_12 endpoint_17_35_window_12
private theorem endpoint_17_35_window_14 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 14 2 191693067114366705 = some 191693067114366705 := by decide +kernel
private theorem endpoint_17_35_prefix_16 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 16 191693067114366705 = some 191693067114366705 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 14 2 191693067114366705 191693067114366705 191693067114366705 endpoint_17_35_prefix_14 endpoint_17_35_window_14

def endpoint_17_35 : CertifiedEndpoint :=
  ⟨⟨17, 35, 2804⟩, 191693067114366705, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_35_flag endpoint_17_35_sources 16 191693067114366705 191693067114366705 rfl endpoint_17_35_base endpoint_17_35_prefix_16) (by decide)⟩
private def endpoint_17_36_flag : Flag := ⟨17, 36, 2769⟩
private def endpoint_17_36_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_36_base : receiptBase endpoint_17_36_flag endpoint_17_36_sources = some 193882799840035975 := by decide +kernel
private theorem endpoint_17_36_window_0 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 2 193882799840035975 = some 193882799840035975 := by decide +kernel
private theorem endpoint_17_36_window_2 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 2 2 193882799840035975 = some 193882799840035975 := by decide +kernel
private theorem endpoint_17_36_prefix_4 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 4 193882799840035975 = some 193882799840035975 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 2 2 193882799840035975 193882799840035975 193882799840035975 endpoint_17_36_window_0 endpoint_17_36_window_2
private theorem endpoint_17_36_window_4 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 4 2 193882799840035975 = some 193882799840035975 := by decide +kernel
private theorem endpoint_17_36_prefix_6 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 6 193882799840035975 = some 193882799840035975 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 4 2 193882799840035975 193882799840035975 193882799840035975 endpoint_17_36_prefix_4 endpoint_17_36_window_4
private theorem endpoint_17_36_window_6 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 6 2 193882799840035975 = some 193882799840035975 := by decide +kernel
private theorem endpoint_17_36_prefix_8 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 8 193882799840035975 = some 193882799840035975 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 6 2 193882799840035975 193882799840035975 193882799840035975 endpoint_17_36_prefix_6 endpoint_17_36_window_6
private theorem endpoint_17_36_window_8 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 8 2 193882799840035975 = some 193882799840035975 := by decide +kernel
private theorem endpoint_17_36_prefix_10 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 10 193882799840035975 = some 193882799840035975 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 8 2 193882799840035975 193882799840035975 193882799840035975 endpoint_17_36_prefix_8 endpoint_17_36_window_8
private theorem endpoint_17_36_window_10 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 10 2 193882799840035975 = some 193882799840035975 := by decide +kernel
private theorem endpoint_17_36_prefix_12 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 12 193882799840035975 = some 193882799840035975 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 10 2 193882799840035975 193882799840035975 193882799840035975 endpoint_17_36_prefix_10 endpoint_17_36_window_10
private theorem endpoint_17_36_window_12 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 12 2 193882799840035975 = some 193882799840035975 := by decide +kernel
private theorem endpoint_17_36_prefix_14 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 14 193882799840035975 = some 193882799840035975 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 12 2 193882799840035975 193882799840035975 193882799840035975 endpoint_17_36_prefix_12 endpoint_17_36_window_12
private theorem endpoint_17_36_window_14 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 14 2 193882799840035975 = some 193882799840035975 := by decide +kernel
private theorem endpoint_17_36_prefix_16 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 16 193882799840035975 = some 193882799840035975 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 14 2 193882799840035975 193882799840035975 193882799840035975 endpoint_17_36_prefix_14 endpoint_17_36_window_14

def endpoint_17_36 : CertifiedEndpoint :=
  ⟨⟨17, 36, 2769⟩, 193882799840035975, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_36_flag endpoint_17_36_sources 16 193882799840035975 193882799840035975 rfl endpoint_17_36_base endpoint_17_36_prefix_16) (by decide)⟩
private def endpoint_17_37_flag : Flag := ⟨17, 37, 2732⟩
private def endpoint_17_37_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_37_base : receiptBase endpoint_17_37_flag endpoint_17_37_sources = some 195816678457216012 := by decide +kernel
private theorem endpoint_17_37_window_0 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 2 195816678457216012 = some 195816678457216012 := by decide +kernel
private theorem endpoint_17_37_window_2 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 2 2 195816678457216012 = some 195816678457216012 := by decide +kernel
private theorem endpoint_17_37_prefix_4 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 4 195816678457216012 = some 195816678457216012 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 2 2 195816678457216012 195816678457216012 195816678457216012 endpoint_17_37_window_0 endpoint_17_37_window_2
private theorem endpoint_17_37_window_4 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 4 2 195816678457216012 = some 195816678457216012 := by decide +kernel
private theorem endpoint_17_37_prefix_6 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 6 195816678457216012 = some 195816678457216012 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 4 2 195816678457216012 195816678457216012 195816678457216012 endpoint_17_37_prefix_4 endpoint_17_37_window_4
private theorem endpoint_17_37_window_6 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 6 2 195816678457216012 = some 195816678457216012 := by decide +kernel
private theorem endpoint_17_37_prefix_8 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 8 195816678457216012 = some 195816678457216012 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 6 2 195816678457216012 195816678457216012 195816678457216012 endpoint_17_37_prefix_6 endpoint_17_37_window_6
private theorem endpoint_17_37_window_8 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 8 2 195816678457216012 = some 195816678457216012 := by decide +kernel
private theorem endpoint_17_37_prefix_10 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 10 195816678457216012 = some 195816678457216012 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 8 2 195816678457216012 195816678457216012 195816678457216012 endpoint_17_37_prefix_8 endpoint_17_37_window_8
private theorem endpoint_17_37_window_10 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 10 2 195816678457216012 = some 195816678457216012 := by decide +kernel
private theorem endpoint_17_37_prefix_12 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 12 195816678457216012 = some 195816678457216012 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 10 2 195816678457216012 195816678457216012 195816678457216012 endpoint_17_37_prefix_10 endpoint_17_37_window_10
private theorem endpoint_17_37_window_12 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 12 2 195816678457216012 = some 195816678457216012 := by decide +kernel
private theorem endpoint_17_37_prefix_14 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 14 195816678457216012 = some 195816678457216012 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 12 2 195816678457216012 195816678457216012 195816678457216012 endpoint_17_37_prefix_12 endpoint_17_37_window_12
private theorem endpoint_17_37_window_14 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 14 2 195816678457216012 = some 195816678457216012 := by decide +kernel
private theorem endpoint_17_37_prefix_16 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 16 195816678457216012 = some 195816678457216012 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 14 2 195816678457216012 195816678457216012 195816678457216012 endpoint_17_37_prefix_14 endpoint_17_37_window_14

def endpoint_17_37 : CertifiedEndpoint :=
  ⟨⟨17, 37, 2732⟩, 195816678457216012, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_37_flag endpoint_17_37_sources 16 195816678457216012 195816678457216012 rfl endpoint_17_37_base endpoint_17_37_prefix_16) (by decide)⟩
private def endpoint_17_38_flag : Flag := ⟨17, 38, 2695⟩
private def endpoint_17_38_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_38_base : receiptBase endpoint_17_38_flag endpoint_17_38_sources = some 197629616106490862 := by decide +kernel
private theorem endpoint_17_38_window_0 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 2 197629616106490862 = some 197629616106490862 := by decide +kernel
private theorem endpoint_17_38_window_2 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 2 2 197629616106490862 = some 197629616106490862 := by decide +kernel
private theorem endpoint_17_38_prefix_4 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 4 197629616106490862 = some 197629616106490862 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 2 2 197629616106490862 197629616106490862 197629616106490862 endpoint_17_38_window_0 endpoint_17_38_window_2
private theorem endpoint_17_38_window_4 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 4 2 197629616106490862 = some 197629616106490862 := by decide +kernel
private theorem endpoint_17_38_prefix_6 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 6 197629616106490862 = some 197629616106490862 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 4 2 197629616106490862 197629616106490862 197629616106490862 endpoint_17_38_prefix_4 endpoint_17_38_window_4
private theorem endpoint_17_38_window_6 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 6 2 197629616106490862 = some 197629616106490862 := by decide +kernel
private theorem endpoint_17_38_prefix_8 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 8 197629616106490862 = some 197629616106490862 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 6 2 197629616106490862 197629616106490862 197629616106490862 endpoint_17_38_prefix_6 endpoint_17_38_window_6
private theorem endpoint_17_38_window_8 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 8 2 197629616106490862 = some 197629616106490862 := by decide +kernel
private theorem endpoint_17_38_prefix_10 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 10 197629616106490862 = some 197629616106490862 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 8 2 197629616106490862 197629616106490862 197629616106490862 endpoint_17_38_prefix_8 endpoint_17_38_window_8
private theorem endpoint_17_38_window_10 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 10 2 197629616106490862 = some 197629616106490862 := by decide +kernel
private theorem endpoint_17_38_prefix_12 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 12 197629616106490862 = some 197629616106490862 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 10 2 197629616106490862 197629616106490862 197629616106490862 endpoint_17_38_prefix_10 endpoint_17_38_window_10
private theorem endpoint_17_38_window_12 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 12 2 197629616106490862 = some 197629616106490862 := by decide +kernel
private theorem endpoint_17_38_prefix_14 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 14 197629616106490862 = some 197629616106490862 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 12 2 197629616106490862 197629616106490862 197629616106490862 endpoint_17_38_prefix_12 endpoint_17_38_window_12
private theorem endpoint_17_38_window_14 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 14 2 197629616106490862 = some 197629616106490862 := by decide +kernel
private theorem endpoint_17_38_prefix_16 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 16 197629616106490862 = some 197629616106490862 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 14 2 197629616106490862 197629616106490862 197629616106490862 endpoint_17_38_prefix_14 endpoint_17_38_window_14

def endpoint_17_38 : CertifiedEndpoint :=
  ⟨⟨17, 38, 2695⟩, 197629616106490862, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_38_flag endpoint_17_38_sources 16 197629616106490862 197629616106490862 rfl endpoint_17_38_base endpoint_17_38_prefix_16) (by decide)⟩
private def endpoint_17_39_flag : Flag := ⟨17, 39, 2658⟩
private def endpoint_17_39_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_39_base : receiptBase endpoint_17_39_flag endpoint_17_39_sources = some 199321612787860526 := by decide +kernel
private theorem endpoint_17_39_window_0 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 2 199321612787860526 = some 199321612787860526 := by decide +kernel
private theorem endpoint_17_39_window_2 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 2 2 199321612787860526 = some 199321612787860526 := by decide +kernel
private theorem endpoint_17_39_prefix_4 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 4 199321612787860526 = some 199321612787860526 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 2 2 199321612787860526 199321612787860526 199321612787860526 endpoint_17_39_window_0 endpoint_17_39_window_2
private theorem endpoint_17_39_window_4 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 4 2 199321612787860526 = some 199321612787860526 := by decide +kernel
private theorem endpoint_17_39_prefix_6 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 6 199321612787860526 = some 199321612787860526 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 4 2 199321612787860526 199321612787860526 199321612787860526 endpoint_17_39_prefix_4 endpoint_17_39_window_4
private theorem endpoint_17_39_window_6 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 6 2 199321612787860526 = some 199321612787860526 := by decide +kernel
private theorem endpoint_17_39_prefix_8 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 8 199321612787860526 = some 199321612787860526 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 6 2 199321612787860526 199321612787860526 199321612787860526 endpoint_17_39_prefix_6 endpoint_17_39_window_6
private theorem endpoint_17_39_window_8 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 8 2 199321612787860526 = some 199321612787860526 := by decide +kernel
private theorem endpoint_17_39_prefix_10 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 10 199321612787860526 = some 199321612787860526 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 8 2 199321612787860526 199321612787860526 199321612787860526 endpoint_17_39_prefix_8 endpoint_17_39_window_8
private theorem endpoint_17_39_window_10 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 10 2 199321612787860526 = some 199321612787860526 := by decide +kernel
private theorem endpoint_17_39_prefix_12 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 12 199321612787860526 = some 199321612787860526 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 10 2 199321612787860526 199321612787860526 199321612787860526 endpoint_17_39_prefix_10 endpoint_17_39_window_10
private theorem endpoint_17_39_window_12 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 12 2 199321612787860526 = some 199321612787860526 := by decide +kernel
private theorem endpoint_17_39_prefix_14 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 14 199321612787860526 = some 199321612787860526 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 12 2 199321612787860526 199321612787860526 199321612787860526 endpoint_17_39_prefix_12 endpoint_17_39_window_12
private theorem endpoint_17_39_window_14 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 14 2 199321612787860526 = some 199321612787860526 := by decide +kernel
private theorem endpoint_17_39_prefix_16 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 16 199321612787860526 = some 199321612787860526 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 14 2 199321612787860526 199321612787860526 199321612787860526 endpoint_17_39_prefix_14 endpoint_17_39_window_14

def endpoint_17_39 : CertifiedEndpoint :=
  ⟨⟨17, 39, 2658⟩, 199321612787860526, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_39_flag endpoint_17_39_sources 16 199321612787860526 199321612787860526 rfl endpoint_17_39_base endpoint_17_39_prefix_16) (by decide)⟩
private def endpoint_17_40_flag : Flag := ⟨17, 40, 2619⟩
private def endpoint_17_40_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_40_base : receiptBase endpoint_17_40_flag endpoint_17_40_sources = some 200741630858269335 := by decide +kernel
private theorem endpoint_17_40_window_0 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 2 200741630858269335 = some 200741630858269335 := by decide +kernel
private theorem endpoint_17_40_window_2 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 2 2 200741630858269335 = some 200741630858269335 := by decide +kernel
private theorem endpoint_17_40_prefix_4 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 4 200741630858269335 = some 200741630858269335 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 2 2 200741630858269335 200741630858269335 200741630858269335 endpoint_17_40_window_0 endpoint_17_40_window_2
private theorem endpoint_17_40_window_4 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 4 2 200741630858269335 = some 200741630858269335 := by decide +kernel
private theorem endpoint_17_40_prefix_6 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 6 200741630858269335 = some 200741630858269335 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 4 2 200741630858269335 200741630858269335 200741630858269335 endpoint_17_40_prefix_4 endpoint_17_40_window_4
private theorem endpoint_17_40_window_6 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 6 2 200741630858269335 = some 200741630858269335 := by decide +kernel
private theorem endpoint_17_40_prefix_8 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 8 200741630858269335 = some 200741630858269335 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 6 2 200741630858269335 200741630858269335 200741630858269335 endpoint_17_40_prefix_6 endpoint_17_40_window_6
private theorem endpoint_17_40_window_8 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 8 2 200741630858269335 = some 200741630858269335 := by decide +kernel
private theorem endpoint_17_40_prefix_10 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 10 200741630858269335 = some 200741630858269335 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 8 2 200741630858269335 200741630858269335 200741630858269335 endpoint_17_40_prefix_8 endpoint_17_40_window_8
private theorem endpoint_17_40_window_10 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 10 2 200741630858269335 = some 200741630858269335 := by decide +kernel
private theorem endpoint_17_40_prefix_12 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 12 200741630858269335 = some 200741630858269335 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 10 2 200741630858269335 200741630858269335 200741630858269335 endpoint_17_40_prefix_10 endpoint_17_40_window_10
private theorem endpoint_17_40_window_12 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 12 2 200741630858269335 = some 200741630858269335 := by decide +kernel
private theorem endpoint_17_40_prefix_14 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 14 200741630858269335 = some 200741630858269335 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 12 2 200741630858269335 200741630858269335 200741630858269335 endpoint_17_40_prefix_12 endpoint_17_40_window_12
private theorem endpoint_17_40_window_14 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 14 2 200741630858269335 = some 200741630858269335 := by decide +kernel
private theorem endpoint_17_40_prefix_16 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 16 200741630858269335 = some 200741630858269335 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 14 2 200741630858269335 200741630858269335 200741630858269335 endpoint_17_40_prefix_14 endpoint_17_40_window_14

def endpoint_17_40 : CertifiedEndpoint :=
  ⟨⟨17, 40, 2619⟩, 200741630858269335, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_40_flag endpoint_17_40_sources 16 200741630858269335 200741630858269335 rfl endpoint_17_40_base endpoint_17_40_prefix_16) (by decide)⟩
private def endpoint_17_41_flag : Flag := ⟨17, 41, 2580⟩
private def endpoint_17_41_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_41_base : receiptBase endpoint_17_41_flag endpoint_17_41_sources = some 202641262458016430 := by decide +kernel
private theorem endpoint_17_41_window_0 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 2 202641262458016430 = some 202641262458016430 := by decide +kernel
private theorem endpoint_17_41_window_2 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 2 2 202641262458016430 = some 202641262458016430 := by decide +kernel
private theorem endpoint_17_41_prefix_4 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 4 202641262458016430 = some 202641262458016430 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 2 2 202641262458016430 202641262458016430 202641262458016430 endpoint_17_41_window_0 endpoint_17_41_window_2
private theorem endpoint_17_41_window_4 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 4 2 202641262458016430 = some 202641262458016430 := by decide +kernel
private theorem endpoint_17_41_prefix_6 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 6 202641262458016430 = some 202641262458016430 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 4 2 202641262458016430 202641262458016430 202641262458016430 endpoint_17_41_prefix_4 endpoint_17_41_window_4
private theorem endpoint_17_41_window_6 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 6 2 202641262458016430 = some 202641262458016430 := by decide +kernel
private theorem endpoint_17_41_prefix_8 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 8 202641262458016430 = some 202641262458016430 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 6 2 202641262458016430 202641262458016430 202641262458016430 endpoint_17_41_prefix_6 endpoint_17_41_window_6
private theorem endpoint_17_41_window_8 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 8 2 202641262458016430 = some 202641262458016430 := by decide +kernel
private theorem endpoint_17_41_prefix_10 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 10 202641262458016430 = some 202641262458016430 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 8 2 202641262458016430 202641262458016430 202641262458016430 endpoint_17_41_prefix_8 endpoint_17_41_window_8
private theorem endpoint_17_41_window_10 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 10 2 202641262458016430 = some 202641262458016430 := by decide +kernel
private theorem endpoint_17_41_prefix_12 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 12 202641262458016430 = some 202641262458016430 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 10 2 202641262458016430 202641262458016430 202641262458016430 endpoint_17_41_prefix_10 endpoint_17_41_window_10
private theorem endpoint_17_41_window_12 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 12 2 202641262458016430 = some 202641262458016430 := by decide +kernel
private theorem endpoint_17_41_prefix_14 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 14 202641262458016430 = some 202641262458016430 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 12 2 202641262458016430 202641262458016430 202641262458016430 endpoint_17_41_prefix_12 endpoint_17_41_window_12
private theorem endpoint_17_41_window_14 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 14 2 202641262458016430 = some 202641262458016430 := by decide +kernel
private theorem endpoint_17_41_prefix_16 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 16 202641262458016430 = some 202641262458016430 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 14 2 202641262458016430 202641262458016430 202641262458016430 endpoint_17_41_prefix_14 endpoint_17_41_window_14

def endpoint_17_41 : CertifiedEndpoint :=
  ⟨⟨17, 41, 2580⟩, 202641262458016430, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_41_flag endpoint_17_41_sources 16 202641262458016430 202641262458016430 rfl endpoint_17_41_base endpoint_17_41_prefix_16) (by decide)⟩
private def endpoint_17_42_flag : Flag := ⟨17, 42, 2540⟩
private def endpoint_17_42_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_42_base : receiptBase endpoint_17_42_flag endpoint_17_42_sources = some 203715582480996619 := by decide +kernel
private theorem endpoint_17_42_window_0 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 2 203715582480996619 = some 203715582480996619 := by decide +kernel
private theorem endpoint_17_42_window_2 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 2 2 203715582480996619 = some 203715582480996619 := by decide +kernel
private theorem endpoint_17_42_prefix_4 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 4 203715582480996619 = some 203715582480996619 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 2 2 203715582480996619 203715582480996619 203715582480996619 endpoint_17_42_window_0 endpoint_17_42_window_2
private theorem endpoint_17_42_window_4 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 4 2 203715582480996619 = some 203715582480996619 := by decide +kernel
private theorem endpoint_17_42_prefix_6 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 6 203715582480996619 = some 203715582480996619 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 4 2 203715582480996619 203715582480996619 203715582480996619 endpoint_17_42_prefix_4 endpoint_17_42_window_4
private theorem endpoint_17_42_window_6 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 6 2 203715582480996619 = some 203715582480996619 := by decide +kernel
private theorem endpoint_17_42_prefix_8 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 8 203715582480996619 = some 203715582480996619 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 6 2 203715582480996619 203715582480996619 203715582480996619 endpoint_17_42_prefix_6 endpoint_17_42_window_6
private theorem endpoint_17_42_window_8 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 8 2 203715582480996619 = some 203715582480996619 := by decide +kernel
private theorem endpoint_17_42_prefix_10 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 10 203715582480996619 = some 203715582480996619 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 8 2 203715582480996619 203715582480996619 203715582480996619 endpoint_17_42_prefix_8 endpoint_17_42_window_8
private theorem endpoint_17_42_window_10 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 10 2 203715582480996619 = some 203715582480996619 := by decide +kernel
private theorem endpoint_17_42_prefix_12 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 12 203715582480996619 = some 203715582480996619 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 10 2 203715582480996619 203715582480996619 203715582480996619 endpoint_17_42_prefix_10 endpoint_17_42_window_10
private theorem endpoint_17_42_window_12 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 12 2 203715582480996619 = some 203715582480996619 := by decide +kernel
private theorem endpoint_17_42_prefix_14 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 14 203715582480996619 = some 203715582480996619 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 12 2 203715582480996619 203715582480996619 203715582480996619 endpoint_17_42_prefix_12 endpoint_17_42_window_12
private theorem endpoint_17_42_window_14 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 14 2 203715582480996619 = some 203715582480996619 := by decide +kernel
private theorem endpoint_17_42_prefix_16 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 16 203715582480996619 = some 203715582480996619 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 14 2 203715582480996619 203715582480996619 203715582480996619 endpoint_17_42_prefix_14 endpoint_17_42_window_14

def endpoint_17_42 : CertifiedEndpoint :=
  ⟨⟨17, 42, 2540⟩, 203715582480996619, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_42_flag endpoint_17_42_sources 16 203715582480996619 203715582480996619 rfl endpoint_17_42_base endpoint_17_42_prefix_16) (by decide)⟩
private def endpoint_17_43_flag : Flag := ⟨17, 43, 2499⟩
private def endpoint_17_43_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_43_base : receiptBase endpoint_17_43_flag endpoint_17_43_sources = some 204578501557765526 := by decide +kernel
private theorem endpoint_17_43_window_0 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 2 204578501557765526 = some 207573086464529322 := by decide +kernel
private theorem endpoint_17_43_window_2 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 2 2 207573086464529322 = some 207573086464529322 := by decide +kernel
private theorem endpoint_17_43_prefix_4 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 4 204578501557765526 = some 207573086464529322 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 2 2 204578501557765526 207573086464529322 207573086464529322 endpoint_17_43_window_0 endpoint_17_43_window_2
private theorem endpoint_17_43_window_4 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 4 2 207573086464529322 = some 207573086464529322 := by decide +kernel
private theorem endpoint_17_43_prefix_6 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 6 204578501557765526 = some 207573086464529322 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 4 2 204578501557765526 207573086464529322 207573086464529322 endpoint_17_43_prefix_4 endpoint_17_43_window_4
private theorem endpoint_17_43_window_6 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 6 2 207573086464529322 = some 207573086464529322 := by decide +kernel
private theorem endpoint_17_43_prefix_8 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 8 204578501557765526 = some 207573086464529322 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 6 2 204578501557765526 207573086464529322 207573086464529322 endpoint_17_43_prefix_6 endpoint_17_43_window_6
private theorem endpoint_17_43_window_8 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 8 2 207573086464529322 = some 207573086464529322 := by decide +kernel
private theorem endpoint_17_43_prefix_10 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 10 204578501557765526 = some 207573086464529322 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 8 2 204578501557765526 207573086464529322 207573086464529322 endpoint_17_43_prefix_8 endpoint_17_43_window_8
private theorem endpoint_17_43_window_10 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 10 2 207573086464529322 = some 207573086464529322 := by decide +kernel
private theorem endpoint_17_43_prefix_12 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 12 204578501557765526 = some 207573086464529322 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 10 2 204578501557765526 207573086464529322 207573086464529322 endpoint_17_43_prefix_10 endpoint_17_43_window_10
private theorem endpoint_17_43_window_12 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 12 2 207573086464529322 = some 207573086464529322 := by decide +kernel
private theorem endpoint_17_43_prefix_14 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 14 204578501557765526 = some 207573086464529322 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 12 2 204578501557765526 207573086464529322 207573086464529322 endpoint_17_43_prefix_12 endpoint_17_43_window_12
private theorem endpoint_17_43_window_14 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 14 2 207573086464529322 = some 207573086464529322 := by decide +kernel
private theorem endpoint_17_43_prefix_16 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 16 204578501557765526 = some 207573086464529322 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 14 2 204578501557765526 207573086464529322 207573086464529322 endpoint_17_43_prefix_14 endpoint_17_43_window_14

def endpoint_17_43 : CertifiedEndpoint :=
  ⟨⟨17, 43, 2499⟩, 207573086464529322, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_43_flag endpoint_17_43_sources 16 204578501557765526 207573086464529322 rfl endpoint_17_43_base endpoint_17_43_prefix_16) (by decide)⟩
private def endpoint_17_44_flag : Flag := ⟨17, 44, 2458⟩
private def endpoint_17_44_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_44_base : receiptBase endpoint_17_44_flag endpoint_17_44_sources = some 205307436742456721 := by decide +kernel
private theorem endpoint_17_44_window_0 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 2 205307436742456721 = some 211853547757613880 := by decide +kernel
private theorem endpoint_17_44_window_2 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 2 2 211853547757613880 = some 211853547757613880 := by decide +kernel
private theorem endpoint_17_44_prefix_4 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 4 205307436742456721 = some 211853547757613880 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 2 2 205307436742456721 211853547757613880 211853547757613880 endpoint_17_44_window_0 endpoint_17_44_window_2
private theorem endpoint_17_44_window_4 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 4 2 211853547757613880 = some 211853547757613880 := by decide +kernel
private theorem endpoint_17_44_prefix_6 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 6 205307436742456721 = some 211853547757613880 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 4 2 205307436742456721 211853547757613880 211853547757613880 endpoint_17_44_prefix_4 endpoint_17_44_window_4
private theorem endpoint_17_44_window_6 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 6 2 211853547757613880 = some 211853547757613880 := by decide +kernel
private theorem endpoint_17_44_prefix_8 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 8 205307436742456721 = some 211853547757613880 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 6 2 205307436742456721 211853547757613880 211853547757613880 endpoint_17_44_prefix_6 endpoint_17_44_window_6
private theorem endpoint_17_44_window_8 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 8 2 211853547757613880 = some 211853547757613880 := by decide +kernel
private theorem endpoint_17_44_prefix_10 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 10 205307436742456721 = some 211853547757613880 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 8 2 205307436742456721 211853547757613880 211853547757613880 endpoint_17_44_prefix_8 endpoint_17_44_window_8
private theorem endpoint_17_44_window_10 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 10 2 211853547757613880 = some 211853547757613880 := by decide +kernel
private theorem endpoint_17_44_prefix_12 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 12 205307436742456721 = some 211853547757613880 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 10 2 205307436742456721 211853547757613880 211853547757613880 endpoint_17_44_prefix_10 endpoint_17_44_window_10
private theorem endpoint_17_44_window_12 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 12 2 211853547757613880 = some 211853547757613880 := by decide +kernel
private theorem endpoint_17_44_prefix_14 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 14 205307436742456721 = some 211853547757613880 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 12 2 205307436742456721 211853547757613880 211853547757613880 endpoint_17_44_prefix_12 endpoint_17_44_window_12
private theorem endpoint_17_44_window_14 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 14 2 211853547757613880 = some 211853547757613880 := by decide +kernel
private theorem endpoint_17_44_prefix_16 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 16 205307436742456721 = some 211853547757613880 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 14 2 205307436742456721 211853547757613880 211853547757613880 endpoint_17_44_prefix_14 endpoint_17_44_window_14

def endpoint_17_44 : CertifiedEndpoint :=
  ⟨⟨17, 44, 2458⟩, 211853547757613880, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_44_flag endpoint_17_44_sources 16 205307436742456721 211853547757613880 rfl endpoint_17_44_base endpoint_17_44_prefix_16) (by decide)⟩
private def endpoint_17_45_flag : Flag := ⟨17, 45, 2415⟩
private def endpoint_17_45_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_45_base : receiptBase endpoint_17_45_flag endpoint_17_45_sources = some 205734639816723289 := by decide +kernel
private theorem endpoint_17_45_window_0 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 2 205734639816723289 = some 215929529076193996 := by decide +kernel
private theorem endpoint_17_45_window_2 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 2 2 215929529076193996 = some 215929529076193996 := by decide +kernel
private theorem endpoint_17_45_prefix_4 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 4 205734639816723289 = some 215929529076193996 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 2 2 205734639816723289 215929529076193996 215929529076193996 endpoint_17_45_window_0 endpoint_17_45_window_2
private theorem endpoint_17_45_window_4 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 4 2 215929529076193996 = some 215929529076193996 := by decide +kernel
private theorem endpoint_17_45_prefix_6 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 6 205734639816723289 = some 215929529076193996 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 4 2 205734639816723289 215929529076193996 215929529076193996 endpoint_17_45_prefix_4 endpoint_17_45_window_4
private theorem endpoint_17_45_window_6 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 6 2 215929529076193996 = some 215929529076193996 := by decide +kernel
private theorem endpoint_17_45_prefix_8 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 8 205734639816723289 = some 215929529076193996 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 6 2 205734639816723289 215929529076193996 215929529076193996 endpoint_17_45_prefix_6 endpoint_17_45_window_6
private theorem endpoint_17_45_window_8 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 8 2 215929529076193996 = some 215929529076193996 := by decide +kernel
private theorem endpoint_17_45_prefix_10 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 10 205734639816723289 = some 215929529076193996 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 8 2 205734639816723289 215929529076193996 215929529076193996 endpoint_17_45_prefix_8 endpoint_17_45_window_8
private theorem endpoint_17_45_window_10 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 10 2 215929529076193996 = some 215929529076193996 := by decide +kernel
private theorem endpoint_17_45_prefix_12 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 12 205734639816723289 = some 215929529076193996 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 10 2 205734639816723289 215929529076193996 215929529076193996 endpoint_17_45_prefix_10 endpoint_17_45_window_10
private theorem endpoint_17_45_window_12 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 12 2 215929529076193996 = some 215929529076193996 := by decide +kernel
private theorem endpoint_17_45_prefix_14 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 14 205734639816723289 = some 215929529076193996 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 12 2 205734639816723289 215929529076193996 215929529076193996 endpoint_17_45_prefix_12 endpoint_17_45_window_12
private theorem endpoint_17_45_window_14 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 14 2 215929529076193996 = some 215929529076193996 := by decide +kernel
private theorem endpoint_17_45_prefix_16 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 16 205734639816723289 = some 215929529076193996 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 14 2 205734639816723289 215929529076193996 215929529076193996 endpoint_17_45_prefix_14 endpoint_17_45_window_14

def endpoint_17_45 : CertifiedEndpoint :=
  ⟨⟨17, 45, 2415⟩, 215929529076193996, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_45_flag endpoint_17_45_sources 16 205734639816723289 215929529076193996 rfl endpoint_17_45_base endpoint_17_45_prefix_16) (by decide)⟩
private def endpoint_17_46_flag : Flag := ⟨17, 46, 2372⟩
private def endpoint_17_46_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_46_base : receiptBase endpoint_17_46_flag endpoint_17_46_sources = some 206021401943872254 := by decide +kernel
private theorem endpoint_17_46_window_0 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 2 206021401943872254 = some 219888478191435416 := by decide +kernel
private theorem endpoint_17_46_window_2 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 2 2 219888478191435416 = some 219888478191435416 := by decide +kernel
private theorem endpoint_17_46_prefix_4 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 4 206021401943872254 = some 219888478191435416 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 2 2 206021401943872254 219888478191435416 219888478191435416 endpoint_17_46_window_0 endpoint_17_46_window_2
private theorem endpoint_17_46_window_4 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 4 2 219888478191435416 = some 219888478191435416 := by decide +kernel
private theorem endpoint_17_46_prefix_6 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 6 206021401943872254 = some 219888478191435416 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 4 2 206021401943872254 219888478191435416 219888478191435416 endpoint_17_46_prefix_4 endpoint_17_46_window_4
private theorem endpoint_17_46_window_6 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 6 2 219888478191435416 = some 219888478191435416 := by decide +kernel
private theorem endpoint_17_46_prefix_8 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 8 206021401943872254 = some 219888478191435416 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 6 2 206021401943872254 219888478191435416 219888478191435416 endpoint_17_46_prefix_6 endpoint_17_46_window_6
private theorem endpoint_17_46_window_8 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 8 2 219888478191435416 = some 219888478191435416 := by decide +kernel
private theorem endpoint_17_46_prefix_10 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 10 206021401943872254 = some 219888478191435416 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 8 2 206021401943872254 219888478191435416 219888478191435416 endpoint_17_46_prefix_8 endpoint_17_46_window_8
private theorem endpoint_17_46_window_10 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 10 2 219888478191435416 = some 219888478191435416 := by decide +kernel
private theorem endpoint_17_46_prefix_12 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 12 206021401943872254 = some 219888478191435416 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 10 2 206021401943872254 219888478191435416 219888478191435416 endpoint_17_46_prefix_10 endpoint_17_46_window_10
private theorem endpoint_17_46_window_12 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 12 2 219888478191435416 = some 219888478191435416 := by decide +kernel
private theorem endpoint_17_46_prefix_14 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 14 206021401943872254 = some 219888478191435416 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 12 2 206021401943872254 219888478191435416 219888478191435416 endpoint_17_46_prefix_12 endpoint_17_46_window_12
private theorem endpoint_17_46_window_14 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 14 2 219888478191435416 = some 219888478191435416 := by decide +kernel
private theorem endpoint_17_46_prefix_16 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 16 206021401943872254 = some 219888478191435416 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 14 2 206021401943872254 219888478191435416 219888478191435416 endpoint_17_46_prefix_14 endpoint_17_46_window_14

def endpoint_17_46 : CertifiedEndpoint :=
  ⟨⟨17, 46, 2372⟩, 219888478191435416, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_46_flag endpoint_17_46_sources 16 206021401943872254 219888478191435416 rfl endpoint_17_46_base endpoint_17_46_prefix_16) (by decide)⟩
private def endpoint_17_47_flag : Flag := ⟨17, 47, 2327⟩
private def endpoint_17_47_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_47_base : receiptBase endpoint_17_47_flag endpoint_17_47_sources = some 205993517850516812 := by decide +kernel
private theorem endpoint_17_47_window_0 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 2 205993517850516812 = some 223632432988513362 := by decide +kernel
private theorem endpoint_17_47_window_2 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 2 2 223632432988513362 = some 223632432988513362 := by decide +kernel
private theorem endpoint_17_47_prefix_4 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 4 205993517850516812 = some 223632432988513362 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 2 2 205993517850516812 223632432988513362 223632432988513362 endpoint_17_47_window_0 endpoint_17_47_window_2
private theorem endpoint_17_47_window_4 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 4 2 223632432988513362 = some 223632432988513362 := by decide +kernel
private theorem endpoint_17_47_prefix_6 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 6 205993517850516812 = some 223632432988513362 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 4 2 205993517850516812 223632432988513362 223632432988513362 endpoint_17_47_prefix_4 endpoint_17_47_window_4
private theorem endpoint_17_47_window_6 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 6 2 223632432988513362 = some 223632432988513362 := by decide +kernel
private theorem endpoint_17_47_prefix_8 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 8 205993517850516812 = some 223632432988513362 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 6 2 205993517850516812 223632432988513362 223632432988513362 endpoint_17_47_prefix_6 endpoint_17_47_window_6
private theorem endpoint_17_47_window_8 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 8 2 223632432988513362 = some 223632432988513362 := by decide +kernel
private theorem endpoint_17_47_prefix_10 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 10 205993517850516812 = some 223632432988513362 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 8 2 205993517850516812 223632432988513362 223632432988513362 endpoint_17_47_prefix_8 endpoint_17_47_window_8
private theorem endpoint_17_47_window_10 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 10 2 223632432988513362 = some 223632432988513362 := by decide +kernel
private theorem endpoint_17_47_prefix_12 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 12 205993517850516812 = some 223632432988513362 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 10 2 205993517850516812 223632432988513362 223632432988513362 endpoint_17_47_prefix_10 endpoint_17_47_window_10
private theorem endpoint_17_47_window_12 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 12 2 223632432988513362 = some 223632432988513362 := by decide +kernel
private theorem endpoint_17_47_prefix_14 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 14 205993517850516812 = some 223632432988513362 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 12 2 205993517850516812 223632432988513362 223632432988513362 endpoint_17_47_prefix_12 endpoint_17_47_window_12
private theorem endpoint_17_47_window_14 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 14 2 223632432988513362 = some 223632432988513362 := by decide +kernel
private theorem endpoint_17_47_prefix_16 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 16 205993517850516812 = some 223632432988513362 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 14 2 205993517850516812 223632432988513362 223632432988513362 endpoint_17_47_prefix_14 endpoint_17_47_window_14

def endpoint_17_47 : CertifiedEndpoint :=
  ⟨⟨17, 47, 2327⟩, 223632432988513362, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_47_flag endpoint_17_47_sources 16 205993517850516812 223632432988513362 rfl endpoint_17_47_base endpoint_17_47_prefix_16) (by decide)⟩
private def endpoint_17_48_flag : Flag := ⟨17, 48, 2282⟩
private def endpoint_17_48_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_48_base : receiptBase endpoint_17_48_flag endpoint_17_48_sources = some 205818735755003877 := by decide +kernel
private theorem endpoint_17_48_window_0 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 2 205818735755003877 = some 227254098410423096 := by decide +kernel
private theorem endpoint_17_48_window_2 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 2 2 227254098410423096 = some 227254098410423096 := by decide +kernel
private theorem endpoint_17_48_prefix_4 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 4 205818735755003877 = some 227254098410423096 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 2 2 205818735755003877 227254098410423096 227254098410423096 endpoint_17_48_window_0 endpoint_17_48_window_2
private theorem endpoint_17_48_window_4 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 4 2 227254098410423096 = some 227254098410423096 := by decide +kernel
private theorem endpoint_17_48_prefix_6 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 6 205818735755003877 = some 227254098410423096 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 4 2 205818735755003877 227254098410423096 227254098410423096 endpoint_17_48_prefix_4 endpoint_17_48_window_4
private theorem endpoint_17_48_window_6 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 6 2 227254098410423096 = some 227254098410423096 := by decide +kernel
private theorem endpoint_17_48_prefix_8 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 8 205818735755003877 = some 227254098410423096 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 6 2 205818735755003877 227254098410423096 227254098410423096 endpoint_17_48_prefix_6 endpoint_17_48_window_6
private theorem endpoint_17_48_window_8 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 8 2 227254098410423096 = some 227254098410423096 := by decide +kernel
private theorem endpoint_17_48_prefix_10 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 10 205818735755003877 = some 227254098410423096 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 8 2 205818735755003877 227254098410423096 227254098410423096 endpoint_17_48_prefix_8 endpoint_17_48_window_8
private theorem endpoint_17_48_window_10 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 10 2 227254098410423096 = some 227254098410423096 := by decide +kernel
private theorem endpoint_17_48_prefix_12 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 12 205818735755003877 = some 227254098410423096 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 10 2 205818735755003877 227254098410423096 227254098410423096 endpoint_17_48_prefix_10 endpoint_17_48_window_10
private theorem endpoint_17_48_window_12 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 12 2 227254098410423096 = some 227254098410423096 := by decide +kernel
private theorem endpoint_17_48_prefix_14 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 14 205818735755003877 = some 227254098410423096 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 12 2 205818735755003877 227254098410423096 227254098410423096 endpoint_17_48_prefix_12 endpoint_17_48_window_12
private theorem endpoint_17_48_window_14 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 14 2 227254098410423096 = some 227254098410423096 := by decide +kernel
private theorem endpoint_17_48_prefix_16 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 16 205818735755003877 = some 227254098410423096 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 14 2 205818735755003877 227254098410423096 227254098410423096 endpoint_17_48_prefix_14 endpoint_17_48_window_14

def endpoint_17_48 : CertifiedEndpoint :=
  ⟨⟨17, 48, 2282⟩, 227254098410423096, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_48_flag endpoint_17_48_sources 16 205818735755003877 227254098410423096 rfl endpoint_17_48_base endpoint_17_48_prefix_16) (by decide)⟩
private def endpoint_17_49_flag : Flag := ⟨17, 49, 2236⟩
private def endpoint_17_49_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_17_49_base : receiptBase endpoint_17_49_flag endpoint_17_49_sources = some 210684523800329952 := by decide +kernel
private theorem endpoint_17_49_window_0 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 2 210684523800329952 = some 223008458564606167 := by decide +kernel
private theorem endpoint_17_49_window_2 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 2 2 223008458564606167 = some 223008458564606167 := by decide +kernel
private theorem endpoint_17_49_prefix_4 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 4 210684523800329952 = some 223008458564606167 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 2 2 210684523800329952 223008458564606167 223008458564606167 endpoint_17_49_window_0 endpoint_17_49_window_2
private theorem endpoint_17_49_window_4 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 4 2 223008458564606167 = some 223008458564606167 := by decide +kernel
private theorem endpoint_17_49_prefix_6 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 6 210684523800329952 = some 223008458564606167 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 4 2 210684523800329952 223008458564606167 223008458564606167 endpoint_17_49_prefix_4 endpoint_17_49_window_4
private theorem endpoint_17_49_window_6 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 6 2 223008458564606167 = some 223008458564606167 := by decide +kernel
private theorem endpoint_17_49_prefix_8 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 8 210684523800329952 = some 223008458564606167 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 6 2 210684523800329952 223008458564606167 223008458564606167 endpoint_17_49_prefix_6 endpoint_17_49_window_6
private theorem endpoint_17_49_window_8 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 8 2 223008458564606167 = some 223008458564606167 := by decide +kernel
private theorem endpoint_17_49_prefix_10 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 10 210684523800329952 = some 223008458564606167 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 8 2 210684523800329952 223008458564606167 223008458564606167 endpoint_17_49_prefix_8 endpoint_17_49_window_8
private theorem endpoint_17_49_window_10 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 10 2 223008458564606167 = some 223008458564606167 := by decide +kernel
private theorem endpoint_17_49_prefix_12 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 12 210684523800329952 = some 223008458564606167 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 10 2 210684523800329952 223008458564606167 223008458564606167 endpoint_17_49_prefix_10 endpoint_17_49_window_10
private theorem endpoint_17_49_window_12 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 12 2 223008458564606167 = some 223008458564606167 := by decide +kernel
private theorem endpoint_17_49_prefix_14 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 14 210684523800329952 = some 223008458564606167 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 12 2 210684523800329952 223008458564606167 223008458564606167 endpoint_17_49_prefix_12 endpoint_17_49_window_12
private theorem endpoint_17_49_window_14 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 14 2 223008458564606167 = some 223008458564606167 := by decide +kernel
private theorem endpoint_17_49_prefix_16 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 16 210684523800329952 = some 223008458564606167 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 14 2 210684523800329952 223008458564606167 223008458564606167 endpoint_17_49_prefix_14 endpoint_17_49_window_14

def endpoint_17_49 : CertifiedEndpoint :=
  ⟨⟨17, 49, 2236⟩, 223008458564606167, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_17_49_flag endpoint_17_49_sources 16 210684523800329952 223008458564606167 rfl endpoint_17_49_base endpoint_17_49_prefix_16) (by decide)⟩

def endpointBlock11 : List CertifiedEndpoint := [
  endpoint_16_40, endpoint_16_41, endpoint_16_42, endpoint_16_43, endpoint_16_44, endpoint_16_45,
  endpoint_16_46, endpoint_16_47, endpoint_16_48, endpoint_16_49, endpoint_16_50, endpoint_16_51,
  endpoint_16_52, endpoint_16_53, endpoint_16_54, endpoint_16_55, endpoint_16_56, endpoint_16_57,
  endpoint_16_58, endpoint_16_59, endpoint_16_60, endpoint_16_61, endpoint_16_62, endpoint_16_63,
  endpoint_16_64, endpoint_16_65, endpoint_16_66, endpoint_16_67, endpoint_16_68, endpoint_16_69,
  endpoint_16_70, endpoint_16_71, endpoint_16_72, endpoint_16_73, endpoint_16_74, endpoint_16_75,
  endpoint_16_76, endpoint_16_77, endpoint_16_78, endpoint_16_79, endpoint_16_80, endpoint_16_81,
  endpoint_16_82, endpoint_17_17, endpoint_17_18, endpoint_17_19, endpoint_17_20, endpoint_17_21,
  endpoint_17_22, endpoint_17_23, endpoint_17_24, endpoint_17_25, endpoint_17_26, endpoint_17_27,
  endpoint_17_28, endpoint_17_29, endpoint_17_30, endpoint_17_31, endpoint_17_32, endpoint_17_33,
  endpoint_17_34, endpoint_17_35, endpoint_17_36, endpoint_17_37, endpoint_17_38, endpoint_17_39,
  endpoint_17_40, endpoint_17_41, endpoint_17_42, endpoint_17_43, endpoint_17_44, endpoint_17_45,
  endpoint_17_46, endpoint_17_47, endpoint_17_48, endpoint_17_49
]

end ProximityPrize.SubmissionLower.Koala6844Receipts
