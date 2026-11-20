import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


private def endpoint_15_32_flag : Flag := ⟨15, 32, 3283⟩
private def endpoint_15_32_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_32_base : receiptBase endpoint_15_32_flag endpoint_15_32_sources = some 187490305279143417 := by decide +kernel
private theorem endpoint_15_32_window_0 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 2 187490305279143417 = some 187490305279143417 := by decide +kernel
private theorem endpoint_15_32_window_2 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 2 2 187490305279143417 = some 187490305279143417 := by decide +kernel
private theorem endpoint_15_32_prefix_4 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 4 187490305279143417 = some 187490305279143417 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 2 2 187490305279143417 187490305279143417 187490305279143417 endpoint_15_32_window_0 endpoint_15_32_window_2
private theorem endpoint_15_32_window_4 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 4 2 187490305279143417 = some 187490305279143417 := by decide +kernel
private theorem endpoint_15_32_prefix_6 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 6 187490305279143417 = some 187490305279143417 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 4 2 187490305279143417 187490305279143417 187490305279143417 endpoint_15_32_prefix_4 endpoint_15_32_window_4
private theorem endpoint_15_32_window_6 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 6 2 187490305279143417 = some 187490305279143417 := by decide +kernel
private theorem endpoint_15_32_prefix_8 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 8 187490305279143417 = some 187490305279143417 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 6 2 187490305279143417 187490305279143417 187490305279143417 endpoint_15_32_prefix_6 endpoint_15_32_window_6
private theorem endpoint_15_32_window_8 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 8 2 187490305279143417 = some 187490305279143417 := by decide +kernel
private theorem endpoint_15_32_prefix_10 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 10 187490305279143417 = some 187490305279143417 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 8 2 187490305279143417 187490305279143417 187490305279143417 endpoint_15_32_prefix_8 endpoint_15_32_window_8
private theorem endpoint_15_32_window_10 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 10 2 187490305279143417 = some 187490305279143417 := by decide +kernel
private theorem endpoint_15_32_prefix_12 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 12 187490305279143417 = some 187490305279143417 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 10 2 187490305279143417 187490305279143417 187490305279143417 endpoint_15_32_prefix_10 endpoint_15_32_window_10
private theorem endpoint_15_32_window_12 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 12 2 187490305279143417 = some 187490305279143417 := by decide +kernel
private theorem endpoint_15_32_prefix_14 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 14 187490305279143417 = some 187490305279143417 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 12 2 187490305279143417 187490305279143417 187490305279143417 endpoint_15_32_prefix_12 endpoint_15_32_window_12

def endpoint_15_32 : CertifiedEndpoint :=
  ⟨⟨15, 32, 3283⟩, 187490305279143417, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_32_flag endpoint_15_32_sources 14 187490305279143417 187490305279143417 rfl endpoint_15_32_base endpoint_15_32_prefix_14) (by decide)⟩
private def endpoint_15_33_flag : Flag := ⟨15, 33, 3255⟩
private def endpoint_15_33_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_33_base : receiptBase endpoint_15_33_flag endpoint_15_33_sources = some 190756290554655260 := by decide +kernel
private theorem endpoint_15_33_window_0 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 2 190756290554655260 = some 190756290554655260 := by decide +kernel
private theorem endpoint_15_33_window_2 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 2 2 190756290554655260 = some 190756290554655260 := by decide +kernel
private theorem endpoint_15_33_prefix_4 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 4 190756290554655260 = some 190756290554655260 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 2 2 190756290554655260 190756290554655260 190756290554655260 endpoint_15_33_window_0 endpoint_15_33_window_2
private theorem endpoint_15_33_window_4 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 4 2 190756290554655260 = some 190756290554655260 := by decide +kernel
private theorem endpoint_15_33_prefix_6 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 6 190756290554655260 = some 190756290554655260 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 4 2 190756290554655260 190756290554655260 190756290554655260 endpoint_15_33_prefix_4 endpoint_15_33_window_4
private theorem endpoint_15_33_window_6 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 6 2 190756290554655260 = some 190756290554655260 := by decide +kernel
private theorem endpoint_15_33_prefix_8 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 8 190756290554655260 = some 190756290554655260 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 6 2 190756290554655260 190756290554655260 190756290554655260 endpoint_15_33_prefix_6 endpoint_15_33_window_6
private theorem endpoint_15_33_window_8 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 8 2 190756290554655260 = some 190756290554655260 := by decide +kernel
private theorem endpoint_15_33_prefix_10 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 10 190756290554655260 = some 190756290554655260 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 8 2 190756290554655260 190756290554655260 190756290554655260 endpoint_15_33_prefix_8 endpoint_15_33_window_8
private theorem endpoint_15_33_window_10 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 10 2 190756290554655260 = some 190756290554655260 := by decide +kernel
private theorem endpoint_15_33_prefix_12 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 12 190756290554655260 = some 190756290554655260 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 10 2 190756290554655260 190756290554655260 190756290554655260 endpoint_15_33_prefix_10 endpoint_15_33_window_10
private theorem endpoint_15_33_window_12 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 12 2 190756290554655260 = some 190756290554655260 := by decide +kernel
private theorem endpoint_15_33_prefix_14 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 14 190756290554655260 = some 190756290554655260 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 12 2 190756290554655260 190756290554655260 190756290554655260 endpoint_15_33_prefix_12 endpoint_15_33_window_12

def endpoint_15_33 : CertifiedEndpoint :=
  ⟨⟨15, 33, 3255⟩, 190756290554655260, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_33_flag endpoint_15_33_sources 14 190756290554655260 190756290554655260 rfl endpoint_15_33_base endpoint_15_33_prefix_14) (by decide)⟩
private def endpoint_15_34_flag : Flag := ⟨15, 34, 3226⟩
private def endpoint_15_34_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_15_34_base : receiptBase endpoint_15_34_flag endpoint_15_34_sources = some 193850252679590850 := by decide +kernel
private theorem endpoint_15_34_window_0 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 2 193850252679590850 = some 193850252679590850 := by decide +kernel
private theorem endpoint_15_34_window_2 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 2 2 193850252679590850 = some 193850252679590850 := by decide +kernel
private theorem endpoint_15_34_prefix_4 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 4 193850252679590850 = some 193850252679590850 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 2 2 193850252679590850 193850252679590850 193850252679590850 endpoint_15_34_window_0 endpoint_15_34_window_2
private theorem endpoint_15_34_window_4 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 4 2 193850252679590850 = some 193850252679590850 := by decide +kernel
private theorem endpoint_15_34_prefix_6 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 6 193850252679590850 = some 193850252679590850 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 4 2 193850252679590850 193850252679590850 193850252679590850 endpoint_15_34_prefix_4 endpoint_15_34_window_4
private theorem endpoint_15_34_window_6 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 6 2 193850252679590850 = some 193850252679590850 := by decide +kernel
private theorem endpoint_15_34_prefix_8 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 8 193850252679590850 = some 193850252679590850 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 6 2 193850252679590850 193850252679590850 193850252679590850 endpoint_15_34_prefix_6 endpoint_15_34_window_6
private theorem endpoint_15_34_window_8 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 8 2 193850252679590850 = some 193850252679590850 := by decide +kernel
private theorem endpoint_15_34_prefix_10 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 10 193850252679590850 = some 193850252679590850 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 8 2 193850252679590850 193850252679590850 193850252679590850 endpoint_15_34_prefix_8 endpoint_15_34_window_8
private theorem endpoint_15_34_window_10 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 10 2 193850252679590850 = some 193850252679590850 := by decide +kernel
private theorem endpoint_15_34_prefix_12 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 12 193850252679590850 = some 193850252679590850 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 10 2 193850252679590850 193850252679590850 193850252679590850 endpoint_15_34_prefix_10 endpoint_15_34_window_10
private theorem endpoint_15_34_window_12 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 12 2 193850252679590850 = some 193850252679590850 := by decide +kernel
private theorem endpoint_15_34_prefix_14 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 14 193850252679590850 = some 193850252679590850 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 12 2 193850252679590850 193850252679590850 193850252679590850 endpoint_15_34_prefix_12 endpoint_15_34_window_12

def endpoint_15_34 : CertifiedEndpoint :=
  ⟨⟨15, 34, 3226⟩, 193850252679590850, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_15_34_flag endpoint_15_34_sources 14 193850252679590850 193850252679590850 rfl endpoint_15_34_base endpoint_15_34_prefix_14) (by decide)⟩
private def endpoint_15_35_flag : Flag := ⟨15, 35, 3197⟩
private def endpoint_15_35_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_15_35_base : receiptBase endpoint_15_35_flag endpoint_15_35_sources = some 196827960138874101 := by decide +kernel
private theorem endpoint_15_35_window_0 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 2 196827960138874101 = some 196827960138874101 := by decide +kernel
private theorem endpoint_15_35_window_2 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 2 2 196827960138874101 = some 196827960138874101 := by decide +kernel
private theorem endpoint_15_35_prefix_4 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 4 196827960138874101 = some 196827960138874101 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 2 2 196827960138874101 196827960138874101 196827960138874101 endpoint_15_35_window_0 endpoint_15_35_window_2
private theorem endpoint_15_35_window_4 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 4 2 196827960138874101 = some 196827960138874101 := by decide +kernel
private theorem endpoint_15_35_prefix_6 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 6 196827960138874101 = some 196827960138874101 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 4 2 196827960138874101 196827960138874101 196827960138874101 endpoint_15_35_prefix_4 endpoint_15_35_window_4
private theorem endpoint_15_35_window_6 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 6 2 196827960138874101 = some 196827960138874101 := by decide +kernel
private theorem endpoint_15_35_prefix_8 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 8 196827960138874101 = some 196827960138874101 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 6 2 196827960138874101 196827960138874101 196827960138874101 endpoint_15_35_prefix_6 endpoint_15_35_window_6
private theorem endpoint_15_35_window_8 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 8 2 196827960138874101 = some 196827960138874101 := by decide +kernel
private theorem endpoint_15_35_prefix_10 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 10 196827960138874101 = some 196827960138874101 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 8 2 196827960138874101 196827960138874101 196827960138874101 endpoint_15_35_prefix_8 endpoint_15_35_window_8
private theorem endpoint_15_35_window_10 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 10 2 196827960138874101 = some 196827960138874101 := by decide +kernel
private theorem endpoint_15_35_prefix_12 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 12 196827960138874101 = some 196827960138874101 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 10 2 196827960138874101 196827960138874101 196827960138874101 endpoint_15_35_prefix_10 endpoint_15_35_window_10
private theorem endpoint_15_35_window_12 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 12 2 196827960138874101 = some 196827960138874101 := by decide +kernel
private theorem endpoint_15_35_prefix_14 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 14 196827960138874101 = some 196827960138874101 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 12 2 196827960138874101 196827960138874101 196827960138874101 endpoint_15_35_prefix_12 endpoint_15_35_window_12

def endpoint_15_35 : CertifiedEndpoint :=
  ⟨⟨15, 35, 3197⟩, 196827960138874101, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_15_35_flag endpoint_15_35_sources 14 196827960138874101 196827960138874101 rfl endpoint_15_35_base endpoint_15_35_prefix_14) (by decide)⟩
private def endpoint_15_36_flag : Flag := ⟨15, 36, 3167⟩
private def endpoint_15_36_sources : Sources := ⟨contact23, contact03, contact25⟩
private theorem endpoint_15_36_base : receiptBase endpoint_15_36_flag endpoint_15_36_sources = some 200947839413684371 := by decide +kernel
private theorem endpoint_15_36_window_0 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 2 200947839413684371 = some 200947839413684371 := by decide +kernel
private theorem endpoint_15_36_window_2 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 2 2 200947839413684371 = some 200947839413684371 := by decide +kernel
private theorem endpoint_15_36_prefix_4 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 4 200947839413684371 = some 200947839413684371 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 2 2 200947839413684371 200947839413684371 200947839413684371 endpoint_15_36_window_0 endpoint_15_36_window_2
private theorem endpoint_15_36_window_4 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 4 2 200947839413684371 = some 200947839413684371 := by decide +kernel
private theorem endpoint_15_36_prefix_6 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 6 200947839413684371 = some 200947839413684371 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 4 2 200947839413684371 200947839413684371 200947839413684371 endpoint_15_36_prefix_4 endpoint_15_36_window_4
private theorem endpoint_15_36_window_6 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 6 2 200947839413684371 = some 200947839413684371 := by decide +kernel
private theorem endpoint_15_36_prefix_8 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 8 200947839413684371 = some 200947839413684371 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 6 2 200947839413684371 200947839413684371 200947839413684371 endpoint_15_36_prefix_6 endpoint_15_36_window_6
private theorem endpoint_15_36_window_8 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 8 2 200947839413684371 = some 200947839413684371 := by decide +kernel
private theorem endpoint_15_36_prefix_10 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 10 200947839413684371 = some 200947839413684371 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 8 2 200947839413684371 200947839413684371 200947839413684371 endpoint_15_36_prefix_8 endpoint_15_36_window_8
private theorem endpoint_15_36_window_10 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 10 2 200947839413684371 = some 200947839413684371 := by decide +kernel
private theorem endpoint_15_36_prefix_12 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 12 200947839413684371 = some 200947839413684371 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 10 2 200947839413684371 200947839413684371 200947839413684371 endpoint_15_36_prefix_10 endpoint_15_36_window_10
private theorem endpoint_15_36_window_12 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 12 2 200947839413684371 = some 200947839413684371 := by decide +kernel
private theorem endpoint_15_36_prefix_14 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 14 200947839413684371 = some 200947839413684371 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 12 2 200947839413684371 200947839413684371 200947839413684371 endpoint_15_36_prefix_12 endpoint_15_36_window_12

def endpoint_15_36 : CertifiedEndpoint :=
  ⟨⟨15, 36, 3167⟩, 200947839413684371, .terminal ⟨contact23, contact03, contact25⟩ (finish_receipt_window endpoint_15_36_flag endpoint_15_36_sources 14 200947839413684371 200947839413684371 rfl endpoint_15_36_base endpoint_15_36_prefix_14) (by decide)⟩
private def endpoint_15_37_flag : Flag := ⟨15, 37, 3137⟩
private def endpoint_15_37_sources : Sources := ⟨contact23, contact03, contact25⟩
private theorem endpoint_15_37_base : receiptBase endpoint_15_37_flag endpoint_15_37_sources = some 203687178421622506 := by decide +kernel
private theorem endpoint_15_37_window_0 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 2 203687178421622506 = some 203687178421622506 := by decide +kernel
private theorem endpoint_15_37_window_2 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 2 2 203687178421622506 = some 203687178421622506 := by decide +kernel
private theorem endpoint_15_37_prefix_4 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 4 203687178421622506 = some 203687178421622506 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 2 2 203687178421622506 203687178421622506 203687178421622506 endpoint_15_37_window_0 endpoint_15_37_window_2
private theorem endpoint_15_37_window_4 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 4 2 203687178421622506 = some 203687178421622506 := by decide +kernel
private theorem endpoint_15_37_prefix_6 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 6 203687178421622506 = some 203687178421622506 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 4 2 203687178421622506 203687178421622506 203687178421622506 endpoint_15_37_prefix_4 endpoint_15_37_window_4
private theorem endpoint_15_37_window_6 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 6 2 203687178421622506 = some 203687178421622506 := by decide +kernel
private theorem endpoint_15_37_prefix_8 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 8 203687178421622506 = some 203687178421622506 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 6 2 203687178421622506 203687178421622506 203687178421622506 endpoint_15_37_prefix_6 endpoint_15_37_window_6
private theorem endpoint_15_37_window_8 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 8 2 203687178421622506 = some 203687178421622506 := by decide +kernel
private theorem endpoint_15_37_prefix_10 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 10 203687178421622506 = some 203687178421622506 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 8 2 203687178421622506 203687178421622506 203687178421622506 endpoint_15_37_prefix_8 endpoint_15_37_window_8
private theorem endpoint_15_37_window_10 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 10 2 203687178421622506 = some 203687178421622506 := by decide +kernel
private theorem endpoint_15_37_prefix_12 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 12 203687178421622506 = some 203687178421622506 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 10 2 203687178421622506 203687178421622506 203687178421622506 endpoint_15_37_prefix_10 endpoint_15_37_window_10
private theorem endpoint_15_37_window_12 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 12 2 203687178421622506 = some 203687178421622506 := by decide +kernel
private theorem endpoint_15_37_prefix_14 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 14 203687178421622506 = some 203687178421622506 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 12 2 203687178421622506 203687178421622506 203687178421622506 endpoint_15_37_prefix_12 endpoint_15_37_window_12

def endpoint_15_37 : CertifiedEndpoint :=
  ⟨⟨15, 37, 3137⟩, 203687178421622506, .terminal ⟨contact23, contact03, contact25⟩ (finish_receipt_window endpoint_15_37_flag endpoint_15_37_sources 14 203687178421622506 203687178421622506 rfl endpoint_15_37_base endpoint_15_37_prefix_14) (by decide)⟩
private def endpoint_15_38_flag : Flag := ⟨15, 38, 3106⟩
private def endpoint_15_38_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_38_base : receiptBase endpoint_15_38_flag endpoint_15_38_sources = some 207717161152657597 := by decide +kernel
private theorem endpoint_15_38_window_0 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 2 207717161152657597 = some 207717161152657597 := by decide +kernel
private theorem endpoint_15_38_window_2 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 2 2 207717161152657597 = some 207717161152657597 := by decide +kernel
private theorem endpoint_15_38_prefix_4 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 4 207717161152657597 = some 207717161152657597 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 2 2 207717161152657597 207717161152657597 207717161152657597 endpoint_15_38_window_0 endpoint_15_38_window_2
private theorem endpoint_15_38_window_4 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 4 2 207717161152657597 = some 207717161152657597 := by decide +kernel
private theorem endpoint_15_38_prefix_6 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 6 207717161152657597 = some 207717161152657597 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 4 2 207717161152657597 207717161152657597 207717161152657597 endpoint_15_38_prefix_4 endpoint_15_38_window_4
private theorem endpoint_15_38_window_6 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 6 2 207717161152657597 = some 207717161152657597 := by decide +kernel
private theorem endpoint_15_38_prefix_8 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 8 207717161152657597 = some 207717161152657597 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 6 2 207717161152657597 207717161152657597 207717161152657597 endpoint_15_38_prefix_6 endpoint_15_38_window_6
private theorem endpoint_15_38_window_8 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 8 2 207717161152657597 = some 207717161152657597 := by decide +kernel
private theorem endpoint_15_38_prefix_10 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 10 207717161152657597 = some 207717161152657597 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 8 2 207717161152657597 207717161152657597 207717161152657597 endpoint_15_38_prefix_8 endpoint_15_38_window_8
private theorem endpoint_15_38_window_10 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 10 2 207717161152657597 = some 207717161152657597 := by decide +kernel
private theorem endpoint_15_38_prefix_12 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 12 207717161152657597 = some 207717161152657597 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 10 2 207717161152657597 207717161152657597 207717161152657597 endpoint_15_38_prefix_10 endpoint_15_38_window_10
private theorem endpoint_15_38_window_12 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 12 2 207717161152657597 = some 207717161152657597 := by decide +kernel
private theorem endpoint_15_38_prefix_14 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 14 207717161152657597 = some 207717161152657597 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 12 2 207717161152657597 207717161152657597 207717161152657597 endpoint_15_38_prefix_12 endpoint_15_38_window_12

def endpoint_15_38 : CertifiedEndpoint :=
  ⟨⟨15, 38, 3106⟩, 207717161152657597, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_38_flag endpoint_15_38_sources 14 207717161152657597 207717161152657597 rfl endpoint_15_38_base endpoint_15_38_prefix_14) (by decide)⟩
private def endpoint_15_39_flag : Flag := ⟨15, 39, 3074⟩
private def endpoint_15_39_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_39_base : receiptBase endpoint_15_39_flag endpoint_15_39_sources = some 210092630739612695 := by decide +kernel
private theorem endpoint_15_39_window_0 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 2 210092630739612695 = some 210092630739612695 := by decide +kernel
private theorem endpoint_15_39_window_2 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 2 2 210092630739612695 = some 210092630739612695 := by decide +kernel
private theorem endpoint_15_39_prefix_4 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 4 210092630739612695 = some 210092630739612695 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 2 2 210092630739612695 210092630739612695 210092630739612695 endpoint_15_39_window_0 endpoint_15_39_window_2
private theorem endpoint_15_39_window_4 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 4 2 210092630739612695 = some 210092630739612695 := by decide +kernel
private theorem endpoint_15_39_prefix_6 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 6 210092630739612695 = some 210092630739612695 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 4 2 210092630739612695 210092630739612695 210092630739612695 endpoint_15_39_prefix_4 endpoint_15_39_window_4
private theorem endpoint_15_39_window_6 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 6 2 210092630739612695 = some 210092630739612695 := by decide +kernel
private theorem endpoint_15_39_prefix_8 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 8 210092630739612695 = some 210092630739612695 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 6 2 210092630739612695 210092630739612695 210092630739612695 endpoint_15_39_prefix_6 endpoint_15_39_window_6
private theorem endpoint_15_39_window_8 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 8 2 210092630739612695 = some 210092630739612695 := by decide +kernel
private theorem endpoint_15_39_prefix_10 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 10 210092630739612695 = some 210092630739612695 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 8 2 210092630739612695 210092630739612695 210092630739612695 endpoint_15_39_prefix_8 endpoint_15_39_window_8
private theorem endpoint_15_39_window_10 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 10 2 210092630739612695 = some 210092630739612695 := by decide +kernel
private theorem endpoint_15_39_prefix_12 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 12 210092630739612695 = some 210092630739612695 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 10 2 210092630739612695 210092630739612695 210092630739612695 endpoint_15_39_prefix_10 endpoint_15_39_window_10
private theorem endpoint_15_39_window_12 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 12 2 210092630739612695 = some 210092630739612695 := by decide +kernel
private theorem endpoint_15_39_prefix_14 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 14 210092630739612695 = some 210092630739612695 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 12 2 210092630739612695 210092630739612695 210092630739612695 endpoint_15_39_prefix_12 endpoint_15_39_window_12

def endpoint_15_39 : CertifiedEndpoint :=
  ⟨⟨15, 39, 3074⟩, 210092630739612695, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_39_flag endpoint_15_39_sources 14 210092630739612695 210092630739612695 rfl endpoint_15_39_base endpoint_15_39_prefix_14) (by decide)⟩
private def endpoint_15_40_flag : Flag := ⟨15, 40, 3042⟩
private def endpoint_15_40_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_40_base : receiptBase endpoint_15_40_flag endpoint_15_40_sources = some 212375031889921815 := by decide +kernel
private theorem endpoint_15_40_window_0 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 2 212375031889921815 = some 212375031889921815 := by decide +kernel
private theorem endpoint_15_40_window_2 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 2 2 212375031889921815 = some 212375031889921815 := by decide +kernel
private theorem endpoint_15_40_prefix_4 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 4 212375031889921815 = some 212375031889921815 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 2 2 212375031889921815 212375031889921815 212375031889921815 endpoint_15_40_window_0 endpoint_15_40_window_2
private theorem endpoint_15_40_window_4 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 4 2 212375031889921815 = some 212375031889921815 := by decide +kernel
private theorem endpoint_15_40_prefix_6 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 6 212375031889921815 = some 212375031889921815 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 4 2 212375031889921815 212375031889921815 212375031889921815 endpoint_15_40_prefix_4 endpoint_15_40_window_4
private theorem endpoint_15_40_window_6 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 6 2 212375031889921815 = some 212375031889921815 := by decide +kernel
private theorem endpoint_15_40_prefix_8 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 8 212375031889921815 = some 212375031889921815 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 6 2 212375031889921815 212375031889921815 212375031889921815 endpoint_15_40_prefix_6 endpoint_15_40_window_6
private theorem endpoint_15_40_window_8 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 8 2 212375031889921815 = some 212375031889921815 := by decide +kernel
private theorem endpoint_15_40_prefix_10 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 10 212375031889921815 = some 212375031889921815 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 8 2 212375031889921815 212375031889921815 212375031889921815 endpoint_15_40_prefix_8 endpoint_15_40_window_8
private theorem endpoint_15_40_window_10 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 10 2 212375031889921815 = some 212375031889921815 := by decide +kernel
private theorem endpoint_15_40_prefix_12 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 12 212375031889921815 = some 212375031889921815 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 10 2 212375031889921815 212375031889921815 212375031889921815 endpoint_15_40_prefix_10 endpoint_15_40_window_10
private theorem endpoint_15_40_window_12 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 12 2 212375031889921815 = some 212375031889921815 := by decide +kernel
private theorem endpoint_15_40_prefix_14 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 14 212375031889921815 = some 212375031889921815 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 12 2 212375031889921815 212375031889921815 212375031889921815 endpoint_15_40_prefix_12 endpoint_15_40_window_12

def endpoint_15_40 : CertifiedEndpoint :=
  ⟨⟨15, 40, 3042⟩, 212375031889921815, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_40_flag endpoint_15_40_sources 14 212375031889921815 212375031889921815 rfl endpoint_15_40_base endpoint_15_40_prefix_14) (by decide)⟩
private def endpoint_15_41_flag : Flag := ⟨15, 41, 3009⟩
private def endpoint_15_41_sources : Sources := ⟨contact27, contact03, contact25⟩
private theorem endpoint_15_41_base : receiptBase endpoint_15_41_flag endpoint_15_41_sources = some 213559043327070041 := by decide +kernel
private theorem endpoint_15_41_window_0 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 2 213559043327070041 = some 216630732064840348 := by decide +kernel
private theorem endpoint_15_41_window_2 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 2 2 216630732064840348 = some 216630732064840348 := by decide +kernel
private theorem endpoint_15_41_prefix_4 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 4 213559043327070041 = some 216630732064840348 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 2 2 213559043327070041 216630732064840348 216630732064840348 endpoint_15_41_window_0 endpoint_15_41_window_2
private theorem endpoint_15_41_window_4 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 4 2 216630732064840348 = some 216630732064840348 := by decide +kernel
private theorem endpoint_15_41_prefix_6 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 6 213559043327070041 = some 216630732064840348 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 4 2 213559043327070041 216630732064840348 216630732064840348 endpoint_15_41_prefix_4 endpoint_15_41_window_4
private theorem endpoint_15_41_window_6 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 6 2 216630732064840348 = some 216630732064840348 := by decide +kernel
private theorem endpoint_15_41_prefix_8 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 8 213559043327070041 = some 216630732064840348 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 6 2 213559043327070041 216630732064840348 216630732064840348 endpoint_15_41_prefix_6 endpoint_15_41_window_6
private theorem endpoint_15_41_window_8 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 8 2 216630732064840348 = some 216630732064840348 := by decide +kernel
private theorem endpoint_15_41_prefix_10 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 10 213559043327070041 = some 216630732064840348 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 8 2 213559043327070041 216630732064840348 216630732064840348 endpoint_15_41_prefix_8 endpoint_15_41_window_8
private theorem endpoint_15_41_window_10 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 10 2 216630732064840348 = some 216630732064840348 := by decide +kernel
private theorem endpoint_15_41_prefix_12 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 12 213559043327070041 = some 216630732064840348 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 10 2 213559043327070041 216630732064840348 216630732064840348 endpoint_15_41_prefix_10 endpoint_15_41_window_10
private theorem endpoint_15_41_window_12 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 12 2 216630732064840348 = some 216630732064840348 := by decide +kernel
private theorem endpoint_15_41_prefix_14 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 14 213559043327070041 = some 216630732064840348 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 12 2 213559043327070041 216630732064840348 216630732064840348 endpoint_15_41_prefix_12 endpoint_15_41_window_12

def endpoint_15_41 : CertifiedEndpoint :=
  ⟨⟨15, 41, 3009⟩, 216630732064840348, .terminal ⟨contact27, contact03, contact25⟩ (finish_receipt_window endpoint_15_41_flag endpoint_15_41_sources 14 213559043327070041 216630732064840348 rfl endpoint_15_41_base endpoint_15_41_prefix_14) (by decide)⟩
private def endpoint_15_42_flag : Flag := ⟨15, 42, 2975⟩
private def endpoint_15_42_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_42_base : receiptBase endpoint_15_42_flag endpoint_15_42_sources = some 217008280528757947 := by decide +kernel
private theorem endpoint_15_42_window_0 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 2 217008280528757947 = some 217008280528757947 := by decide +kernel
private theorem endpoint_15_42_window_2 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 2 2 217008280528757947 = some 217008280528757947 := by decide +kernel
private theorem endpoint_15_42_prefix_4 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 4 217008280528757947 = some 217008280528757947 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 2 2 217008280528757947 217008280528757947 217008280528757947 endpoint_15_42_window_0 endpoint_15_42_window_2
private theorem endpoint_15_42_window_4 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 4 2 217008280528757947 = some 217008280528757947 := by decide +kernel
private theorem endpoint_15_42_prefix_6 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 6 217008280528757947 = some 217008280528757947 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 4 2 217008280528757947 217008280528757947 217008280528757947 endpoint_15_42_prefix_4 endpoint_15_42_window_4
private theorem endpoint_15_42_window_6 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 6 2 217008280528757947 = some 217008280528757947 := by decide +kernel
private theorem endpoint_15_42_prefix_8 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 8 217008280528757947 = some 217008280528757947 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 6 2 217008280528757947 217008280528757947 217008280528757947 endpoint_15_42_prefix_6 endpoint_15_42_window_6
private theorem endpoint_15_42_window_8 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 8 2 217008280528757947 = some 217008280528757947 := by decide +kernel
private theorem endpoint_15_42_prefix_10 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 10 217008280528757947 = some 217008280528757947 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 8 2 217008280528757947 217008280528757947 217008280528757947 endpoint_15_42_prefix_8 endpoint_15_42_window_8
private theorem endpoint_15_42_window_10 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 10 2 217008280528757947 = some 217008280528757947 := by decide +kernel
private theorem endpoint_15_42_prefix_12 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 12 217008280528757947 = some 217008280528757947 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 10 2 217008280528757947 217008280528757947 217008280528757947 endpoint_15_42_prefix_10 endpoint_15_42_window_10
private theorem endpoint_15_42_window_12 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 12 2 217008280528757947 = some 217008280528757947 := by decide +kernel
private theorem endpoint_15_42_prefix_14 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 14 217008280528757947 = some 217008280528757947 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 12 2 217008280528757947 217008280528757947 217008280528757947 endpoint_15_42_prefix_12 endpoint_15_42_window_12

def endpoint_15_42 : CertifiedEndpoint :=
  ⟨⟨15, 42, 2975⟩, 217008280528757947, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_42_flag endpoint_15_42_sources 14 217008280528757947 217008280528757947 rfl endpoint_15_42_base endpoint_15_42_prefix_14) (by decide)⟩
private def endpoint_15_43_flag : Flag := ⟨15, 43, 2941⟩
private def endpoint_15_43_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_43_base : receiptBase endpoint_15_43_flag endpoint_15_43_sources = some 218873435684363354 := by decide +kernel
private theorem endpoint_15_43_window_0 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 2 218873435684363354 = some 219103722038274237 := by decide +kernel
private theorem endpoint_15_43_window_2 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 2 2 219103722038274237 = some 219103722038274237 := by decide +kernel
private theorem endpoint_15_43_prefix_4 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 4 218873435684363354 = some 219103722038274237 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 2 2 218873435684363354 219103722038274237 219103722038274237 endpoint_15_43_window_0 endpoint_15_43_window_2
private theorem endpoint_15_43_window_4 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 4 2 219103722038274237 = some 219103722038274237 := by decide +kernel
private theorem endpoint_15_43_prefix_6 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 6 218873435684363354 = some 219103722038274237 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 4 2 218873435684363354 219103722038274237 219103722038274237 endpoint_15_43_prefix_4 endpoint_15_43_window_4
private theorem endpoint_15_43_window_6 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 6 2 219103722038274237 = some 219103722038274237 := by decide +kernel
private theorem endpoint_15_43_prefix_8 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 8 218873435684363354 = some 219103722038274237 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 6 2 218873435684363354 219103722038274237 219103722038274237 endpoint_15_43_prefix_6 endpoint_15_43_window_6
private theorem endpoint_15_43_window_8 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 8 2 219103722038274237 = some 219103722038274237 := by decide +kernel
private theorem endpoint_15_43_prefix_10 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 10 218873435684363354 = some 219103722038274237 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 8 2 218873435684363354 219103722038274237 219103722038274237 endpoint_15_43_prefix_8 endpoint_15_43_window_8
private theorem endpoint_15_43_window_10 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 10 2 219103722038274237 = some 219103722038274237 := by decide +kernel
private theorem endpoint_15_43_prefix_12 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 12 218873435684363354 = some 219103722038274237 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 10 2 218873435684363354 219103722038274237 219103722038274237 endpoint_15_43_prefix_10 endpoint_15_43_window_10
private theorem endpoint_15_43_window_12 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 12 2 219103722038274237 = some 219103722038274237 := by decide +kernel
private theorem endpoint_15_43_prefix_14 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 14 218873435684363354 = some 219103722038274237 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 12 2 218873435684363354 219103722038274237 219103722038274237 endpoint_15_43_prefix_12 endpoint_15_43_window_12

def endpoint_15_43 : CertifiedEndpoint :=
  ⟨⟨15, 43, 2941⟩, 219103722038274237, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_43_flag endpoint_15_43_sources 14 218873435684363354 219103722038274237 rfl endpoint_15_43_base endpoint_15_43_prefix_14) (by decide)⟩
private def endpoint_15_44_flag : Flag := ⟨15, 44, 2905⟩
private def endpoint_15_44_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_44_base : receiptBase endpoint_15_44_flag endpoint_15_44_sources = some 220489581304437879 := by decide +kernel
private theorem endpoint_15_44_window_0 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 2 220489581304437879 = some 223940533503025510 := by decide +kernel
private theorem endpoint_15_44_window_2 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 2 2 223940533503025510 = some 223940533503025510 := by decide +kernel
private theorem endpoint_15_44_prefix_4 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 4 220489581304437879 = some 223940533503025510 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 2 2 220489581304437879 223940533503025510 223940533503025510 endpoint_15_44_window_0 endpoint_15_44_window_2
private theorem endpoint_15_44_window_4 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 4 2 223940533503025510 = some 223940533503025510 := by decide +kernel
private theorem endpoint_15_44_prefix_6 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 6 220489581304437879 = some 223940533503025510 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 4 2 220489581304437879 223940533503025510 223940533503025510 endpoint_15_44_prefix_4 endpoint_15_44_window_4
private theorem endpoint_15_44_window_6 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 6 2 223940533503025510 = some 223940533503025510 := by decide +kernel
private theorem endpoint_15_44_prefix_8 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 8 220489581304437879 = some 223940533503025510 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 6 2 220489581304437879 223940533503025510 223940533503025510 endpoint_15_44_prefix_6 endpoint_15_44_window_6
private theorem endpoint_15_44_window_8 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 8 2 223940533503025510 = some 223940533503025510 := by decide +kernel
private theorem endpoint_15_44_prefix_10 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 10 220489581304437879 = some 223940533503025510 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 8 2 220489581304437879 223940533503025510 223940533503025510 endpoint_15_44_prefix_8 endpoint_15_44_window_8
private theorem endpoint_15_44_window_10 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 10 2 223940533503025510 = some 223940533503025510 := by decide +kernel
private theorem endpoint_15_44_prefix_12 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 12 220489581304437879 = some 223940533503025510 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 10 2 220489581304437879 223940533503025510 223940533503025510 endpoint_15_44_prefix_10 endpoint_15_44_window_10
private theorem endpoint_15_44_window_12 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 12 2 223940533503025510 = some 223940533503025510 := by decide +kernel
private theorem endpoint_15_44_prefix_14 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 14 220489581304437879 = some 223940533503025510 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 12 2 220489581304437879 223940533503025510 223940533503025510 endpoint_15_44_prefix_12 endpoint_15_44_window_12

def endpoint_15_44 : CertifiedEndpoint :=
  ⟨⟨15, 44, 2905⟩, 223940533503025510, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_44_flag endpoint_15_44_sources 14 220489581304437879 223940533503025510 rfl endpoint_15_44_base endpoint_15_44_prefix_14) (by decide)⟩
private def endpoint_15_45_flag : Flag := ⟨15, 45, 2869⟩
private def endpoint_15_45_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_45_base : receiptBase endpoint_15_45_flag endpoint_15_45_sources = some 222000546857830598 := by decide +kernel
private theorem endpoint_15_45_window_0 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 2 222000546857830598 = some 228691598082303993 := by decide +kernel
private theorem endpoint_15_45_window_2 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 2 2 228691598082303993 = some 228691598082303993 := by decide +kernel
private theorem endpoint_15_45_prefix_4 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 4 222000546857830598 = some 228691598082303993 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 2 2 222000546857830598 228691598082303993 228691598082303993 endpoint_15_45_window_0 endpoint_15_45_window_2
private theorem endpoint_15_45_window_4 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 4 2 228691598082303993 = some 228691598082303993 := by decide +kernel
private theorem endpoint_15_45_prefix_6 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 6 222000546857830598 = some 228691598082303993 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 4 2 222000546857830598 228691598082303993 228691598082303993 endpoint_15_45_prefix_4 endpoint_15_45_window_4
private theorem endpoint_15_45_window_6 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 6 2 228691598082303993 = some 228691598082303993 := by decide +kernel
private theorem endpoint_15_45_prefix_8 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 8 222000546857830598 = some 228691598082303993 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 6 2 222000546857830598 228691598082303993 228691598082303993 endpoint_15_45_prefix_6 endpoint_15_45_window_6
private theorem endpoint_15_45_window_8 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 8 2 228691598082303993 = some 228691598082303993 := by decide +kernel
private theorem endpoint_15_45_prefix_10 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 10 222000546857830598 = some 228691598082303993 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 8 2 222000546857830598 228691598082303993 228691598082303993 endpoint_15_45_prefix_8 endpoint_15_45_window_8
private theorem endpoint_15_45_window_10 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 10 2 228691598082303993 = some 228691598082303993 := by decide +kernel
private theorem endpoint_15_45_prefix_12 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 12 222000546857830598 = some 228691598082303993 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 10 2 222000546857830598 228691598082303993 228691598082303993 endpoint_15_45_prefix_10 endpoint_15_45_window_10
private theorem endpoint_15_45_window_12 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 12 2 228691598082303993 = some 228691598082303993 := by decide +kernel
private theorem endpoint_15_45_prefix_14 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 14 222000546857830598 = some 228691598082303993 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 12 2 222000546857830598 228691598082303993 228691598082303993 endpoint_15_45_prefix_12 endpoint_15_45_window_12

def endpoint_15_45 : CertifiedEndpoint :=
  ⟨⟨15, 45, 2869⟩, 228691598082303993, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_45_flag endpoint_15_45_sources 14 222000546857830598 228691598082303993 rfl endpoint_15_45_base endpoint_15_45_prefix_14) (by decide)⟩
private def endpoint_15_46_flag : Flag := ⟨15, 46, 2832⟩
private def endpoint_15_46_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_46_base : receiptBase endpoint_15_46_flag endpoint_15_46_sources = some 223328654318791943 := by decide +kernel
private theorem endpoint_15_46_window_0 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 2 223328654318791943 = some 233314334379025128 := by decide +kernel
private theorem endpoint_15_46_window_2 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 2 2 233314334379025128 = some 233314334379025128 := by decide +kernel
private theorem endpoint_15_46_prefix_4 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 4 223328654318791943 = some 233314334379025128 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 2 2 223328654318791943 233314334379025128 233314334379025128 endpoint_15_46_window_0 endpoint_15_46_window_2
private theorem endpoint_15_46_window_4 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 4 2 233314334379025128 = some 233314334379025128 := by decide +kernel
private theorem endpoint_15_46_prefix_6 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 6 223328654318791943 = some 233314334379025128 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 4 2 223328654318791943 233314334379025128 233314334379025128 endpoint_15_46_prefix_4 endpoint_15_46_window_4
private theorem endpoint_15_46_window_6 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 6 2 233314334379025128 = some 233314334379025128 := by decide +kernel
private theorem endpoint_15_46_prefix_8 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 8 223328654318791943 = some 233314334379025128 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 6 2 223328654318791943 233314334379025128 233314334379025128 endpoint_15_46_prefix_6 endpoint_15_46_window_6
private theorem endpoint_15_46_window_8 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 8 2 233314334379025128 = some 233314334379025128 := by decide +kernel
private theorem endpoint_15_46_prefix_10 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 10 223328654318791943 = some 233314334379025128 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 8 2 223328654318791943 233314334379025128 233314334379025128 endpoint_15_46_prefix_8 endpoint_15_46_window_8
private theorem endpoint_15_46_window_10 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 10 2 233314334379025128 = some 233314334379025128 := by decide +kernel
private theorem endpoint_15_46_prefix_12 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 12 223328654318791943 = some 233314334379025128 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 10 2 223328654318791943 233314334379025128 233314334379025128 endpoint_15_46_prefix_10 endpoint_15_46_window_10
private theorem endpoint_15_46_window_12 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 12 2 233314334379025128 = some 233314334379025128 := by decide +kernel
private theorem endpoint_15_46_prefix_14 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 14 223328654318791943 = some 233314334379025128 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 12 2 223328654318791943 233314334379025128 233314334379025128 endpoint_15_46_prefix_12 endpoint_15_46_window_12

def endpoint_15_46 : CertifiedEndpoint :=
  ⟨⟨15, 46, 2832⟩, 233314334379025128, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_46_flag endpoint_15_46_sources 14 223328654318791943 233314334379025128 rfl endpoint_15_46_base endpoint_15_46_prefix_14) (by decide)⟩
private def endpoint_15_47_flag : Flag := ⟨15, 47, 2794⟩
private def endpoint_15_47_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_47_base : receiptBase endpoint_15_47_flag endpoint_15_47_sources = some 225133823619684197 := by decide +kernel
private theorem endpoint_15_47_window_0 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 2 225133823619684197 = some 232533557303395068 := by decide +kernel
private theorem endpoint_15_47_window_2 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 2 2 232533557303395068 = some 232533557303395068 := by decide +kernel
private theorem endpoint_15_47_prefix_4 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 4 225133823619684197 = some 232533557303395068 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 2 2 225133823619684197 232533557303395068 232533557303395068 endpoint_15_47_window_0 endpoint_15_47_window_2
private theorem endpoint_15_47_window_4 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 4 2 232533557303395068 = some 232533557303395068 := by decide +kernel
private theorem endpoint_15_47_prefix_6 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 6 225133823619684197 = some 232533557303395068 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 4 2 225133823619684197 232533557303395068 232533557303395068 endpoint_15_47_prefix_4 endpoint_15_47_window_4
private theorem endpoint_15_47_window_6 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 6 2 232533557303395068 = some 232533557303395068 := by decide +kernel
private theorem endpoint_15_47_prefix_8 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 8 225133823619684197 = some 232533557303395068 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 6 2 225133823619684197 232533557303395068 232533557303395068 endpoint_15_47_prefix_6 endpoint_15_47_window_6
private theorem endpoint_15_47_window_8 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 8 2 232533557303395068 = some 232533557303395068 := by decide +kernel
private theorem endpoint_15_47_prefix_10 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 10 225133823619684197 = some 232533557303395068 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 8 2 225133823619684197 232533557303395068 232533557303395068 endpoint_15_47_prefix_8 endpoint_15_47_window_8
private theorem endpoint_15_47_window_10 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 10 2 232533557303395068 = some 232533557303395068 := by decide +kernel
private theorem endpoint_15_47_prefix_12 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 12 225133823619684197 = some 232533557303395068 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 10 2 225133823619684197 232533557303395068 232533557303395068 endpoint_15_47_prefix_10 endpoint_15_47_window_10
private theorem endpoint_15_47_window_12 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 12 2 232533557303395068 = some 232533557303395068 := by decide +kernel
private theorem endpoint_15_47_prefix_14 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 14 225133823619684197 = some 232533557303395068 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 12 2 225133823619684197 232533557303395068 232533557303395068 endpoint_15_47_prefix_12 endpoint_15_47_window_12

def endpoint_15_47 : CertifiedEndpoint :=
  ⟨⟨15, 47, 2794⟩, 232533557303395068, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_47_flag endpoint_15_47_sources 14 225133823619684197 232533557303395068 rfl endpoint_15_47_base endpoint_15_47_prefix_14) (by decide)⟩
private def endpoint_15_48_flag : Flag := ⟨15, 48, 2754⟩
private def endpoint_15_48_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_48_base : receiptBase endpoint_15_48_flag endpoint_15_48_sources = some 226011742319403005 := by decide +kernel
private theorem endpoint_15_48_window_0 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 2 226011742319403005 = some 236708471851219182 := by decide +kernel
private theorem endpoint_15_48_window_2 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 2 2 236708471851219182 = some 236708471851219182 := by decide +kernel
private theorem endpoint_15_48_prefix_4 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 4 226011742319403005 = some 236708471851219182 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 2 2 226011742319403005 236708471851219182 236708471851219182 endpoint_15_48_window_0 endpoint_15_48_window_2
private theorem endpoint_15_48_window_4 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 4 2 236708471851219182 = some 236708471851219182 := by decide +kernel
private theorem endpoint_15_48_prefix_6 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 6 226011742319403005 = some 236708471851219182 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 4 2 226011742319403005 236708471851219182 236708471851219182 endpoint_15_48_prefix_4 endpoint_15_48_window_4
private theorem endpoint_15_48_window_6 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 6 2 236708471851219182 = some 236708471851219182 := by decide +kernel
private theorem endpoint_15_48_prefix_8 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 8 226011742319403005 = some 236708471851219182 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 6 2 226011742319403005 236708471851219182 236708471851219182 endpoint_15_48_prefix_6 endpoint_15_48_window_6
private theorem endpoint_15_48_window_8 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 8 2 236708471851219182 = some 236708471851219182 := by decide +kernel
private theorem endpoint_15_48_prefix_10 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 10 226011742319403005 = some 236708471851219182 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 8 2 226011742319403005 236708471851219182 236708471851219182 endpoint_15_48_prefix_8 endpoint_15_48_window_8
private theorem endpoint_15_48_window_10 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 10 2 236708471851219182 = some 236708471851219182 := by decide +kernel
private theorem endpoint_15_48_prefix_12 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 12 226011742319403005 = some 236708471851219182 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 10 2 226011742319403005 236708471851219182 236708471851219182 endpoint_15_48_prefix_10 endpoint_15_48_window_10
private theorem endpoint_15_48_window_12 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 12 2 236708471851219182 = some 236708471851219182 := by decide +kernel
private theorem endpoint_15_48_prefix_14 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 14 226011742319403005 = some 236708471851219182 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 12 2 226011742319403005 236708471851219182 236708471851219182 endpoint_15_48_prefix_12 endpoint_15_48_window_12

def endpoint_15_48 : CertifiedEndpoint :=
  ⟨⟨15, 48, 2754⟩, 236708471851219182, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_48_flag endpoint_15_48_sources 14 226011742319403005 236708471851219182 rfl endpoint_15_48_base endpoint_15_48_prefix_14) (by decide)⟩
private def endpoint_15_49_flag : Flag := ⟨15, 49, 2714⟩
private def endpoint_15_49_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_49_base : receiptBase endpoint_15_49_flag endpoint_15_49_sources = some 226772225310739992 := by decide +kernel
private theorem endpoint_15_49_window_0 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 2 226772225310739992 = some 240788499593000818 := by decide +kernel
private theorem endpoint_15_49_window_2 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 2 2 240788499593000818 = some 240788499593000818 := by decide +kernel
private theorem endpoint_15_49_prefix_4 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 4 226772225310739992 = some 240788499593000818 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 2 2 226772225310739992 240788499593000818 240788499593000818 endpoint_15_49_window_0 endpoint_15_49_window_2
private theorem endpoint_15_49_window_4 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 4 2 240788499593000818 = some 240788499593000818 := by decide +kernel
private theorem endpoint_15_49_prefix_6 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 6 226772225310739992 = some 240788499593000818 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 4 2 226772225310739992 240788499593000818 240788499593000818 endpoint_15_49_prefix_4 endpoint_15_49_window_4
private theorem endpoint_15_49_window_6 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 6 2 240788499593000818 = some 240788499593000818 := by decide +kernel
private theorem endpoint_15_49_prefix_8 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 8 226772225310739992 = some 240788499593000818 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 6 2 226772225310739992 240788499593000818 240788499593000818 endpoint_15_49_prefix_6 endpoint_15_49_window_6
private theorem endpoint_15_49_window_8 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 8 2 240788499593000818 = some 240788499593000818 := by decide +kernel
private theorem endpoint_15_49_prefix_10 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 10 226772225310739992 = some 240788499593000818 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 8 2 226772225310739992 240788499593000818 240788499593000818 endpoint_15_49_prefix_8 endpoint_15_49_window_8
private theorem endpoint_15_49_window_10 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 10 2 240788499593000818 = some 240788499593000818 := by decide +kernel
private theorem endpoint_15_49_prefix_12 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 12 226772225310739992 = some 240788499593000818 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 10 2 226772225310739992 240788499593000818 240788499593000818 endpoint_15_49_prefix_10 endpoint_15_49_window_10
private theorem endpoint_15_49_window_12 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 12 2 240788499593000818 = some 240788499593000818 := by decide +kernel
private theorem endpoint_15_49_prefix_14 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 14 226772225310739992 = some 240788499593000818 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 12 2 226772225310739992 240788499593000818 240788499593000818 endpoint_15_49_prefix_12 endpoint_15_49_window_12

def endpoint_15_49 : CertifiedEndpoint :=
  ⟨⟨15, 49, 2714⟩, 240788499593000818, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_49_flag endpoint_15_49_sources 14 226772225310739992 240788499593000818 rfl endpoint_15_49_base endpoint_15_49_prefix_14) (by decide)⟩
private def endpoint_15_50_flag : Flag := ⟨15, 50, 2673⟩
private def endpoint_15_50_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_50_base : receiptBase endpoint_15_50_flag endpoint_15_50_sources = some 227331519523461174 := by decide +kernel
private theorem endpoint_15_50_window_0 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 2 227331519523461174 = some 244726489171370574 := by decide +kernel
private theorem endpoint_15_50_window_2 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 2 2 244726489171370574 = some 244726489171370574 := by decide +kernel
private theorem endpoint_15_50_prefix_4 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 4 227331519523461174 = some 244726489171370574 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 2 2 227331519523461174 244726489171370574 244726489171370574 endpoint_15_50_window_0 endpoint_15_50_window_2
private theorem endpoint_15_50_window_4 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 4 2 244726489171370574 = some 244726489171370574 := by decide +kernel
private theorem endpoint_15_50_prefix_6 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 6 227331519523461174 = some 244726489171370574 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 4 2 227331519523461174 244726489171370574 244726489171370574 endpoint_15_50_prefix_4 endpoint_15_50_window_4
private theorem endpoint_15_50_window_6 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 6 2 244726489171370574 = some 244726489171370574 := by decide +kernel
private theorem endpoint_15_50_prefix_8 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 8 227331519523461174 = some 244726489171370574 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 6 2 227331519523461174 244726489171370574 244726489171370574 endpoint_15_50_prefix_6 endpoint_15_50_window_6
private theorem endpoint_15_50_window_8 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 8 2 244726489171370574 = some 244726489171370574 := by decide +kernel
private theorem endpoint_15_50_prefix_10 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 10 227331519523461174 = some 244726489171370574 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 8 2 227331519523461174 244726489171370574 244726489171370574 endpoint_15_50_prefix_8 endpoint_15_50_window_8
private theorem endpoint_15_50_window_10 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 10 2 244726489171370574 = some 244726489171370574 := by decide +kernel
private theorem endpoint_15_50_prefix_12 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 12 227331519523461174 = some 244726489171370574 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 10 2 227331519523461174 244726489171370574 244726489171370574 endpoint_15_50_prefix_10 endpoint_15_50_window_10
private theorem endpoint_15_50_window_12 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 12 2 244726489171370574 = some 244726489171370574 := by decide +kernel
private theorem endpoint_15_50_prefix_14 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 14 227331519523461174 = some 244726489171370574 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 12 2 227331519523461174 244726489171370574 244726489171370574 endpoint_15_50_prefix_12 endpoint_15_50_window_12

def endpoint_15_50 : CertifiedEndpoint :=
  ⟨⟨15, 50, 2673⟩, 244726489171370574, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_50_flag endpoint_15_50_sources 14 227331519523461174 244726489171370574 rfl endpoint_15_50_base endpoint_15_50_prefix_14) (by decide)⟩
private def endpoint_15_51_flag : Flag := ⟨15, 51, 2631⟩
private def endpoint_15_51_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_15_51_base : receiptBase endpoint_15_51_flag endpoint_15_51_sources = some 228425650695422335 := by decide +kernel
private theorem endpoint_15_51_window_0 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 2 228425650695422335 = some 244608373376006508 := by decide +kernel
private theorem endpoint_15_51_window_2 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 2 2 244608373376006508 = some 244608373376006508 := by decide +kernel
private theorem endpoint_15_51_prefix_4 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 4 228425650695422335 = some 244608373376006508 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 2 2 228425650695422335 244608373376006508 244608373376006508 endpoint_15_51_window_0 endpoint_15_51_window_2
private theorem endpoint_15_51_window_4 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 4 2 244608373376006508 = some 244608373376006508 := by decide +kernel
private theorem endpoint_15_51_prefix_6 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 6 228425650695422335 = some 244608373376006508 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 4 2 228425650695422335 244608373376006508 244608373376006508 endpoint_15_51_prefix_4 endpoint_15_51_window_4
private theorem endpoint_15_51_window_6 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 6 2 244608373376006508 = some 244608373376006508 := by decide +kernel
private theorem endpoint_15_51_prefix_8 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 8 228425650695422335 = some 244608373376006508 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 6 2 228425650695422335 244608373376006508 244608373376006508 endpoint_15_51_prefix_6 endpoint_15_51_window_6
private theorem endpoint_15_51_window_8 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 8 2 244608373376006508 = some 244608373376006508 := by decide +kernel
private theorem endpoint_15_51_prefix_10 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 10 228425650695422335 = some 244608373376006508 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 8 2 228425650695422335 244608373376006508 244608373376006508 endpoint_15_51_prefix_8 endpoint_15_51_window_8
private theorem endpoint_15_51_window_10 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 10 2 244608373376006508 = some 244608373376006508 := by decide +kernel
private theorem endpoint_15_51_prefix_12 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 12 228425650695422335 = some 244608373376006508 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 10 2 228425650695422335 244608373376006508 244608373376006508 endpoint_15_51_prefix_10 endpoint_15_51_window_10
private theorem endpoint_15_51_window_12 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 12 2 244608373376006508 = some 244608373376006508 := by decide +kernel
private theorem endpoint_15_51_prefix_14 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 14 228425650695422335 = some 244608373376006508 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 12 2 228425650695422335 244608373376006508 244608373376006508 endpoint_15_51_prefix_12 endpoint_15_51_window_12

def endpoint_15_51 : CertifiedEndpoint :=
  ⟨⟨15, 51, 2631⟩, 244608373376006508, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_15_51_flag endpoint_15_51_sources 14 228425650695422335 244608373376006508 rfl endpoint_15_51_base endpoint_15_51_prefix_14) (by decide)⟩
private def endpoint_15_52_flag : Flag := ⟨15, 52, 2587⟩
private def endpoint_15_52_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_15_52_base : receiptBase endpoint_15_52_flag endpoint_15_52_sources = some 228488941271080372 := by decide +kernel
private theorem endpoint_15_52_window_0 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 2 228488941271080372 = some 248111108578698688 := by decide +kernel
private theorem endpoint_15_52_window_2 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 2 2 248111108578698688 = some 248111108578698688 := by decide +kernel
private theorem endpoint_15_52_prefix_4 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 4 228488941271080372 = some 248111108578698688 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 2 2 228488941271080372 248111108578698688 248111108578698688 endpoint_15_52_window_0 endpoint_15_52_window_2
private theorem endpoint_15_52_window_4 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 4 2 248111108578698688 = some 248111108578698688 := by decide +kernel
private theorem endpoint_15_52_prefix_6 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 6 228488941271080372 = some 248111108578698688 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 4 2 228488941271080372 248111108578698688 248111108578698688 endpoint_15_52_prefix_4 endpoint_15_52_window_4
private theorem endpoint_15_52_window_6 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 6 2 248111108578698688 = some 248111108578698688 := by decide +kernel
private theorem endpoint_15_52_prefix_8 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 8 228488941271080372 = some 248111108578698688 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 6 2 228488941271080372 248111108578698688 248111108578698688 endpoint_15_52_prefix_6 endpoint_15_52_window_6
private theorem endpoint_15_52_window_8 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 8 2 248111108578698688 = some 248111108578698688 := by decide +kernel
private theorem endpoint_15_52_prefix_10 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 10 228488941271080372 = some 248111108578698688 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 8 2 228488941271080372 248111108578698688 248111108578698688 endpoint_15_52_prefix_8 endpoint_15_52_window_8
private theorem endpoint_15_52_window_10 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 10 2 248111108578698688 = some 248111108578698688 := by decide +kernel
private theorem endpoint_15_52_prefix_12 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 12 228488941271080372 = some 248111108578698688 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 10 2 228488941271080372 248111108578698688 248111108578698688 endpoint_15_52_prefix_10 endpoint_15_52_window_10
private theorem endpoint_15_52_window_12 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 12 2 248111108578698688 = some 248111108578698688 := by decide +kernel
private theorem endpoint_15_52_prefix_14 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 14 228488941271080372 = some 248111108578698688 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 12 2 228488941271080372 248111108578698688 248111108578698688 endpoint_15_52_prefix_12 endpoint_15_52_window_12

def endpoint_15_52 : CertifiedEndpoint :=
  ⟨⟨15, 52, 2587⟩, 248111108578698688, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_15_52_flag endpoint_15_52_sources 14 228488941271080372 248111108578698688 rfl endpoint_15_52_base endpoint_15_52_prefix_14) (by decide)⟩
private def endpoint_15_53_flag : Flag := ⟨15, 53, 2543⟩
private def endpoint_15_53_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_15_53_base : receiptBase endpoint_15_53_flag endpoint_15_53_sources = some 229209354331341201 := by decide +kernel
private theorem endpoint_15_53_window_0 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 2 229209354331341201 = some 248885741194836077 := by decide +kernel
private theorem endpoint_15_53_window_2 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 2 2 248885741194836077 = some 248885741194836077 := by decide +kernel
private theorem endpoint_15_53_prefix_4 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 4 229209354331341201 = some 248885741194836077 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 2 2 229209354331341201 248885741194836077 248885741194836077 endpoint_15_53_window_0 endpoint_15_53_window_2
private theorem endpoint_15_53_window_4 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 4 2 248885741194836077 = some 248885741194836077 := by decide +kernel
private theorem endpoint_15_53_prefix_6 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 6 229209354331341201 = some 248885741194836077 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 4 2 229209354331341201 248885741194836077 248885741194836077 endpoint_15_53_prefix_4 endpoint_15_53_window_4
private theorem endpoint_15_53_window_6 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 6 2 248885741194836077 = some 248885741194836077 := by decide +kernel
private theorem endpoint_15_53_prefix_8 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 8 229209354331341201 = some 248885741194836077 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 6 2 229209354331341201 248885741194836077 248885741194836077 endpoint_15_53_prefix_6 endpoint_15_53_window_6
private theorem endpoint_15_53_window_8 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 8 2 248885741194836077 = some 248885741194836077 := by decide +kernel
private theorem endpoint_15_53_prefix_10 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 10 229209354331341201 = some 248885741194836077 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 8 2 229209354331341201 248885741194836077 248885741194836077 endpoint_15_53_prefix_8 endpoint_15_53_window_8
private theorem endpoint_15_53_window_10 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 10 2 248885741194836077 = some 248885741194836077 := by decide +kernel
private theorem endpoint_15_53_prefix_12 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 12 229209354331341201 = some 248885741194836077 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 10 2 229209354331341201 248885741194836077 248885741194836077 endpoint_15_53_prefix_10 endpoint_15_53_window_10
private theorem endpoint_15_53_window_12 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 12 2 248885741194836077 = some 248885741194836077 := by decide +kernel
private theorem endpoint_15_53_prefix_14 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 14 229209354331341201 = some 248885741194836077 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 12 2 229209354331341201 248885741194836077 248885741194836077 endpoint_15_53_prefix_12 endpoint_15_53_window_12

def endpoint_15_53 : CertifiedEndpoint :=
  ⟨⟨15, 53, 2543⟩, 248885741194836077, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_15_53_flag endpoint_15_53_sources 14 229209354331341201 248885741194836077 rfl endpoint_15_53_base endpoint_15_53_prefix_14) (by decide)⟩
private def endpoint_15_54_flag : Flag := ⟨15, 54, 2497⟩
private def endpoint_15_54_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_15_54_base : receiptBase endpoint_15_54_flag endpoint_15_54_sources = some 228837896575462753 := by decide +kernel
private theorem endpoint_15_54_window_0 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 2 228837896575462753 = some 252018352552135758 := by decide +kernel
private theorem endpoint_15_54_window_2 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 2 2 252018352552135758 = some 252018352552135758 := by decide +kernel
private theorem endpoint_15_54_prefix_4 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 4 228837896575462753 = some 252018352552135758 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 2 2 228837896575462753 252018352552135758 252018352552135758 endpoint_15_54_window_0 endpoint_15_54_window_2
private theorem endpoint_15_54_window_4 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 4 2 252018352552135758 = some 252018352552135758 := by decide +kernel
private theorem endpoint_15_54_prefix_6 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 6 228837896575462753 = some 252018352552135758 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 4 2 228837896575462753 252018352552135758 252018352552135758 endpoint_15_54_prefix_4 endpoint_15_54_window_4
private theorem endpoint_15_54_window_6 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 6 2 252018352552135758 = some 252018352552135758 := by decide +kernel
private theorem endpoint_15_54_prefix_8 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 8 228837896575462753 = some 252018352552135758 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 6 2 228837896575462753 252018352552135758 252018352552135758 endpoint_15_54_prefix_6 endpoint_15_54_window_6
private theorem endpoint_15_54_window_8 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 8 2 252018352552135758 = some 252018352552135758 := by decide +kernel
private theorem endpoint_15_54_prefix_10 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 10 228837896575462753 = some 252018352552135758 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 8 2 228837896575462753 252018352552135758 252018352552135758 endpoint_15_54_prefix_8 endpoint_15_54_window_8
private theorem endpoint_15_54_window_10 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 10 2 252018352552135758 = some 252018352552135758 := by decide +kernel
private theorem endpoint_15_54_prefix_12 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 12 228837896575462753 = some 252018352552135758 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 10 2 228837896575462753 252018352552135758 252018352552135758 endpoint_15_54_prefix_10 endpoint_15_54_window_10
private theorem endpoint_15_54_window_12 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 12 2 252018352552135758 = some 252018352552135758 := by decide +kernel
private theorem endpoint_15_54_prefix_14 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 14 228837896575462753 = some 252018352552135758 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 12 2 228837896575462753 252018352552135758 252018352552135758 endpoint_15_54_prefix_12 endpoint_15_54_window_12

def endpoint_15_54 : CertifiedEndpoint :=
  ⟨⟨15, 54, 2497⟩, 252018352552135758, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_15_54_flag endpoint_15_54_sources 14 228837896575462753 252018352552135758 rfl endpoint_15_54_base endpoint_15_54_prefix_14) (by decide)⟩
private def endpoint_15_55_flag : Flag := ⟨15, 55, 2450⟩
private def endpoint_15_55_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_15_55_base : receiptBase endpoint_15_55_flag endpoint_15_55_sources = some 228919053524952569 := by decide +kernel
private theorem endpoint_15_55_window_0 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 2 228919053524952569 = some 247423428823505921 := by decide +kernel
private theorem endpoint_15_55_window_2 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 2 2 247423428823505921 = some 247423428823505921 := by decide +kernel
private theorem endpoint_15_55_prefix_4 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 4 228919053524952569 = some 247423428823505921 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 2 2 228919053524952569 247423428823505921 247423428823505921 endpoint_15_55_window_0 endpoint_15_55_window_2
private theorem endpoint_15_55_window_4 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 4 2 247423428823505921 = some 247423428823505921 := by decide +kernel
private theorem endpoint_15_55_prefix_6 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 6 228919053524952569 = some 247423428823505921 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 4 2 228919053524952569 247423428823505921 247423428823505921 endpoint_15_55_prefix_4 endpoint_15_55_window_4
private theorem endpoint_15_55_window_6 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 6 2 247423428823505921 = some 247423428823505921 := by decide +kernel
private theorem endpoint_15_55_prefix_8 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 8 228919053524952569 = some 247423428823505921 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 6 2 228919053524952569 247423428823505921 247423428823505921 endpoint_15_55_prefix_6 endpoint_15_55_window_6
private theorem endpoint_15_55_window_8 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 8 2 247423428823505921 = some 247423428823505921 := by decide +kernel
private theorem endpoint_15_55_prefix_10 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 10 228919053524952569 = some 247423428823505921 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 8 2 228919053524952569 247423428823505921 247423428823505921 endpoint_15_55_prefix_8 endpoint_15_55_window_8
private theorem endpoint_15_55_window_10 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 10 2 247423428823505921 = some 247423428823505921 := by decide +kernel
private theorem endpoint_15_55_prefix_12 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 12 228919053524952569 = some 247423428823505921 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 10 2 228919053524952569 247423428823505921 247423428823505921 endpoint_15_55_prefix_10 endpoint_15_55_window_10
private theorem endpoint_15_55_window_12 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 12 2 247423428823505921 = some 247423428823505921 := by decide +kernel
private theorem endpoint_15_55_prefix_14 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 14 228919053524952569 = some 247423428823505921 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 12 2 228919053524952569 247423428823505921 247423428823505921 endpoint_15_55_prefix_12 endpoint_15_55_window_12

def endpoint_15_55 : CertifiedEndpoint :=
  ⟨⟨15, 55, 2450⟩, 247423428823505921, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_15_55_flag endpoint_15_55_sources 14 228919053524952569 247423428823505921 rfl endpoint_15_55_base endpoint_15_55_prefix_14) (by decide)⟩
private def endpoint_15_56_flag : Flag := ⟨15, 56, 2401⟩
private def endpoint_15_56_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_15_56_base : receiptBase endpoint_15_56_flag endpoint_15_56_sources = some 227992600850255658 := by decide +kernel
private theorem endpoint_15_56_window_0 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 2 227992600850255658 = some 250013872814617664 := by decide +kernel
private theorem endpoint_15_56_window_2 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 2 2 250013872814617664 = some 250013872814617664 := by decide +kernel
private theorem endpoint_15_56_prefix_4 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 4 227992600850255658 = some 250013872814617664 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 2 2 227992600850255658 250013872814617664 250013872814617664 endpoint_15_56_window_0 endpoint_15_56_window_2
private theorem endpoint_15_56_window_4 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 4 2 250013872814617664 = some 250013872814617664 := by decide +kernel
private theorem endpoint_15_56_prefix_6 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 6 227992600850255658 = some 250013872814617664 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 4 2 227992600850255658 250013872814617664 250013872814617664 endpoint_15_56_prefix_4 endpoint_15_56_window_4
private theorem endpoint_15_56_window_6 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 6 2 250013872814617664 = some 250013872814617664 := by decide +kernel
private theorem endpoint_15_56_prefix_8 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 8 227992600850255658 = some 250013872814617664 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 6 2 227992600850255658 250013872814617664 250013872814617664 endpoint_15_56_prefix_6 endpoint_15_56_window_6
private theorem endpoint_15_56_window_8 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 8 2 250013872814617664 = some 250013872814617664 := by decide +kernel
private theorem endpoint_15_56_prefix_10 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 10 227992600850255658 = some 250013872814617664 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 8 2 227992600850255658 250013872814617664 250013872814617664 endpoint_15_56_prefix_8 endpoint_15_56_window_8
private theorem endpoint_15_56_window_10 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 10 2 250013872814617664 = some 250013872814617664 := by decide +kernel
private theorem endpoint_15_56_prefix_12 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 12 227992600850255658 = some 250013872814617664 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 10 2 227992600850255658 250013872814617664 250013872814617664 endpoint_15_56_prefix_10 endpoint_15_56_window_10
private theorem endpoint_15_56_window_12 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 12 2 250013872814617664 = some 250013872814617664 := by decide +kernel
private theorem endpoint_15_56_prefix_14 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 14 227992600850255658 = some 250013872814617664 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 12 2 227992600850255658 250013872814617664 250013872814617664 endpoint_15_56_prefix_12 endpoint_15_56_window_12

def endpoint_15_56 : CertifiedEndpoint :=
  ⟨⟨15, 56, 2401⟩, 250013872814617664, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_15_56_flag endpoint_15_56_sources 14 227992600850255658 250013872814617664 rfl endpoint_15_56_base endpoint_15_56_prefix_14) (by decide)⟩
private def endpoint_15_57_flag : Flag := ⟨15, 57, 2351⟩
private def endpoint_15_57_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_15_57_base : receiptBase endpoint_15_57_flag endpoint_15_57_sources = some 226824916767009347 := by decide +kernel
private theorem endpoint_15_57_window_0 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 2 226824916767009347 = some 252433716390537252 := by decide +kernel
private theorem endpoint_15_57_window_2 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 2 2 252433716390537252 = some 252433716390537252 := by decide +kernel
private theorem endpoint_15_57_prefix_4 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 4 226824916767009347 = some 252433716390537252 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 2 2 226824916767009347 252433716390537252 252433716390537252 endpoint_15_57_window_0 endpoint_15_57_window_2
private theorem endpoint_15_57_window_4 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 4 2 252433716390537252 = some 252433716390537252 := by decide +kernel
private theorem endpoint_15_57_prefix_6 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 6 226824916767009347 = some 252433716390537252 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 4 2 226824916767009347 252433716390537252 252433716390537252 endpoint_15_57_prefix_4 endpoint_15_57_window_4
private theorem endpoint_15_57_window_6 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 6 2 252433716390537252 = some 252433716390537252 := by decide +kernel
private theorem endpoint_15_57_prefix_8 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 8 226824916767009347 = some 252433716390537252 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 6 2 226824916767009347 252433716390537252 252433716390537252 endpoint_15_57_prefix_6 endpoint_15_57_window_6
private theorem endpoint_15_57_window_8 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 8 2 252433716390537252 = some 252433716390537252 := by decide +kernel
private theorem endpoint_15_57_prefix_10 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 10 226824916767009347 = some 252433716390537252 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 8 2 226824916767009347 252433716390537252 252433716390537252 endpoint_15_57_prefix_8 endpoint_15_57_window_8
private theorem endpoint_15_57_window_10 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 10 2 252433716390537252 = some 252433716390537252 := by decide +kernel
private theorem endpoint_15_57_prefix_12 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 12 226824916767009347 = some 252433716390537252 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 10 2 226824916767009347 252433716390537252 252433716390537252 endpoint_15_57_prefix_10 endpoint_15_57_window_10
private theorem endpoint_15_57_window_12 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 12 2 252433716390537252 = some 252433716390537252 := by decide +kernel
private theorem endpoint_15_57_prefix_14 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 14 226824916767009347 = some 252433716390537252 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 12 2 226824916767009347 252433716390537252 252433716390537252 endpoint_15_57_prefix_12 endpoint_15_57_window_12

def endpoint_15_57 : CertifiedEndpoint :=
  ⟨⟨15, 57, 2351⟩, 252433716390537252, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_15_57_flag endpoint_15_57_sources 14 226824916767009347 252433716390537252 rfl endpoint_15_57_base endpoint_15_57_prefix_14) (by decide)⟩
private def endpoint_15_58_flag : Flag := ⟨15, 58, 2300⟩
private def endpoint_15_58_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_15_58_base : receiptBase endpoint_15_58_flag endpoint_15_58_sources = some 225411570807085592 := by decide +kernel
private theorem endpoint_15_58_window_0 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 2 225411570807085592 = some 254679532081051052 := by decide +kernel
private theorem endpoint_15_58_window_2 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 2 2 254679532081051052 = some 254679532081051052 := by decide +kernel
private theorem endpoint_15_58_prefix_4 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 4 225411570807085592 = some 254679532081051052 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 2 2 225411570807085592 254679532081051052 254679532081051052 endpoint_15_58_window_0 endpoint_15_58_window_2
private theorem endpoint_15_58_window_4 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 4 2 254679532081051052 = some 254679532081051052 := by decide +kernel
private theorem endpoint_15_58_prefix_6 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 6 225411570807085592 = some 254679532081051052 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 4 2 225411570807085592 254679532081051052 254679532081051052 endpoint_15_58_prefix_4 endpoint_15_58_window_4
private theorem endpoint_15_58_window_6 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 6 2 254679532081051052 = some 254679532081051052 := by decide +kernel
private theorem endpoint_15_58_prefix_8 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 8 225411570807085592 = some 254679532081051052 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 6 2 225411570807085592 254679532081051052 254679532081051052 endpoint_15_58_prefix_6 endpoint_15_58_window_6
private theorem endpoint_15_58_window_8 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 8 2 254679532081051052 = some 254679532081051052 := by decide +kernel
private theorem endpoint_15_58_prefix_10 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 10 225411570807085592 = some 254679532081051052 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 8 2 225411570807085592 254679532081051052 254679532081051052 endpoint_15_58_prefix_8 endpoint_15_58_window_8
private theorem endpoint_15_58_window_10 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 10 2 254679532081051052 = some 254679532081051052 := by decide +kernel
private theorem endpoint_15_58_prefix_12 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 12 225411570807085592 = some 254679532081051052 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 10 2 225411570807085592 254679532081051052 254679532081051052 endpoint_15_58_prefix_10 endpoint_15_58_window_10
private theorem endpoint_15_58_window_12 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 12 2 254679532081051052 = some 254679532081051052 := by decide +kernel
private theorem endpoint_15_58_prefix_14 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 14 225411570807085592 = some 254679532081051052 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 12 2 225411570807085592 254679532081051052 254679532081051052 endpoint_15_58_prefix_12 endpoint_15_58_window_12

def endpoint_15_58 : CertifiedEndpoint :=
  ⟨⟨15, 58, 2300⟩, 254679532081051052, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_15_58_flag endpoint_15_58_sources 14 225411570807085592 254679532081051052 rfl endpoint_15_58_base endpoint_15_58_prefix_14) (by decide)⟩
private def endpoint_15_59_flag : Flag := ⟨15, 59, 2247⟩
private def endpoint_15_59_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_15_59_base : receiptBase endpoint_15_59_flag endpoint_15_59_sources = some 229396675694563045 := by decide +kernel
private theorem endpoint_15_59_window_0 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 2 229396675694563045 = some 248120032532765186 := by decide +kernel
private theorem endpoint_15_59_window_2 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 2 2 248120032532765186 = some 248120032532765186 := by decide +kernel
private theorem endpoint_15_59_prefix_4 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 4 229396675694563045 = some 248120032532765186 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 2 2 229396675694563045 248120032532765186 248120032532765186 endpoint_15_59_window_0 endpoint_15_59_window_2
private theorem endpoint_15_59_window_4 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 4 2 248120032532765186 = some 248120032532765186 := by decide +kernel
private theorem endpoint_15_59_prefix_6 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 6 229396675694563045 = some 248120032532765186 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 4 2 229396675694563045 248120032532765186 248120032532765186 endpoint_15_59_prefix_4 endpoint_15_59_window_4
private theorem endpoint_15_59_window_6 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 6 2 248120032532765186 = some 248120032532765186 := by decide +kernel
private theorem endpoint_15_59_prefix_8 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 8 229396675694563045 = some 248120032532765186 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 6 2 229396675694563045 248120032532765186 248120032532765186 endpoint_15_59_prefix_6 endpoint_15_59_window_6
private theorem endpoint_15_59_window_8 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 8 2 248120032532765186 = some 248120032532765186 := by decide +kernel
private theorem endpoint_15_59_prefix_10 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 10 229396675694563045 = some 248120032532765186 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 8 2 229396675694563045 248120032532765186 248120032532765186 endpoint_15_59_prefix_8 endpoint_15_59_window_8
private theorem endpoint_15_59_window_10 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 10 2 248120032532765186 = some 248120032532765186 := by decide +kernel
private theorem endpoint_15_59_prefix_12 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 12 229396675694563045 = some 248120032532765186 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 10 2 229396675694563045 248120032532765186 248120032532765186 endpoint_15_59_prefix_10 endpoint_15_59_window_10
private theorem endpoint_15_59_window_12 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 12 2 248120032532765186 = some 248120032532765186 := by decide +kernel
private theorem endpoint_15_59_prefix_14 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 14 229396675694563045 = some 248120032532765186 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 12 2 229396675694563045 248120032532765186 248120032532765186 endpoint_15_59_prefix_12 endpoint_15_59_window_12

def endpoint_15_59 : CertifiedEndpoint :=
  ⟨⟨15, 59, 2247⟩, 248120032532765186, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_15_59_flag endpoint_15_59_sources 14 229396675694563045 248120032532765186 rfl endpoint_15_59_base endpoint_15_59_prefix_14) (by decide)⟩
private def endpoint_15_60_flag : Flag := ⟨15, 60, 2193⟩
private def endpoint_15_60_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_60_base : receiptBase endpoint_15_60_flag endpoint_15_60_sources = some 227387654732603169 := by decide +kernel
private theorem endpoint_15_60_window_0 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 2 227387654732603169 = some 244802412294862950 := by decide +kernel
private theorem endpoint_15_60_window_2 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 2 2 244802412294862950 = some 244802412294862950 := by decide +kernel
private theorem endpoint_15_60_prefix_4 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 4 227387654732603169 = some 244802412294862950 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 2 2 227387654732603169 244802412294862950 244802412294862950 endpoint_15_60_window_0 endpoint_15_60_window_2
private theorem endpoint_15_60_window_4 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 4 2 244802412294862950 = some 244802412294862950 := by decide +kernel
private theorem endpoint_15_60_prefix_6 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 6 227387654732603169 = some 244802412294862950 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 4 2 227387654732603169 244802412294862950 244802412294862950 endpoint_15_60_prefix_4 endpoint_15_60_window_4
private theorem endpoint_15_60_window_6 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 6 2 244802412294862950 = some 244802412294862950 := by decide +kernel
private theorem endpoint_15_60_prefix_8 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 8 227387654732603169 = some 244802412294862950 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 6 2 227387654732603169 244802412294862950 244802412294862950 endpoint_15_60_prefix_6 endpoint_15_60_window_6
private theorem endpoint_15_60_window_8 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 8 2 244802412294862950 = some 244802412294862950 := by decide +kernel
private theorem endpoint_15_60_prefix_10 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 10 227387654732603169 = some 244802412294862950 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 8 2 227387654732603169 244802412294862950 244802412294862950 endpoint_15_60_prefix_8 endpoint_15_60_window_8
private theorem endpoint_15_60_window_10 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 10 2 244802412294862950 = some 244802412294862950 := by decide +kernel
private theorem endpoint_15_60_prefix_12 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 12 227387654732603169 = some 244802412294862950 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 10 2 227387654732603169 244802412294862950 244802412294862950 endpoint_15_60_prefix_10 endpoint_15_60_window_10
private theorem endpoint_15_60_window_12 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 12 2 244802412294862950 = some 244802412294862950 := by decide +kernel
private theorem endpoint_15_60_prefix_14 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 14 227387654732603169 = some 244802412294862950 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 12 2 227387654732603169 244802412294862950 244802412294862950 endpoint_15_60_prefix_12 endpoint_15_60_window_12

def endpoint_15_60 : CertifiedEndpoint :=
  ⟨⟨15, 60, 2193⟩, 244802412294862950, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_60_flag endpoint_15_60_sources 14 227387654732603169 244802412294862950 rfl endpoint_15_60_base endpoint_15_60_prefix_14) (by decide)⟩
private def endpoint_15_61_flag : Flag := ⟨15, 61, 2136⟩
private def endpoint_15_61_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_61_base : receiptBase endpoint_15_61_flag endpoint_15_61_sources = some 224877921046394758 := by decide +kernel
private theorem endpoint_15_61_window_0 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 2 224877921046394758 = some 246059140822271266 := by decide +kernel
private theorem endpoint_15_61_window_2 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 2 2 246059140822271266 = some 246059140822271266 := by decide +kernel
private theorem endpoint_15_61_prefix_4 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 4 224877921046394758 = some 246059140822271266 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 2 2 224877921046394758 246059140822271266 246059140822271266 endpoint_15_61_window_0 endpoint_15_61_window_2
private theorem endpoint_15_61_window_4 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 4 2 246059140822271266 = some 246059140822271266 := by decide +kernel
private theorem endpoint_15_61_prefix_6 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 6 224877921046394758 = some 246059140822271266 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 4 2 224877921046394758 246059140822271266 246059140822271266 endpoint_15_61_prefix_4 endpoint_15_61_window_4
private theorem endpoint_15_61_window_6 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 6 2 246059140822271266 = some 246059140822271266 := by decide +kernel
private theorem endpoint_15_61_prefix_8 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 8 224877921046394758 = some 246059140822271266 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 6 2 224877921046394758 246059140822271266 246059140822271266 endpoint_15_61_prefix_6 endpoint_15_61_window_6
private theorem endpoint_15_61_window_8 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 8 2 246059140822271266 = some 246059140822271266 := by decide +kernel
private theorem endpoint_15_61_prefix_10 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 10 224877921046394758 = some 246059140822271266 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 8 2 224877921046394758 246059140822271266 246059140822271266 endpoint_15_61_prefix_8 endpoint_15_61_window_8
private theorem endpoint_15_61_window_10 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 10 2 246059140822271266 = some 246059140822271266 := by decide +kernel
private theorem endpoint_15_61_prefix_12 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 12 224877921046394758 = some 246059140822271266 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 10 2 224877921046394758 246059140822271266 246059140822271266 endpoint_15_61_prefix_10 endpoint_15_61_window_10
private theorem endpoint_15_61_window_12 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 12 2 246059140822271266 = some 246059140822271266 := by decide +kernel
private theorem endpoint_15_61_prefix_14 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 14 224877921046394758 = some 246059140822271266 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 12 2 224877921046394758 246059140822271266 246059140822271266 endpoint_15_61_prefix_12 endpoint_15_61_window_12

def endpoint_15_61 : CertifiedEndpoint :=
  ⟨⟨15, 61, 2136⟩, 246059140822271266, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_61_flag endpoint_15_61_sources 14 224877921046394758 246059140822271266 rfl endpoint_15_61_base endpoint_15_61_prefix_14) (by decide)⟩
private def endpoint_15_62_flag : Flag := ⟨15, 62, 2078⟩
private def endpoint_15_62_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_62_base : receiptBase endpoint_15_62_flag endpoint_15_62_sources = some 222094200687303663 := by decide +kernel
private theorem endpoint_15_62_window_0 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 2 222094200687303663 = some 247121276642991996 := by decide +kernel
private theorem endpoint_15_62_window_2 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 2 2 247121276642991996 = some 247121276642991996 := by decide +kernel
private theorem endpoint_15_62_prefix_4 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 4 222094200687303663 = some 247121276642991996 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 2 2 222094200687303663 247121276642991996 247121276642991996 endpoint_15_62_window_0 endpoint_15_62_window_2
private theorem endpoint_15_62_window_4 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 4 2 247121276642991996 = some 247121276642991996 := by decide +kernel
private theorem endpoint_15_62_prefix_6 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 6 222094200687303663 = some 247121276642991996 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 4 2 222094200687303663 247121276642991996 247121276642991996 endpoint_15_62_prefix_4 endpoint_15_62_window_4
private theorem endpoint_15_62_window_6 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 6 2 247121276642991996 = some 247121276642991996 := by decide +kernel
private theorem endpoint_15_62_prefix_8 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 8 222094200687303663 = some 247121276642991996 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 6 2 222094200687303663 247121276642991996 247121276642991996 endpoint_15_62_prefix_6 endpoint_15_62_window_6
private theorem endpoint_15_62_window_8 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 8 2 247121276642991996 = some 247121276642991996 := by decide +kernel
private theorem endpoint_15_62_prefix_10 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 10 222094200687303663 = some 247121276642991996 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 8 2 222094200687303663 247121276642991996 247121276642991996 endpoint_15_62_prefix_8 endpoint_15_62_window_8
private theorem endpoint_15_62_window_10 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 10 2 247121276642991996 = some 247121276642991996 := by decide +kernel
private theorem endpoint_15_62_prefix_12 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 12 222094200687303663 = some 247121276642991996 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 10 2 222094200687303663 247121276642991996 247121276642991996 endpoint_15_62_prefix_10 endpoint_15_62_window_10
private theorem endpoint_15_62_window_12 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 12 2 247121276642991996 = some 247121276642991996 := by decide +kernel
private theorem endpoint_15_62_prefix_14 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 14 222094200687303663 = some 247121276642991996 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 12 2 222094200687303663 247121276642991996 247121276642991996 endpoint_15_62_prefix_12 endpoint_15_62_window_12

def endpoint_15_62 : CertifiedEndpoint :=
  ⟨⟨15, 62, 2078⟩, 247121276642991996, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_62_flag endpoint_15_62_sources 14 222094200687303663 247121276642991996 rfl endpoint_15_62_base endpoint_15_62_prefix_14) (by decide)⟩
private def endpoint_15_63_flag : Flag := ⟨15, 63, 2019⟩
private def endpoint_15_63_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_15_63_base : receiptBase endpoint_15_63_flag endpoint_15_63_sources = some 219953406664375713 := by decide +kernel
private theorem endpoint_15_63_window_0 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 2 219953406664375713 = some 235015564435512432 := by decide +kernel
private theorem endpoint_15_63_window_2 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 2 2 235015564435512432 = some 235015564435512432 := by decide +kernel
private theorem endpoint_15_63_prefix_4 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 4 219953406664375713 = some 235015564435512432 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 2 2 219953406664375713 235015564435512432 235015564435512432 endpoint_15_63_window_0 endpoint_15_63_window_2
private theorem endpoint_15_63_window_4 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 4 2 235015564435512432 = some 235015564435512432 := by decide +kernel
private theorem endpoint_15_63_prefix_6 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 6 219953406664375713 = some 235015564435512432 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 4 2 219953406664375713 235015564435512432 235015564435512432 endpoint_15_63_prefix_4 endpoint_15_63_window_4
private theorem endpoint_15_63_window_6 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 6 2 235015564435512432 = some 235015564435512432 := by decide +kernel
private theorem endpoint_15_63_prefix_8 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 8 219953406664375713 = some 235015564435512432 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 6 2 219953406664375713 235015564435512432 235015564435512432 endpoint_15_63_prefix_6 endpoint_15_63_window_6
private theorem endpoint_15_63_window_8 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 8 2 235015564435512432 = some 235015564435512432 := by decide +kernel
private theorem endpoint_15_63_prefix_10 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 10 219953406664375713 = some 235015564435512432 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 8 2 219953406664375713 235015564435512432 235015564435512432 endpoint_15_63_prefix_8 endpoint_15_63_window_8
private theorem endpoint_15_63_window_10 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 10 2 235015564435512432 = some 235015564435512432 := by decide +kernel
private theorem endpoint_15_63_prefix_12 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 12 219953406664375713 = some 235015564435512432 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 10 2 219953406664375713 235015564435512432 235015564435512432 endpoint_15_63_prefix_10 endpoint_15_63_window_10
private theorem endpoint_15_63_window_12 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 12 2 235015564435512432 = some 235015564435512432 := by decide +kernel
private theorem endpoint_15_63_prefix_14 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 14 219953406664375713 = some 235015564435512432 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 12 2 219953406664375713 235015564435512432 235015564435512432 endpoint_15_63_prefix_12 endpoint_15_63_window_12

def endpoint_15_63 : CertifiedEndpoint :=
  ⟨⟨15, 63, 2019⟩, 235015564435512432, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_15_63_flag endpoint_15_63_sources 14 219953406664375713 235015564435512432 rfl endpoint_15_63_base endpoint_15_63_prefix_14) (by decide)⟩
private def endpoint_15_64_flag : Flag := ⟨15, 64, 1957⟩
private def endpoint_15_64_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_15_64_base : receiptBase endpoint_15_64_flag endpoint_15_64_sources = some 216366058889742419 := by decide +kernel
private theorem endpoint_15_64_window_0 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 2 216366058889742419 = some 235315083857771292 := by decide +kernel
private theorem endpoint_15_64_window_2 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 2 2 235315083857771292 = some 235315083857771292 := by decide +kernel
private theorem endpoint_15_64_prefix_4 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 4 216366058889742419 = some 235315083857771292 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 2 2 216366058889742419 235315083857771292 235315083857771292 endpoint_15_64_window_0 endpoint_15_64_window_2
private theorem endpoint_15_64_window_4 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 4 2 235315083857771292 = some 235315083857771292 := by decide +kernel
private theorem endpoint_15_64_prefix_6 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 6 216366058889742419 = some 235315083857771292 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 4 2 216366058889742419 235315083857771292 235315083857771292 endpoint_15_64_prefix_4 endpoint_15_64_window_4
private theorem endpoint_15_64_window_6 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 6 2 235315083857771292 = some 235315083857771292 := by decide +kernel
private theorem endpoint_15_64_prefix_8 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 8 216366058889742419 = some 235315083857771292 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 6 2 216366058889742419 235315083857771292 235315083857771292 endpoint_15_64_prefix_6 endpoint_15_64_window_6
private theorem endpoint_15_64_window_8 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 8 2 235315083857771292 = some 235315083857771292 := by decide +kernel
private theorem endpoint_15_64_prefix_10 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 10 216366058889742419 = some 235315083857771292 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 8 2 216366058889742419 235315083857771292 235315083857771292 endpoint_15_64_prefix_8 endpoint_15_64_window_8
private theorem endpoint_15_64_window_10 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 10 2 235315083857771292 = some 235315083857771292 := by decide +kernel
private theorem endpoint_15_64_prefix_12 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 12 216366058889742419 = some 235315083857771292 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 10 2 216366058889742419 235315083857771292 235315083857771292 endpoint_15_64_prefix_10 endpoint_15_64_window_10
private theorem endpoint_15_64_window_12 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 12 2 235315083857771292 = some 235315083857771292 := by decide +kernel
private theorem endpoint_15_64_prefix_14 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 14 216366058889742419 = some 235315083857771292 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 12 2 216366058889742419 235315083857771292 235315083857771292 endpoint_15_64_prefix_12 endpoint_15_64_window_12

def endpoint_15_64 : CertifiedEndpoint :=
  ⟨⟨15, 64, 1957⟩, 235315083857771292, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_15_64_flag endpoint_15_64_sources 14 216366058889742419 235315083857771292 rfl endpoint_15_64_base endpoint_15_64_prefix_14) (by decide)⟩
private def endpoint_15_65_flag : Flag := ⟨15, 65, 1893⟩
private def endpoint_15_65_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_15_65_base : receiptBase endpoint_15_65_flag endpoint_15_65_sources = some 212373627605389290 := by decide +kernel
private theorem endpoint_15_65_window_0 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 2 212373627605389290 = some 235340869493979256 := by decide +kernel
private theorem endpoint_15_65_window_2 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 2 2 235340869493979256 = some 235340869493979256 := by decide +kernel
private theorem endpoint_15_65_prefix_4 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 4 212373627605389290 = some 235340869493979256 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 2 2 212373627605389290 235340869493979256 235340869493979256 endpoint_15_65_window_0 endpoint_15_65_window_2
private theorem endpoint_15_65_window_4 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 4 2 235340869493979256 = some 235340869493979256 := by decide +kernel
private theorem endpoint_15_65_prefix_6 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 6 212373627605389290 = some 235340869493979256 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 4 2 212373627605389290 235340869493979256 235340869493979256 endpoint_15_65_prefix_4 endpoint_15_65_window_4
private theorem endpoint_15_65_window_6 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 6 2 235340869493979256 = some 235340869493979256 := by decide +kernel
private theorem endpoint_15_65_prefix_8 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 8 212373627605389290 = some 235340869493979256 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 6 2 212373627605389290 235340869493979256 235340869493979256 endpoint_15_65_prefix_6 endpoint_15_65_window_6
private theorem endpoint_15_65_window_8 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 8 2 235340869493979256 = some 235340869493979256 := by decide +kernel
private theorem endpoint_15_65_prefix_10 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 10 212373627605389290 = some 235340869493979256 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 8 2 212373627605389290 235340869493979256 235340869493979256 endpoint_15_65_prefix_8 endpoint_15_65_window_8
private theorem endpoint_15_65_window_10 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 10 2 235340869493979256 = some 235340869493979256 := by decide +kernel
private theorem endpoint_15_65_prefix_12 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 12 212373627605389290 = some 235340869493979256 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 10 2 212373627605389290 235340869493979256 235340869493979256 endpoint_15_65_prefix_10 endpoint_15_65_window_10
private theorem endpoint_15_65_window_12 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 12 2 235340869493979256 = some 235340869493979256 := by decide +kernel
private theorem endpoint_15_65_prefix_14 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 14 212373627605389290 = some 235340869493979256 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 12 2 212373627605389290 235340869493979256 235340869493979256 endpoint_15_65_prefix_12 endpoint_15_65_window_12

def endpoint_15_65 : CertifiedEndpoint :=
  ⟨⟨15, 65, 1893⟩, 235340869493979256, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_15_65_flag endpoint_15_65_sources 14 212373627605389290 235340869493979256 rfl endpoint_15_65_base endpoint_15_65_prefix_14) (by decide)⟩
private def endpoint_15_66_flag : Flag := ⟨15, 66, 1828⟩
private def endpoint_15_66_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_15_66_base : receiptBase endpoint_15_66_flag endpoint_15_66_sources = some 209119777338576562 := by decide +kernel
private theorem endpoint_15_66_window_0 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 2 209119777338576562 = some 228379024203981036 := by decide +kernel
private theorem endpoint_15_66_window_2 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 2 2 228379024203981036 = some 228379024203981036 := by decide +kernel
private theorem endpoint_15_66_prefix_4 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 4 209119777338576562 = some 228379024203981036 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 2 2 209119777338576562 228379024203981036 228379024203981036 endpoint_15_66_window_0 endpoint_15_66_window_2
private theorem endpoint_15_66_window_4 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 4 2 228379024203981036 = some 228379024203981036 := by decide +kernel
private theorem endpoint_15_66_prefix_6 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 6 209119777338576562 = some 228379024203981036 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 4 2 209119777338576562 228379024203981036 228379024203981036 endpoint_15_66_prefix_4 endpoint_15_66_window_4
private theorem endpoint_15_66_window_6 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 6 2 228379024203981036 = some 228379024203981036 := by decide +kernel
private theorem endpoint_15_66_prefix_8 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 8 209119777338576562 = some 228379024203981036 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 6 2 209119777338576562 228379024203981036 228379024203981036 endpoint_15_66_prefix_6 endpoint_15_66_window_6
private theorem endpoint_15_66_window_8 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 8 2 228379024203981036 = some 228379024203981036 := by decide +kernel
private theorem endpoint_15_66_prefix_10 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 10 209119777338576562 = some 228379024203981036 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 8 2 209119777338576562 228379024203981036 228379024203981036 endpoint_15_66_prefix_8 endpoint_15_66_window_8
private theorem endpoint_15_66_window_10 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 10 2 228379024203981036 = some 228379024203981036 := by decide +kernel
private theorem endpoint_15_66_prefix_12 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 12 209119777338576562 = some 228379024203981036 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 10 2 209119777338576562 228379024203981036 228379024203981036 endpoint_15_66_prefix_10 endpoint_15_66_window_10
private theorem endpoint_15_66_window_12 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 12 2 228379024203981036 = some 228379024203981036 := by decide +kernel
private theorem endpoint_15_66_prefix_14 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 14 209119777338576562 = some 228379024203981036 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 12 2 209119777338576562 228379024203981036 228379024203981036 endpoint_15_66_prefix_12 endpoint_15_66_window_12

def endpoint_15_66 : CertifiedEndpoint :=
  ⟨⟨15, 66, 1828⟩, 228379024203981036, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_15_66_flag endpoint_15_66_sources 14 209119777338576562 228379024203981036 rfl endpoint_15_66_base endpoint_15_66_prefix_14) (by decide)⟩
private def endpoint_15_67_flag : Flag := ⟨15, 67, 1760⟩
private def endpoint_15_67_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_15_67_base : receiptBase endpoint_15_67_flag endpoint_15_67_sources = some 206791266385202710 := by decide +kernel
private theorem endpoint_15_67_window_0 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 2 206791266385202710 = some 211323109612701634 := by decide +kernel
private theorem endpoint_15_67_window_2 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 2 2 211323109612701634 = some 211323109612701634 := by decide +kernel
private theorem endpoint_15_67_prefix_4 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 4 206791266385202710 = some 211323109612701634 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 2 2 206791266385202710 211323109612701634 211323109612701634 endpoint_15_67_window_0 endpoint_15_67_window_2
private theorem endpoint_15_67_window_4 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 4 2 211323109612701634 = some 211323109612701634 := by decide +kernel
private theorem endpoint_15_67_prefix_6 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 6 206791266385202710 = some 211323109612701634 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 4 2 206791266385202710 211323109612701634 211323109612701634 endpoint_15_67_prefix_4 endpoint_15_67_window_4
private theorem endpoint_15_67_window_6 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 6 2 211323109612701634 = some 211323109612701634 := by decide +kernel
private theorem endpoint_15_67_prefix_8 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 8 206791266385202710 = some 211323109612701634 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 6 2 206791266385202710 211323109612701634 211323109612701634 endpoint_15_67_prefix_6 endpoint_15_67_window_6
private theorem endpoint_15_67_window_8 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 8 2 211323109612701634 = some 211323109612701634 := by decide +kernel
private theorem endpoint_15_67_prefix_10 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 10 206791266385202710 = some 211323109612701634 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 8 2 206791266385202710 211323109612701634 211323109612701634 endpoint_15_67_prefix_8 endpoint_15_67_window_8
private theorem endpoint_15_67_window_10 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 10 2 211323109612701634 = some 211323109612701634 := by decide +kernel
private theorem endpoint_15_67_prefix_12 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 12 206791266385202710 = some 211323109612701634 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 10 2 206791266385202710 211323109612701634 211323109612701634 endpoint_15_67_prefix_10 endpoint_15_67_window_10
private theorem endpoint_15_67_window_12 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 12 2 211323109612701634 = some 211323109612701634 := by decide +kernel
private theorem endpoint_15_67_prefix_14 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 14 206791266385202710 = some 211323109612701634 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 12 2 206791266385202710 211323109612701634 211323109612701634 endpoint_15_67_prefix_12 endpoint_15_67_window_12

def endpoint_15_67 : CertifiedEndpoint :=
  ⟨⟨15, 67, 1760⟩, 211323109612701634, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_15_67_flag endpoint_15_67_sources 14 206791266385202710 211323109612701634 rfl endpoint_15_67_base endpoint_15_67_prefix_14) (by decide)⟩
private def endpoint_15_68_flag : Flag := ⟨15, 68, 1689⟩
private def endpoint_15_68_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_15_68_base : receiptBase endpoint_15_68_flag endpoint_15_68_sources = some 201152966044798824 := by decide +kernel
private theorem endpoint_15_68_window_0 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 2 201152966044798824 = some 210023666923241922 := by decide +kernel
private theorem endpoint_15_68_window_2 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 2 2 210023666923241922 = some 210023666923241922 := by decide +kernel
private theorem endpoint_15_68_prefix_4 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 4 201152966044798824 = some 210023666923241922 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 2 2 201152966044798824 210023666923241922 210023666923241922 endpoint_15_68_window_0 endpoint_15_68_window_2
private theorem endpoint_15_68_window_4 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 4 2 210023666923241922 = some 210023666923241922 := by decide +kernel
private theorem endpoint_15_68_prefix_6 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 6 201152966044798824 = some 210023666923241922 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 4 2 201152966044798824 210023666923241922 210023666923241922 endpoint_15_68_prefix_4 endpoint_15_68_window_4
private theorem endpoint_15_68_window_6 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 6 2 210023666923241922 = some 210023666923241922 := by decide +kernel
private theorem endpoint_15_68_prefix_8 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 8 201152966044798824 = some 210023666923241922 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 6 2 201152966044798824 210023666923241922 210023666923241922 endpoint_15_68_prefix_6 endpoint_15_68_window_6
private theorem endpoint_15_68_window_8 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 8 2 210023666923241922 = some 210023666923241922 := by decide +kernel
private theorem endpoint_15_68_prefix_10 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 10 201152966044798824 = some 210023666923241922 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 8 2 201152966044798824 210023666923241922 210023666923241922 endpoint_15_68_prefix_8 endpoint_15_68_window_8
private theorem endpoint_15_68_window_10 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 10 2 210023666923241922 = some 210023666923241922 := by decide +kernel
private theorem endpoint_15_68_prefix_12 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 12 201152966044798824 = some 210023666923241922 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 10 2 201152966044798824 210023666923241922 210023666923241922 endpoint_15_68_prefix_10 endpoint_15_68_window_10
private theorem endpoint_15_68_window_12 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 12 2 210023666923241922 = some 210023666923241922 := by decide +kernel
private theorem endpoint_15_68_prefix_14 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 14 201152966044798824 = some 210023666923241922 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 12 2 201152966044798824 210023666923241922 210023666923241922 endpoint_15_68_prefix_12 endpoint_15_68_window_12

def endpoint_15_68 : CertifiedEndpoint :=
  ⟨⟨15, 68, 1689⟩, 210023666923241922, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_15_68_flag endpoint_15_68_sources 14 201152966044798824 210023666923241922 rfl endpoint_15_68_base endpoint_15_68_prefix_14) (by decide)⟩
private def endpoint_15_69_flag : Flag := ⟨15, 69, 1617⟩
private def endpoint_15_69_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_15_69_base : receiptBase endpoint_15_69_flag endpoint_15_69_sources = some 195173709039510041 := by decide +kernel
private theorem endpoint_15_69_window_0 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 2 195173709039510041 = some 208489644374602239 := by decide +kernel
private theorem endpoint_15_69_window_2 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 2 2 208489644374602239 = some 208489644374602239 := by decide +kernel
private theorem endpoint_15_69_prefix_4 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 4 195173709039510041 = some 208489644374602239 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 2 2 195173709039510041 208489644374602239 208489644374602239 endpoint_15_69_window_0 endpoint_15_69_window_2
private theorem endpoint_15_69_window_4 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 4 2 208489644374602239 = some 208489644374602239 := by decide +kernel
private theorem endpoint_15_69_prefix_6 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 6 195173709039510041 = some 208489644374602239 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 4 2 195173709039510041 208489644374602239 208489644374602239 endpoint_15_69_prefix_4 endpoint_15_69_window_4
private theorem endpoint_15_69_window_6 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 6 2 208489644374602239 = some 208489644374602239 := by decide +kernel
private theorem endpoint_15_69_prefix_8 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 8 195173709039510041 = some 208489644374602239 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 6 2 195173709039510041 208489644374602239 208489644374602239 endpoint_15_69_prefix_6 endpoint_15_69_window_6
private theorem endpoint_15_69_window_8 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 8 2 208489644374602239 = some 208489644374602239 := by decide +kernel
private theorem endpoint_15_69_prefix_10 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 10 195173709039510041 = some 208489644374602239 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 8 2 195173709039510041 208489644374602239 208489644374602239 endpoint_15_69_prefix_8 endpoint_15_69_window_8
private theorem endpoint_15_69_window_10 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 10 2 208489644374602239 = some 208489644374602239 := by decide +kernel
private theorem endpoint_15_69_prefix_12 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 12 195173709039510041 = some 208489644374602239 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 10 2 195173709039510041 208489644374602239 208489644374602239 endpoint_15_69_prefix_10 endpoint_15_69_window_10
private theorem endpoint_15_69_window_12 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 12 2 208489644374602239 = some 208489644374602239 := by decide +kernel
private theorem endpoint_15_69_prefix_14 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 14 195173709039510041 = some 208489644374602239 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 12 2 195173709039510041 208489644374602239 208489644374602239 endpoint_15_69_prefix_12 endpoint_15_69_window_12

def endpoint_15_69 : CertifiedEndpoint :=
  ⟨⟨15, 69, 1617⟩, 208489644374602239, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_15_69_flag endpoint_15_69_sources 14 195173709039510041 208489644374602239 rfl endpoint_15_69_base endpoint_15_69_prefix_14) (by decide)⟩
private def endpoint_15_70_flag : Flag := ⟨15, 70, 1542⟩
private def endpoint_15_70_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_15_70_base : receiptBase endpoint_15_70_flag endpoint_15_70_sources = some 187510424856683055 := by decide +kernel
private theorem endpoint_15_70_window_0 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 2 187510424856683055 = some 207591421542417696 := by decide +kernel
private theorem endpoint_15_70_window_2 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 2 2 207591421542417696 = some 207591421542417696 := by decide +kernel
private theorem endpoint_15_70_prefix_4 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 4 187510424856683055 = some 207591421542417696 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 2 2 187510424856683055 207591421542417696 207591421542417696 endpoint_15_70_window_0 endpoint_15_70_window_2
private theorem endpoint_15_70_window_4 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 4 2 207591421542417696 = some 207591421542417696 := by decide +kernel
private theorem endpoint_15_70_prefix_6 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 6 187510424856683055 = some 207591421542417696 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 4 2 187510424856683055 207591421542417696 207591421542417696 endpoint_15_70_prefix_4 endpoint_15_70_window_4
private theorem endpoint_15_70_window_6 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 6 2 207591421542417696 = some 207591421542417696 := by decide +kernel
private theorem endpoint_15_70_prefix_8 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 8 187510424856683055 = some 207591421542417696 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 6 2 187510424856683055 207591421542417696 207591421542417696 endpoint_15_70_prefix_6 endpoint_15_70_window_6
private theorem endpoint_15_70_window_8 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 8 2 207591421542417696 = some 207591421542417696 := by decide +kernel
private theorem endpoint_15_70_prefix_10 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 10 187510424856683055 = some 207591421542417696 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 8 2 187510424856683055 207591421542417696 207591421542417696 endpoint_15_70_prefix_8 endpoint_15_70_window_8
private theorem endpoint_15_70_window_10 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 10 2 207591421542417696 = some 207591421542417696 := by decide +kernel
private theorem endpoint_15_70_prefix_12 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 12 187510424856683055 = some 207591421542417696 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 10 2 187510424856683055 207591421542417696 207591421542417696 endpoint_15_70_prefix_10 endpoint_15_70_window_10
private theorem endpoint_15_70_window_12 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 12 2 207591421542417696 = some 207591421542417696 := by decide +kernel
private theorem endpoint_15_70_prefix_14 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 14 187510424856683055 = some 207591421542417696 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 12 2 187510424856683055 207591421542417696 207591421542417696 endpoint_15_70_prefix_12 endpoint_15_70_window_12

def endpoint_15_70 : CertifiedEndpoint :=
  ⟨⟨15, 70, 1542⟩, 207591421542417696, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_15_70_flag endpoint_15_70_sources 14 187510424856683055 207591421542417696 rfl endpoint_15_70_base endpoint_15_70_prefix_14) (by decide)⟩
private def endpoint_15_71_flag : Flag := ⟨15, 71, 1464⟩
private def endpoint_15_71_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_15_71_base : receiptBase endpoint_15_71_flag endpoint_15_71_sources = some 182876130314107339 := by decide +kernel
private theorem endpoint_15_71_window_0 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 2 182876130314107339 = some 188971085914725646 := by decide +kernel
private theorem endpoint_15_71_window_2 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 2 2 188971085914725646 = some 188971085914725646 := by decide +kernel
private theorem endpoint_15_71_prefix_4 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 4 182876130314107339 = some 188971085914725646 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 2 2 182876130314107339 188971085914725646 188971085914725646 endpoint_15_71_window_0 endpoint_15_71_window_2
private theorem endpoint_15_71_window_4 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 4 2 188971085914725646 = some 188971085914725646 := by decide +kernel
private theorem endpoint_15_71_prefix_6 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 6 182876130314107339 = some 188971085914725646 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 4 2 182876130314107339 188971085914725646 188971085914725646 endpoint_15_71_prefix_4 endpoint_15_71_window_4
private theorem endpoint_15_71_window_6 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 6 2 188971085914725646 = some 188971085914725646 := by decide +kernel
private theorem endpoint_15_71_prefix_8 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 8 182876130314107339 = some 188971085914725646 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 6 2 182876130314107339 188971085914725646 188971085914725646 endpoint_15_71_prefix_6 endpoint_15_71_window_6
private theorem endpoint_15_71_window_8 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 8 2 188971085914725646 = some 188971085914725646 := by decide +kernel
private theorem endpoint_15_71_prefix_10 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 10 182876130314107339 = some 188971085914725646 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 8 2 182876130314107339 188971085914725646 188971085914725646 endpoint_15_71_prefix_8 endpoint_15_71_window_8
private theorem endpoint_15_71_window_10 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 10 2 188971085914725646 = some 188971085914725646 := by decide +kernel
private theorem endpoint_15_71_prefix_12 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 12 182876130314107339 = some 188971085914725646 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 10 2 182876130314107339 188971085914725646 188971085914725646 endpoint_15_71_prefix_10 endpoint_15_71_window_10
private theorem endpoint_15_71_window_12 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 12 2 188971085914725646 = some 188971085914725646 := by decide +kernel
private theorem endpoint_15_71_prefix_14 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 14 182876130314107339 = some 188971085914725646 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 12 2 182876130314107339 188971085914725646 188971085914725646 endpoint_15_71_prefix_12 endpoint_15_71_window_12

def endpoint_15_71 : CertifiedEndpoint :=
  ⟨⟨15, 71, 1464⟩, 188971085914725646, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_15_71_flag endpoint_15_71_sources 14 182876130314107339 188971085914725646 rfl endpoint_15_71_base endpoint_15_71_prefix_14) (by decide)⟩
private def endpoint_15_72_flag : Flag := ⟨15, 72, 1384⟩
private def endpoint_15_72_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_15_72_base : receiptBase endpoint_15_72_flag endpoint_15_72_sources = some 175143680226576993 := by decide +kernel
private theorem endpoint_15_72_window_0 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 2 175143680226576993 = some 186100581863620518 := by decide +kernel
private theorem endpoint_15_72_window_2 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 2 2 186100581863620518 = some 186100581863620518 := by decide +kernel
private theorem endpoint_15_72_prefix_4 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 4 175143680226576993 = some 186100581863620518 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 2 2 175143680226576993 186100581863620518 186100581863620518 endpoint_15_72_window_0 endpoint_15_72_window_2
private theorem endpoint_15_72_window_4 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 4 2 186100581863620518 = some 186100581863620518 := by decide +kernel
private theorem endpoint_15_72_prefix_6 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 6 175143680226576993 = some 186100581863620518 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 4 2 175143680226576993 186100581863620518 186100581863620518 endpoint_15_72_prefix_4 endpoint_15_72_window_4
private theorem endpoint_15_72_window_6 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 6 2 186100581863620518 = some 186100581863620518 := by decide +kernel
private theorem endpoint_15_72_prefix_8 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 8 175143680226576993 = some 186100581863620518 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 6 2 175143680226576993 186100581863620518 186100581863620518 endpoint_15_72_prefix_6 endpoint_15_72_window_6
private theorem endpoint_15_72_window_8 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 8 2 186100581863620518 = some 186100581863620518 := by decide +kernel
private theorem endpoint_15_72_prefix_10 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 10 175143680226576993 = some 186100581863620518 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 8 2 175143680226576993 186100581863620518 186100581863620518 endpoint_15_72_prefix_8 endpoint_15_72_window_8
private theorem endpoint_15_72_window_10 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 10 2 186100581863620518 = some 186100581863620518 := by decide +kernel
private theorem endpoint_15_72_prefix_12 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 12 175143680226576993 = some 186100581863620518 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 10 2 175143680226576993 186100581863620518 186100581863620518 endpoint_15_72_prefix_10 endpoint_15_72_window_10
private theorem endpoint_15_72_window_12 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 12 2 186100581863620518 = some 186100581863620518 := by decide +kernel
private theorem endpoint_15_72_prefix_14 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 14 175143680226576993 = some 186100581863620518 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 12 2 175143680226576993 186100581863620518 186100581863620518 endpoint_15_72_prefix_12 endpoint_15_72_window_12

def endpoint_15_72 : CertifiedEndpoint :=
  ⟨⟨15, 72, 1384⟩, 186100581863620518, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_15_72_flag endpoint_15_72_sources 14 175143680226576993 186100581863620518 rfl endpoint_15_72_base endpoint_15_72_prefix_14) (by decide)⟩
private def endpoint_15_73_flag : Flag := ⟨15, 73, 1302⟩
private def endpoint_15_73_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_15_73_base : receiptBase endpoint_15_73_flag endpoint_15_73_sources = some 167307511548039100 := by decide +kernel
private theorem endpoint_15_73_window_0 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 2 167307511548039100 = some 179707764505167177 := by decide +kernel
private theorem endpoint_15_73_window_2 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 2 2 179707764505167177 = some 179707764505167177 := by decide +kernel
private theorem endpoint_15_73_prefix_4 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 4 167307511548039100 = some 179707764505167177 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 2 2 167307511548039100 179707764505167177 179707764505167177 endpoint_15_73_window_0 endpoint_15_73_window_2
private theorem endpoint_15_73_window_4 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 4 2 179707764505167177 = some 179707764505167177 := by decide +kernel
private theorem endpoint_15_73_prefix_6 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 6 167307511548039100 = some 179707764505167177 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 4 2 167307511548039100 179707764505167177 179707764505167177 endpoint_15_73_prefix_4 endpoint_15_73_window_4
private theorem endpoint_15_73_window_6 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 6 2 179707764505167177 = some 179707764505167177 := by decide +kernel
private theorem endpoint_15_73_prefix_8 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 8 167307511548039100 = some 179707764505167177 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 6 2 167307511548039100 179707764505167177 179707764505167177 endpoint_15_73_prefix_6 endpoint_15_73_window_6
private theorem endpoint_15_73_window_8 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 8 2 179707764505167177 = some 179707764505167177 := by decide +kernel
private theorem endpoint_15_73_prefix_10 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 10 167307511548039100 = some 179707764505167177 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 8 2 167307511548039100 179707764505167177 179707764505167177 endpoint_15_73_prefix_8 endpoint_15_73_window_8
private theorem endpoint_15_73_window_10 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 10 2 179707764505167177 = some 179707764505167177 := by decide +kernel
private theorem endpoint_15_73_prefix_12 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 12 167307511548039100 = some 179707764505167177 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 10 2 167307511548039100 179707764505167177 179707764505167177 endpoint_15_73_prefix_10 endpoint_15_73_window_10
private theorem endpoint_15_73_window_12 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 12 2 179707764505167177 = some 179707764505167177 := by decide +kernel
private theorem endpoint_15_73_prefix_14 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 14 167307511548039100 = some 179707764505167177 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 12 2 167307511548039100 179707764505167177 179707764505167177 endpoint_15_73_prefix_12 endpoint_15_73_window_12

def endpoint_15_73 : CertifiedEndpoint :=
  ⟨⟨15, 73, 1302⟩, 179707764505167177, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_15_73_flag endpoint_15_73_sources 14 167307511548039100 179707764505167177 rfl endpoint_15_73_base endpoint_15_73_prefix_14) (by decide)⟩
private def endpoint_15_74_flag : Flag := ⟨15, 74, 1217⟩
private def endpoint_15_74_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_15_74_base : receiptBase endpoint_15_74_flag endpoint_15_74_sources = some 159450957695648400 := by decide +kernel
private theorem endpoint_15_74_window_0 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 2 159450957695648400 = some 168483993381454686 := by decide +kernel
private theorem endpoint_15_74_window_2 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 2 2 168483993381454686 = some 168483993381454686 := by decide +kernel
private theorem endpoint_15_74_prefix_4 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 4 159450957695648400 = some 168483993381454686 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 2 2 159450957695648400 168483993381454686 168483993381454686 endpoint_15_74_window_0 endpoint_15_74_window_2
private theorem endpoint_15_74_window_4 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 4 2 168483993381454686 = some 168483993381454686 := by decide +kernel
private theorem endpoint_15_74_prefix_6 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 6 159450957695648400 = some 168483993381454686 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 4 2 159450957695648400 168483993381454686 168483993381454686 endpoint_15_74_prefix_4 endpoint_15_74_window_4
private theorem endpoint_15_74_window_6 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 6 2 168483993381454686 = some 168483993381454686 := by decide +kernel
private theorem endpoint_15_74_prefix_8 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 8 159450957695648400 = some 168483993381454686 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 6 2 159450957695648400 168483993381454686 168483993381454686 endpoint_15_74_prefix_6 endpoint_15_74_window_6
private theorem endpoint_15_74_window_8 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 8 2 168483993381454686 = some 168483993381454686 := by decide +kernel
private theorem endpoint_15_74_prefix_10 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 10 159450957695648400 = some 168483993381454686 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 8 2 159450957695648400 168483993381454686 168483993381454686 endpoint_15_74_prefix_8 endpoint_15_74_window_8
private theorem endpoint_15_74_window_10 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 10 2 168483993381454686 = some 168483993381454686 := by decide +kernel
private theorem endpoint_15_74_prefix_12 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 12 159450957695648400 = some 168483993381454686 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 10 2 159450957695648400 168483993381454686 168483993381454686 endpoint_15_74_prefix_10 endpoint_15_74_window_10
private theorem endpoint_15_74_window_12 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 12 2 168483993381454686 = some 168483993381454686 := by decide +kernel
private theorem endpoint_15_74_prefix_14 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 14 159450957695648400 = some 168483993381454686 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 12 2 159450957695648400 168483993381454686 168483993381454686 endpoint_15_74_prefix_12 endpoint_15_74_window_12

def endpoint_15_74 : CertifiedEndpoint :=
  ⟨⟨15, 74, 1217⟩, 168483993381454686, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_15_74_flag endpoint_15_74_sources 14 159450957695648400 168483993381454686 rfl endpoint_15_74_base endpoint_15_74_prefix_14) (by decide)⟩
private def endpoint_15_75_flag : Flag := ⟨15, 75, 1129⟩
private def endpoint_15_75_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_15_75_base : receiptBase endpoint_15_75_flag endpoint_15_75_sources = some 151098767189567533 := by decide +kernel
private theorem endpoint_15_75_window_0 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 2 151098767189567533 = some 155039995106609580 := by decide +kernel
private theorem endpoint_15_75_window_2 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 2 2 155039995106609580 = some 155039995106609580 := by decide +kernel
private theorem endpoint_15_75_prefix_4 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 4 151098767189567533 = some 155039995106609580 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 2 2 151098767189567533 155039995106609580 155039995106609580 endpoint_15_75_window_0 endpoint_15_75_window_2
private theorem endpoint_15_75_window_4 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 4 2 155039995106609580 = some 155039995106609580 := by decide +kernel
private theorem endpoint_15_75_prefix_6 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 6 151098767189567533 = some 155039995106609580 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 4 2 151098767189567533 155039995106609580 155039995106609580 endpoint_15_75_prefix_4 endpoint_15_75_window_4
private theorem endpoint_15_75_window_6 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 6 2 155039995106609580 = some 155039995106609580 := by decide +kernel
private theorem endpoint_15_75_prefix_8 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 8 151098767189567533 = some 155039995106609580 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 6 2 151098767189567533 155039995106609580 155039995106609580 endpoint_15_75_prefix_6 endpoint_15_75_window_6
private theorem endpoint_15_75_window_8 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 8 2 155039995106609580 = some 155039995106609580 := by decide +kernel
private theorem endpoint_15_75_prefix_10 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 10 151098767189567533 = some 155039995106609580 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 8 2 151098767189567533 155039995106609580 155039995106609580 endpoint_15_75_prefix_8 endpoint_15_75_window_8
private theorem endpoint_15_75_window_10 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 10 2 155039995106609580 = some 155039995106609580 := by decide +kernel
private theorem endpoint_15_75_prefix_12 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 12 151098767189567533 = some 155039995106609580 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 10 2 151098767189567533 155039995106609580 155039995106609580 endpoint_15_75_prefix_10 endpoint_15_75_window_10
private theorem endpoint_15_75_window_12 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 12 2 155039995106609580 = some 155039995106609580 := by decide +kernel
private theorem endpoint_15_75_prefix_14 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 14 151098767189567533 = some 155039995106609580 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 12 2 151098767189567533 155039995106609580 155039995106609580 endpoint_15_75_prefix_12 endpoint_15_75_window_12

def endpoint_15_75 : CertifiedEndpoint :=
  ⟨⟨15, 75, 1129⟩, 155039995106609580, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_15_75_flag endpoint_15_75_sources 14 151098767189567533 155039995106609580 rfl endpoint_15_75_base endpoint_15_75_prefix_14) (by decide)⟩
def endpoint_15_76 : CertifiedEndpoint :=
  ⟨⟨15, 76, 1039⟩, 253958484170753819, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_77 : CertifiedEndpoint :=
  ⟨⟨15, 77, 946⟩, 233528917051035181, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_78 : CertifiedEndpoint :=
  ⟨⟨15, 78, 850⟩, 211612438079570470, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_79 : CertifiedEndpoint :=
  ⟨⟨15, 79, 752⟩, 188441264778143927, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_80 : CertifiedEndpoint :=
  ⟨⟨15, 80, 652⟩, 163992925318706452, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_81 : CertifiedEndpoint :=
  ⟨⟨15, 81, 548⟩, 137698116126793763, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_82 : CertifiedEndpoint :=
  ⟨⟨15, 82, 442⟩, 110066215902072542, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_83 : CertifiedEndpoint :=
  ⟨⟨15, 83, 334⟩, 81074752816493689, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_84 : CertifiedEndpoint :=
  ⟨⟨15, 84, 223⟩, 50416603254775963, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_85 : CertifiedEndpoint :=
  ⟨⟨15, 85, 109⟩, 18058059474845714, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_16 : CertifiedEndpoint :=
  ⟨⟨16, 16, 3539⟩, 124894706392041939, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_17 : CertifiedEndpoint :=
  ⟨⟨16, 17, 3515⟩, 128640981638736502, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_18 : CertifiedEndpoint :=
  ⟨⟨16, 18, 3491⟩, 132324170823476873, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_19 : CertifiedEndpoint :=
  ⟨⟨16, 19, 3467⟩, 145215654086908628, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_20 : CertifiedEndpoint :=
  ⟨⟨16, 20, 3442⟩, 157864946670830598, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_21 : CertifiedEndpoint :=
  ⟨⟨16, 21, 3417⟩, 170310085795543366, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_22 : CertifiedEndpoint :=
  ⟨⟨16, 22, 3392⟩, 182551071461046932, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_23 : CertifiedEndpoint :=
  ⟨⟨16, 23, 3366⟩, 194529851402020203, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_24 : CertifiedEndpoint :=
  ⟨⟨16, 24, 3340⟩, 206296471865776068, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_25 : CertifiedEndpoint :=
  ⟨⟨16, 25, 3314⟩, 217850932852314527, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_26 : CertifiedEndpoint :=
  ⟨⟨16, 26, 3287⟩, 229123173069302181, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_27 : CertifiedEndpoint :=
  ⟨⟨16, 27, 3259⟩, 240101183489726724, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_28 : CertifiedEndpoint :=
  ⟨⟨16, 28, 3231⟩, 250851022396917453, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_16_29_flag : Flag := ⟨16, 29, 3203⟩
private def endpoint_16_29_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_29_base : receiptBase endpoint_16_29_flag endpoint_16_29_sources = some 175624958338864011 := by decide +kernel
private theorem endpoint_16_29_window_0 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 2 175624958338864011 = some 175624958338864011 := by decide +kernel
private theorem endpoint_16_29_window_2 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 2 2 175624958338864011 = some 175624958338864011 := by decide +kernel
private theorem endpoint_16_29_prefix_4 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 4 175624958338864011 = some 175624958338864011 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 2 2 175624958338864011 175624958338864011 175624958338864011 endpoint_16_29_window_0 endpoint_16_29_window_2
private theorem endpoint_16_29_window_4 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 4 2 175624958338864011 = some 175624958338864011 := by decide +kernel
private theorem endpoint_16_29_prefix_6 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 6 175624958338864011 = some 175624958338864011 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 4 2 175624958338864011 175624958338864011 175624958338864011 endpoint_16_29_prefix_4 endpoint_16_29_window_4
private theorem endpoint_16_29_window_6 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 6 2 175624958338864011 = some 175624958338864011 := by decide +kernel
private theorem endpoint_16_29_prefix_8 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 8 175624958338864011 = some 175624958338864011 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 6 2 175624958338864011 175624958338864011 175624958338864011 endpoint_16_29_prefix_6 endpoint_16_29_window_6
private theorem endpoint_16_29_window_8 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 8 2 175624958338864011 = some 175624958338864011 := by decide +kernel
private theorem endpoint_16_29_prefix_10 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 10 175624958338864011 = some 175624958338864011 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 8 2 175624958338864011 175624958338864011 175624958338864011 endpoint_16_29_prefix_8 endpoint_16_29_window_8
private theorem endpoint_16_29_window_10 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 10 2 175624958338864011 = some 175624958338864011 := by decide +kernel
private theorem endpoint_16_29_prefix_12 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 12 175624958338864011 = some 175624958338864011 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 10 2 175624958338864011 175624958338864011 175624958338864011 endpoint_16_29_prefix_10 endpoint_16_29_window_10
private theorem endpoint_16_29_window_12 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 12 2 175624958338864011 = some 175624958338864011 := by decide +kernel
private theorem endpoint_16_29_prefix_14 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 14 175624958338864011 = some 175624958338864011 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 12 2 175624958338864011 175624958338864011 175624958338864011 endpoint_16_29_prefix_12 endpoint_16_29_window_12
private theorem endpoint_16_29_window_14 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 14 1 175624958338864011 = some 175624958338864011 := by decide +kernel
private theorem endpoint_16_29_prefix_15 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 15 175624958338864011 = some 175624958338864011 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 14 1 175624958338864011 175624958338864011 175624958338864011 endpoint_16_29_prefix_14 endpoint_16_29_window_14

def endpoint_16_29 : CertifiedEndpoint :=
  ⟨⟨16, 29, 3203⟩, 175624958338864011, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_29_flag endpoint_16_29_sources 15 175624958338864011 175624958338864011 rfl endpoint_16_29_base endpoint_16_29_prefix_15) (by decide)⟩
private def endpoint_16_30_flag : Flag := ⟨16, 30, 3174⟩
private def endpoint_16_30_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_30_base : receiptBase endpoint_16_30_flag endpoint_16_30_sources = some 179012261770794529 := by decide +kernel
private theorem endpoint_16_30_window_0 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 2 179012261770794529 = some 179012261770794529 := by decide +kernel
private theorem endpoint_16_30_window_2 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 2 2 179012261770794529 = some 179012261770794529 := by decide +kernel
private theorem endpoint_16_30_prefix_4 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 4 179012261770794529 = some 179012261770794529 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 2 2 179012261770794529 179012261770794529 179012261770794529 endpoint_16_30_window_0 endpoint_16_30_window_2
private theorem endpoint_16_30_window_4 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 4 2 179012261770794529 = some 179012261770794529 := by decide +kernel
private theorem endpoint_16_30_prefix_6 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 6 179012261770794529 = some 179012261770794529 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 4 2 179012261770794529 179012261770794529 179012261770794529 endpoint_16_30_prefix_4 endpoint_16_30_window_4
private theorem endpoint_16_30_window_6 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 6 2 179012261770794529 = some 179012261770794529 := by decide +kernel
private theorem endpoint_16_30_prefix_8 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 8 179012261770794529 = some 179012261770794529 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 6 2 179012261770794529 179012261770794529 179012261770794529 endpoint_16_30_prefix_6 endpoint_16_30_window_6
private theorem endpoint_16_30_window_8 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 8 2 179012261770794529 = some 179012261770794529 := by decide +kernel
private theorem endpoint_16_30_prefix_10 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 10 179012261770794529 = some 179012261770794529 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 8 2 179012261770794529 179012261770794529 179012261770794529 endpoint_16_30_prefix_8 endpoint_16_30_window_8
private theorem endpoint_16_30_window_10 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 10 2 179012261770794529 = some 179012261770794529 := by decide +kernel
private theorem endpoint_16_30_prefix_12 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 12 179012261770794529 = some 179012261770794529 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 10 2 179012261770794529 179012261770794529 179012261770794529 endpoint_16_30_prefix_10 endpoint_16_30_window_10
private theorem endpoint_16_30_window_12 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 12 2 179012261770794529 = some 179012261770794529 := by decide +kernel
private theorem endpoint_16_30_prefix_14 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 14 179012261770794529 = some 179012261770794529 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 12 2 179012261770794529 179012261770794529 179012261770794529 endpoint_16_30_prefix_12 endpoint_16_30_window_12
private theorem endpoint_16_30_window_14 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 14 1 179012261770794529 = some 179012261770794529 := by decide +kernel
private theorem endpoint_16_30_prefix_15 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 15 179012261770794529 = some 179012261770794529 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 14 1 179012261770794529 179012261770794529 179012261770794529 endpoint_16_30_prefix_14 endpoint_16_30_window_14

def endpoint_16_30 : CertifiedEndpoint :=
  ⟨⟨16, 30, 3174⟩, 179012261770794529, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_30_flag endpoint_16_30_sources 15 179012261770794529 179012261770794529 rfl endpoint_16_30_base endpoint_16_30_prefix_15) (by decide)⟩
private def endpoint_16_31_flag : Flag := ⟨16, 31, 3144⟩
private def endpoint_16_31_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_31_base : receiptBase endpoint_16_31_flag endpoint_16_31_sources = some 182252515984841911 := by decide +kernel
private theorem endpoint_16_31_window_0 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 2 182252515984841911 = some 182252515984841911 := by decide +kernel
private theorem endpoint_16_31_window_2 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 2 2 182252515984841911 = some 182252515984841911 := by decide +kernel
private theorem endpoint_16_31_prefix_4 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 4 182252515984841911 = some 182252515984841911 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 2 2 182252515984841911 182252515984841911 182252515984841911 endpoint_16_31_window_0 endpoint_16_31_window_2
private theorem endpoint_16_31_window_4 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 4 2 182252515984841911 = some 182252515984841911 := by decide +kernel
private theorem endpoint_16_31_prefix_6 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 6 182252515984841911 = some 182252515984841911 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 4 2 182252515984841911 182252515984841911 182252515984841911 endpoint_16_31_prefix_4 endpoint_16_31_window_4
private theorem endpoint_16_31_window_6 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 6 2 182252515984841911 = some 182252515984841911 := by decide +kernel
private theorem endpoint_16_31_prefix_8 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 8 182252515984841911 = some 182252515984841911 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 6 2 182252515984841911 182252515984841911 182252515984841911 endpoint_16_31_prefix_6 endpoint_16_31_window_6
private theorem endpoint_16_31_window_8 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 8 2 182252515984841911 = some 182252515984841911 := by decide +kernel
private theorem endpoint_16_31_prefix_10 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 10 182252515984841911 = some 182252515984841911 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 8 2 182252515984841911 182252515984841911 182252515984841911 endpoint_16_31_prefix_8 endpoint_16_31_window_8
private theorem endpoint_16_31_window_10 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 10 2 182252515984841911 = some 182252515984841911 := by decide +kernel
private theorem endpoint_16_31_prefix_12 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 12 182252515984841911 = some 182252515984841911 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 10 2 182252515984841911 182252515984841911 182252515984841911 endpoint_16_31_prefix_10 endpoint_16_31_window_10
private theorem endpoint_16_31_window_12 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 12 2 182252515984841911 = some 182252515984841911 := by decide +kernel
private theorem endpoint_16_31_prefix_14 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 14 182252515984841911 = some 182252515984841911 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 12 2 182252515984841911 182252515984841911 182252515984841911 endpoint_16_31_prefix_12 endpoint_16_31_window_12
private theorem endpoint_16_31_window_14 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 14 1 182252515984841911 = some 182252515984841911 := by decide +kernel
private theorem endpoint_16_31_prefix_15 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 15 182252515984841911 = some 182252515984841911 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 14 1 182252515984841911 182252515984841911 182252515984841911 endpoint_16_31_prefix_14 endpoint_16_31_window_14

def endpoint_16_31 : CertifiedEndpoint :=
  ⟨⟨16, 31, 3144⟩, 182252515984841911, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_31_flag endpoint_16_31_sources 15 182252515984841911 182252515984841911 rfl endpoint_16_31_base endpoint_16_31_prefix_15) (by decide)⟩
private def endpoint_16_32_flag : Flag := ⟨16, 32, 3114⟩
private def endpoint_16_32_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_32_base : receiptBase endpoint_16_32_flag endpoint_16_32_sources = some 185399771689585111 := by decide +kernel
private theorem endpoint_16_32_window_0 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 2 185399771689585111 = some 185399771689585111 := by decide +kernel
private theorem endpoint_16_32_window_2 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 2 2 185399771689585111 = some 185399771689585111 := by decide +kernel
private theorem endpoint_16_32_prefix_4 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 4 185399771689585111 = some 185399771689585111 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 2 2 185399771689585111 185399771689585111 185399771689585111 endpoint_16_32_window_0 endpoint_16_32_window_2
private theorem endpoint_16_32_window_4 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 4 2 185399771689585111 = some 185399771689585111 := by decide +kernel
private theorem endpoint_16_32_prefix_6 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 6 185399771689585111 = some 185399771689585111 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 4 2 185399771689585111 185399771689585111 185399771689585111 endpoint_16_32_prefix_4 endpoint_16_32_window_4
private theorem endpoint_16_32_window_6 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 6 2 185399771689585111 = some 185399771689585111 := by decide +kernel
private theorem endpoint_16_32_prefix_8 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 8 185399771689585111 = some 185399771689585111 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 6 2 185399771689585111 185399771689585111 185399771689585111 endpoint_16_32_prefix_6 endpoint_16_32_window_6
private theorem endpoint_16_32_window_8 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 8 2 185399771689585111 = some 185399771689585111 := by decide +kernel
private theorem endpoint_16_32_prefix_10 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 10 185399771689585111 = some 185399771689585111 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 8 2 185399771689585111 185399771689585111 185399771689585111 endpoint_16_32_prefix_8 endpoint_16_32_window_8
private theorem endpoint_16_32_window_10 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 10 2 185399771689585111 = some 185399771689585111 := by decide +kernel
private theorem endpoint_16_32_prefix_12 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 12 185399771689585111 = some 185399771689585111 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 10 2 185399771689585111 185399771689585111 185399771689585111 endpoint_16_32_prefix_10 endpoint_16_32_window_10
private theorem endpoint_16_32_window_12 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 12 2 185399771689585111 = some 185399771689585111 := by decide +kernel
private theorem endpoint_16_32_prefix_14 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 14 185399771689585111 = some 185399771689585111 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 12 2 185399771689585111 185399771689585111 185399771689585111 endpoint_16_32_prefix_12 endpoint_16_32_window_12
private theorem endpoint_16_32_window_14 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 14 1 185399771689585111 = some 185399771689585111 := by decide +kernel
private theorem endpoint_16_32_prefix_15 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 15 185399771689585111 = some 185399771689585111 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 14 1 185399771689585111 185399771689585111 185399771689585111 endpoint_16_32_prefix_14 endpoint_16_32_window_14

def endpoint_16_32 : CertifiedEndpoint :=
  ⟨⟨16, 32, 3114⟩, 185399771689585111, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_32_flag endpoint_16_32_sources 15 185399771689585111 185399771689585111 rfl endpoint_16_32_base endpoint_16_32_prefix_15) (by decide)⟩
private def endpoint_16_33_flag : Flag := ⟨16, 33, 3084⟩
private def endpoint_16_33_sources : Sources := ⟨contact27, contact03, contact25⟩
private theorem endpoint_16_33_base : receiptBase endpoint_16_33_flag endpoint_16_33_sources = some 190177304303425889 := by decide +kernel
private theorem endpoint_16_33_window_0 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 2 190177304303425889 = some 190177304303425889 := by decide +kernel
private theorem endpoint_16_33_window_2 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 2 2 190177304303425889 = some 190177304303425889 := by decide +kernel
private theorem endpoint_16_33_prefix_4 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 4 190177304303425889 = some 190177304303425889 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 2 2 190177304303425889 190177304303425889 190177304303425889 endpoint_16_33_window_0 endpoint_16_33_window_2
private theorem endpoint_16_33_window_4 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 4 2 190177304303425889 = some 190177304303425889 := by decide +kernel
private theorem endpoint_16_33_prefix_6 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 6 190177304303425889 = some 190177304303425889 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 4 2 190177304303425889 190177304303425889 190177304303425889 endpoint_16_33_prefix_4 endpoint_16_33_window_4
private theorem endpoint_16_33_window_6 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 6 2 190177304303425889 = some 190177304303425889 := by decide +kernel
private theorem endpoint_16_33_prefix_8 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 8 190177304303425889 = some 190177304303425889 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 6 2 190177304303425889 190177304303425889 190177304303425889 endpoint_16_33_prefix_6 endpoint_16_33_window_6
private theorem endpoint_16_33_window_8 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 8 2 190177304303425889 = some 190177304303425889 := by decide +kernel
private theorem endpoint_16_33_prefix_10 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 10 190177304303425889 = some 190177304303425889 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 8 2 190177304303425889 190177304303425889 190177304303425889 endpoint_16_33_prefix_8 endpoint_16_33_window_8
private theorem endpoint_16_33_window_10 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 10 2 190177304303425889 = some 190177304303425889 := by decide +kernel
private theorem endpoint_16_33_prefix_12 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 12 190177304303425889 = some 190177304303425889 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 10 2 190177304303425889 190177304303425889 190177304303425889 endpoint_16_33_prefix_10 endpoint_16_33_window_10
private theorem endpoint_16_33_window_12 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 12 2 190177304303425889 = some 190177304303425889 := by decide +kernel
private theorem endpoint_16_33_prefix_14 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 14 190177304303425889 = some 190177304303425889 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 12 2 190177304303425889 190177304303425889 190177304303425889 endpoint_16_33_prefix_12 endpoint_16_33_window_12
private theorem endpoint_16_33_window_14 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 14 1 190177304303425889 = some 190177304303425889 := by decide +kernel
private theorem endpoint_16_33_prefix_15 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 15 190177304303425889 = some 190177304303425889 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 14 1 190177304303425889 190177304303425889 190177304303425889 endpoint_16_33_prefix_14 endpoint_16_33_window_14

def endpoint_16_33 : CertifiedEndpoint :=
  ⟨⟨16, 33, 3084⟩, 190177304303425889, .terminal ⟨contact27, contact03, contact25⟩ (finish_receipt_window endpoint_16_33_flag endpoint_16_33_sources 15 190177304303425889 190177304303425889 rfl endpoint_16_33_base endpoint_16_33_prefix_15) (by decide)⟩
private def endpoint_16_34_flag : Flag := ⟨16, 34, 3052⟩
private def endpoint_16_34_sources : Sources := ⟨contact25, contact03, contact25⟩
private theorem endpoint_16_34_base : receiptBase endpoint_16_34_flag endpoint_16_34_sources = some 193206335485718146 := by decide +kernel
private theorem endpoint_16_34_window_0 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 2 193206335485718146 = some 193206335485718146 := by decide +kernel
private theorem endpoint_16_34_window_2 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 2 2 193206335485718146 = some 193206335485718146 := by decide +kernel
private theorem endpoint_16_34_prefix_4 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 4 193206335485718146 = some 193206335485718146 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 2 2 193206335485718146 193206335485718146 193206335485718146 endpoint_16_34_window_0 endpoint_16_34_window_2
private theorem endpoint_16_34_window_4 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 4 2 193206335485718146 = some 193206335485718146 := by decide +kernel
private theorem endpoint_16_34_prefix_6 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 6 193206335485718146 = some 193206335485718146 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 4 2 193206335485718146 193206335485718146 193206335485718146 endpoint_16_34_prefix_4 endpoint_16_34_window_4
private theorem endpoint_16_34_window_6 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 6 2 193206335485718146 = some 193206335485718146 := by decide +kernel
private theorem endpoint_16_34_prefix_8 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 8 193206335485718146 = some 193206335485718146 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 6 2 193206335485718146 193206335485718146 193206335485718146 endpoint_16_34_prefix_6 endpoint_16_34_window_6
private theorem endpoint_16_34_window_8 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 8 2 193206335485718146 = some 193206335485718146 := by decide +kernel
private theorem endpoint_16_34_prefix_10 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 10 193206335485718146 = some 193206335485718146 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 8 2 193206335485718146 193206335485718146 193206335485718146 endpoint_16_34_prefix_8 endpoint_16_34_window_8
private theorem endpoint_16_34_window_10 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 10 2 193206335485718146 = some 193206335485718146 := by decide +kernel
private theorem endpoint_16_34_prefix_12 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 12 193206335485718146 = some 193206335485718146 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 10 2 193206335485718146 193206335485718146 193206335485718146 endpoint_16_34_prefix_10 endpoint_16_34_window_10
private theorem endpoint_16_34_window_12 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 12 2 193206335485718146 = some 193206335485718146 := by decide +kernel
private theorem endpoint_16_34_prefix_14 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 14 193206335485718146 = some 193206335485718146 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 12 2 193206335485718146 193206335485718146 193206335485718146 endpoint_16_34_prefix_12 endpoint_16_34_window_12
private theorem endpoint_16_34_window_14 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 14 1 193206335485718146 = some 193206335485718146 := by decide +kernel
private theorem endpoint_16_34_prefix_15 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 15 193206335485718146 = some 193206335485718146 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 14 1 193206335485718146 193206335485718146 193206335485718146 endpoint_16_34_prefix_14 endpoint_16_34_window_14

def endpoint_16_34 : CertifiedEndpoint :=
  ⟨⟨16, 34, 3052⟩, 193206335485718146, .terminal ⟨contact25, contact03, contact25⟩ (finish_receipt_window endpoint_16_34_flag endpoint_16_34_sources 15 193206335485718146 193206335485718146 rfl endpoint_16_34_base endpoint_16_34_prefix_15) (by decide)⟩
private def endpoint_16_35_flag : Flag := ⟨16, 35, 3020⟩
private def endpoint_16_35_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_35_base : receiptBase endpoint_16_35_flag endpoint_16_35_sources = some 197399750870246127 := by decide +kernel
private theorem endpoint_16_35_window_0 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 2 197399750870246127 = some 197399750870246127 := by decide +kernel
private theorem endpoint_16_35_window_2 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 2 2 197399750870246127 = some 197399750870246127 := by decide +kernel
private theorem endpoint_16_35_prefix_4 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 4 197399750870246127 = some 197399750870246127 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 2 2 197399750870246127 197399750870246127 197399750870246127 endpoint_16_35_window_0 endpoint_16_35_window_2
private theorem endpoint_16_35_window_4 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 4 2 197399750870246127 = some 197399750870246127 := by decide +kernel
private theorem endpoint_16_35_prefix_6 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 6 197399750870246127 = some 197399750870246127 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 4 2 197399750870246127 197399750870246127 197399750870246127 endpoint_16_35_prefix_4 endpoint_16_35_window_4
private theorem endpoint_16_35_window_6 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 6 2 197399750870246127 = some 197399750870246127 := by decide +kernel
private theorem endpoint_16_35_prefix_8 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 8 197399750870246127 = some 197399750870246127 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 6 2 197399750870246127 197399750870246127 197399750870246127 endpoint_16_35_prefix_6 endpoint_16_35_window_6
private theorem endpoint_16_35_window_8 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 8 2 197399750870246127 = some 197399750870246127 := by decide +kernel
private theorem endpoint_16_35_prefix_10 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 10 197399750870246127 = some 197399750870246127 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 8 2 197399750870246127 197399750870246127 197399750870246127 endpoint_16_35_prefix_8 endpoint_16_35_window_8
private theorem endpoint_16_35_window_10 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 10 2 197399750870246127 = some 197399750870246127 := by decide +kernel
private theorem endpoint_16_35_prefix_12 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 12 197399750870246127 = some 197399750870246127 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 10 2 197399750870246127 197399750870246127 197399750870246127 endpoint_16_35_prefix_10 endpoint_16_35_window_10
private theorem endpoint_16_35_window_12 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 12 2 197399750870246127 = some 197399750870246127 := by decide +kernel
private theorem endpoint_16_35_prefix_14 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 14 197399750870246127 = some 197399750870246127 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 12 2 197399750870246127 197399750870246127 197399750870246127 endpoint_16_35_prefix_12 endpoint_16_35_window_12
private theorem endpoint_16_35_window_14 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 14 1 197399750870246127 = some 197399750870246127 := by decide +kernel
private theorem endpoint_16_35_prefix_15 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 15 197399750870246127 = some 197399750870246127 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 14 1 197399750870246127 197399750870246127 197399750870246127 endpoint_16_35_prefix_14 endpoint_16_35_window_14

def endpoint_16_35 : CertifiedEndpoint :=
  ⟨⟨16, 35, 3020⟩, 197399750870246127, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_35_flag endpoint_16_35_sources 15 197399750870246127 197399750870246127 rfl endpoint_16_35_base endpoint_16_35_prefix_15) (by decide)⟩
private def endpoint_16_36_flag : Flag := ⟨16, 36, 2988⟩
private def endpoint_16_36_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_36_base : receiptBase endpoint_16_36_flag endpoint_16_36_sources = some 199935936006108979 := by decide +kernel
private theorem endpoint_16_36_window_0 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 2 199935936006108979 = some 199935936006108979 := by decide +kernel
private theorem endpoint_16_36_window_2 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 2 2 199935936006108979 = some 199935936006108979 := by decide +kernel
private theorem endpoint_16_36_prefix_4 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 4 199935936006108979 = some 199935936006108979 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 2 2 199935936006108979 199935936006108979 199935936006108979 endpoint_16_36_window_0 endpoint_16_36_window_2
private theorem endpoint_16_36_window_4 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 4 2 199935936006108979 = some 199935936006108979 := by decide +kernel
private theorem endpoint_16_36_prefix_6 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 6 199935936006108979 = some 199935936006108979 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 4 2 199935936006108979 199935936006108979 199935936006108979 endpoint_16_36_prefix_4 endpoint_16_36_window_4
private theorem endpoint_16_36_window_6 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 6 2 199935936006108979 = some 199935936006108979 := by decide +kernel
private theorem endpoint_16_36_prefix_8 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 8 199935936006108979 = some 199935936006108979 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 6 2 199935936006108979 199935936006108979 199935936006108979 endpoint_16_36_prefix_6 endpoint_16_36_window_6
private theorem endpoint_16_36_window_8 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 8 2 199935936006108979 = some 199935936006108979 := by decide +kernel
private theorem endpoint_16_36_prefix_10 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 10 199935936006108979 = some 199935936006108979 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 8 2 199935936006108979 199935936006108979 199935936006108979 endpoint_16_36_prefix_8 endpoint_16_36_window_8
private theorem endpoint_16_36_window_10 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 10 2 199935936006108979 = some 199935936006108979 := by decide +kernel
private theorem endpoint_16_36_prefix_12 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 12 199935936006108979 = some 199935936006108979 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 10 2 199935936006108979 199935936006108979 199935936006108979 endpoint_16_36_prefix_10 endpoint_16_36_window_10
private theorem endpoint_16_36_window_12 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 12 2 199935936006108979 = some 199935936006108979 := by decide +kernel
private theorem endpoint_16_36_prefix_14 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 14 199935936006108979 = some 199935936006108979 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 12 2 199935936006108979 199935936006108979 199935936006108979 endpoint_16_36_prefix_12 endpoint_16_36_window_12
private theorem endpoint_16_36_window_14 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 14 1 199935936006108979 = some 199935936006108979 := by decide +kernel
private theorem endpoint_16_36_prefix_15 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 15 199935936006108979 = some 199935936006108979 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 14 1 199935936006108979 199935936006108979 199935936006108979 endpoint_16_36_prefix_14 endpoint_16_36_window_14

def endpoint_16_36 : CertifiedEndpoint :=
  ⟨⟨16, 36, 2988⟩, 199935936006108979, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_36_flag endpoint_16_36_sources 15 199935936006108979 199935936006108979 rfl endpoint_16_36_base endpoint_16_36_prefix_15) (by decide)⟩
private def endpoint_16_37_flag : Flag := ⟨16, 37, 2954⟩
private def endpoint_16_37_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_37_base : receiptBase endpoint_16_37_flag endpoint_16_37_sources = some 202238968366982112 := by decide +kernel
private theorem endpoint_16_37_window_0 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 2 202238968366982112 = some 202238968366982112 := by decide +kernel
private theorem endpoint_16_37_window_2 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 2 2 202238968366982112 = some 202238968366982112 := by decide +kernel
private theorem endpoint_16_37_prefix_4 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 4 202238968366982112 = some 202238968366982112 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 2 2 202238968366982112 202238968366982112 202238968366982112 endpoint_16_37_window_0 endpoint_16_37_window_2
private theorem endpoint_16_37_window_4 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 4 2 202238968366982112 = some 202238968366982112 := by decide +kernel
private theorem endpoint_16_37_prefix_6 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 6 202238968366982112 = some 202238968366982112 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 4 2 202238968366982112 202238968366982112 202238968366982112 endpoint_16_37_prefix_4 endpoint_16_37_window_4
private theorem endpoint_16_37_window_6 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 6 2 202238968366982112 = some 202238968366982112 := by decide +kernel
private theorem endpoint_16_37_prefix_8 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 8 202238968366982112 = some 202238968366982112 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 6 2 202238968366982112 202238968366982112 202238968366982112 endpoint_16_37_prefix_6 endpoint_16_37_window_6
private theorem endpoint_16_37_window_8 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 8 2 202238968366982112 = some 202238968366982112 := by decide +kernel
private theorem endpoint_16_37_prefix_10 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 10 202238968366982112 = some 202238968366982112 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 8 2 202238968366982112 202238968366982112 202238968366982112 endpoint_16_37_prefix_8 endpoint_16_37_window_8
private theorem endpoint_16_37_window_10 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 10 2 202238968366982112 = some 202238968366982112 := by decide +kernel
private theorem endpoint_16_37_prefix_12 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 12 202238968366982112 = some 202238968366982112 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 10 2 202238968366982112 202238968366982112 202238968366982112 endpoint_16_37_prefix_10 endpoint_16_37_window_10
private theorem endpoint_16_37_window_12 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 12 2 202238968366982112 = some 202238968366982112 := by decide +kernel
private theorem endpoint_16_37_prefix_14 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 14 202238968366982112 = some 202238968366982112 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 12 2 202238968366982112 202238968366982112 202238968366982112 endpoint_16_37_prefix_12 endpoint_16_37_window_12
private theorem endpoint_16_37_window_14 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 14 1 202238968366982112 = some 202238968366982112 := by decide +kernel
private theorem endpoint_16_37_prefix_15 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 15 202238968366982112 = some 202238968366982112 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 14 1 202238968366982112 202238968366982112 202238968366982112 endpoint_16_37_prefix_14 endpoint_16_37_window_14

def endpoint_16_37 : CertifiedEndpoint :=
  ⟨⟨16, 37, 2954⟩, 202238968366982112, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_37_flag endpoint_16_37_sources 15 202238968366982112 202238968366982112 rfl endpoint_16_37_base endpoint_16_37_prefix_15) (by decide)⟩
private def endpoint_16_38_flag : Flag := ⟨16, 38, 2920⟩
private def endpoint_16_38_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_38_base : receiptBase endpoint_16_38_flag endpoint_16_38_sources = some 204437842236251942 := by decide +kernel
private theorem endpoint_16_38_window_0 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 2 204437842236251942 = some 204437842236251942 := by decide +kernel
private theorem endpoint_16_38_window_2 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 2 2 204437842236251942 = some 204437842236251942 := by decide +kernel
private theorem endpoint_16_38_prefix_4 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 4 204437842236251942 = some 204437842236251942 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 2 2 204437842236251942 204437842236251942 204437842236251942 endpoint_16_38_window_0 endpoint_16_38_window_2
private theorem endpoint_16_38_window_4 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 4 2 204437842236251942 = some 204437842236251942 := by decide +kernel
private theorem endpoint_16_38_prefix_6 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 6 204437842236251942 = some 204437842236251942 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 4 2 204437842236251942 204437842236251942 204437842236251942 endpoint_16_38_prefix_4 endpoint_16_38_window_4
private theorem endpoint_16_38_window_6 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 6 2 204437842236251942 = some 204437842236251942 := by decide +kernel
private theorem endpoint_16_38_prefix_8 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 8 204437842236251942 = some 204437842236251942 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 6 2 204437842236251942 204437842236251942 204437842236251942 endpoint_16_38_prefix_6 endpoint_16_38_window_6
private theorem endpoint_16_38_window_8 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 8 2 204437842236251942 = some 204437842236251942 := by decide +kernel
private theorem endpoint_16_38_prefix_10 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 10 204437842236251942 = some 204437842236251942 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 8 2 204437842236251942 204437842236251942 204437842236251942 endpoint_16_38_prefix_8 endpoint_16_38_window_8
private theorem endpoint_16_38_window_10 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 10 2 204437842236251942 = some 204437842236251942 := by decide +kernel
private theorem endpoint_16_38_prefix_12 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 12 204437842236251942 = some 204437842236251942 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 10 2 204437842236251942 204437842236251942 204437842236251942 endpoint_16_38_prefix_10 endpoint_16_38_window_10
private theorem endpoint_16_38_window_12 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 12 2 204437842236251942 = some 204437842236251942 := by decide +kernel
private theorem endpoint_16_38_prefix_14 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 14 204437842236251942 = some 204437842236251942 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 12 2 204437842236251942 204437842236251942 204437842236251942 endpoint_16_38_prefix_12 endpoint_16_38_window_12
private theorem endpoint_16_38_window_14 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 14 1 204437842236251942 = some 204437842236251942 := by decide +kernel
private theorem endpoint_16_38_prefix_15 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 15 204437842236251942 = some 204437842236251942 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 14 1 204437842236251942 204437842236251942 204437842236251942 endpoint_16_38_prefix_14 endpoint_16_38_window_14

def endpoint_16_38 : CertifiedEndpoint :=
  ⟨⟨16, 38, 2920⟩, 204437842236251942, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_38_flag endpoint_16_38_sources 15 204437842236251942 204437842236251942 rfl endpoint_16_38_base endpoint_16_38_prefix_15) (by decide)⟩
private def endpoint_16_39_flag : Flag := ⟨16, 39, 2886⟩
private def endpoint_16_39_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_39_base : receiptBase endpoint_16_39_flag endpoint_16_39_sources = some 207021878582009432 := by decide +kernel
private theorem endpoint_16_39_window_0 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 2 207021878582009432 = some 207021878582009432 := by decide +kernel
private theorem endpoint_16_39_window_2 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 2 2 207021878582009432 = some 207021878582009432 := by decide +kernel
private theorem endpoint_16_39_prefix_4 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 4 207021878582009432 = some 207021878582009432 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 2 2 207021878582009432 207021878582009432 207021878582009432 endpoint_16_39_window_0 endpoint_16_39_window_2
private theorem endpoint_16_39_window_4 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 4 2 207021878582009432 = some 207021878582009432 := by decide +kernel
private theorem endpoint_16_39_prefix_6 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 6 207021878582009432 = some 207021878582009432 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 4 2 207021878582009432 207021878582009432 207021878582009432 endpoint_16_39_prefix_4 endpoint_16_39_window_4
private theorem endpoint_16_39_window_6 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 6 2 207021878582009432 = some 207021878582009432 := by decide +kernel
private theorem endpoint_16_39_prefix_8 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 8 207021878582009432 = some 207021878582009432 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 6 2 207021878582009432 207021878582009432 207021878582009432 endpoint_16_39_prefix_6 endpoint_16_39_window_6
private theorem endpoint_16_39_window_8 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 8 2 207021878582009432 = some 207021878582009432 := by decide +kernel
private theorem endpoint_16_39_prefix_10 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 10 207021878582009432 = some 207021878582009432 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 8 2 207021878582009432 207021878582009432 207021878582009432 endpoint_16_39_prefix_8 endpoint_16_39_window_8
private theorem endpoint_16_39_window_10 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 10 2 207021878582009432 = some 207021878582009432 := by decide +kernel
private theorem endpoint_16_39_prefix_12 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 12 207021878582009432 = some 207021878582009432 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 10 2 207021878582009432 207021878582009432 207021878582009432 endpoint_16_39_prefix_10 endpoint_16_39_window_10
private theorem endpoint_16_39_window_12 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 12 2 207021878582009432 = some 207021878582009432 := by decide +kernel
private theorem endpoint_16_39_prefix_14 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 14 207021878582009432 = some 207021878582009432 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 12 2 207021878582009432 207021878582009432 207021878582009432 endpoint_16_39_prefix_12 endpoint_16_39_window_12
private theorem endpoint_16_39_window_14 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 14 1 207021878582009432 = some 207021878582009432 := by decide +kernel
private theorem endpoint_16_39_prefix_15 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 15 207021878582009432 = some 207021878582009432 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 14 1 207021878582009432 207021878582009432 207021878582009432 endpoint_16_39_prefix_14 endpoint_16_39_window_14

def endpoint_16_39 : CertifiedEndpoint :=
  ⟨⟨16, 39, 2886⟩, 207021878582009432, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_39_flag endpoint_16_39_sources 15 207021878582009432 207021878582009432 rfl endpoint_16_39_base endpoint_16_39_prefix_15) (by decide)⟩

def endpointBlock10 : List CertifiedEndpoint := [
  endpoint_15_32, endpoint_15_33, endpoint_15_34, endpoint_15_35, endpoint_15_36, endpoint_15_37,
  endpoint_15_38, endpoint_15_39, endpoint_15_40, endpoint_15_41, endpoint_15_42, endpoint_15_43,
  endpoint_15_44, endpoint_15_45, endpoint_15_46, endpoint_15_47, endpoint_15_48, endpoint_15_49,
  endpoint_15_50, endpoint_15_51, endpoint_15_52, endpoint_15_53, endpoint_15_54, endpoint_15_55,
  endpoint_15_56, endpoint_15_57, endpoint_15_58, endpoint_15_59, endpoint_15_60, endpoint_15_61,
  endpoint_15_62, endpoint_15_63, endpoint_15_64, endpoint_15_65, endpoint_15_66, endpoint_15_67,
  endpoint_15_68, endpoint_15_69, endpoint_15_70, endpoint_15_71, endpoint_15_72, endpoint_15_73,
  endpoint_15_74, endpoint_15_75, endpoint_15_76, endpoint_15_77, endpoint_15_78, endpoint_15_79,
  endpoint_15_80, endpoint_15_81, endpoint_15_82, endpoint_15_83, endpoint_15_84, endpoint_15_85,
  endpoint_16_16, endpoint_16_17, endpoint_16_18, endpoint_16_19, endpoint_16_20, endpoint_16_21,
  endpoint_16_22, endpoint_16_23, endpoint_16_24, endpoint_16_25, endpoint_16_26, endpoint_16_27,
  endpoint_16_28, endpoint_16_29, endpoint_16_30, endpoint_16_31, endpoint_16_32, endpoint_16_33,
  endpoint_16_34, endpoint_16_35, endpoint_16_36, endpoint_16_37, endpoint_16_38, endpoint_16_39
]

end ProximityPrize.SubmissionLower.Koala6844Receipts
