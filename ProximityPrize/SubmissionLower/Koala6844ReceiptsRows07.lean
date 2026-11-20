import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


private def endpoint_11_74_flag : Flag := ⟨11, 74, 2024⟩
private def endpoint_11_74_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_11_74_base : receiptBase endpoint_11_74_flag endpoint_11_74_sources = some 207501855247928844 := by decide +kernel
private theorem endpoint_11_74_window_0 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 2 207501855247928844 = some 207501855247928844 := by decide +kernel
private theorem endpoint_11_74_window_2 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 2 2 207501855247928844 = some 207501855247928844 := by decide +kernel
private theorem endpoint_11_74_prefix_4 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 4 207501855247928844 = some 207501855247928844 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 2 2 207501855247928844 207501855247928844 207501855247928844 endpoint_11_74_window_0 endpoint_11_74_window_2
private theorem endpoint_11_74_window_4 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 4 2 207501855247928844 = some 207501855247928844 := by decide +kernel
private theorem endpoint_11_74_prefix_6 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 6 207501855247928844 = some 207501855247928844 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 4 2 207501855247928844 207501855247928844 207501855247928844 endpoint_11_74_prefix_4 endpoint_11_74_window_4
private theorem endpoint_11_74_window_6 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 6 2 207501855247928844 = some 207501855247928844 := by decide +kernel
private theorem endpoint_11_74_prefix_8 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 8 207501855247928844 = some 207501855247928844 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 6 2 207501855247928844 207501855247928844 207501855247928844 endpoint_11_74_prefix_6 endpoint_11_74_window_6
private theorem endpoint_11_74_window_8 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 8 2 207501855247928844 = some 207501855247928844 := by decide +kernel
private theorem endpoint_11_74_prefix_10 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 10 207501855247928844 = some 207501855247928844 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 8 2 207501855247928844 207501855247928844 207501855247928844 endpoint_11_74_prefix_8 endpoint_11_74_window_8

def endpoint_11_74 : CertifiedEndpoint :=
  ⟨⟨11, 74, 2024⟩, 207501855247928844, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_11_74_flag endpoint_11_74_sources 10 207501855247928844 207501855247928844 rfl endpoint_11_74_base endpoint_11_74_prefix_10) (by decide)⟩
private def endpoint_11_75_flag : Flag := ⟨11, 75, 1942⟩
private def endpoint_11_75_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_11_75_base : receiptBase endpoint_11_75_flag endpoint_11_75_sources = some 203226672872436836 := by decide +kernel
private theorem endpoint_11_75_window_0 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 2 203226672872436836 = some 203226672872436836 := by decide +kernel
private theorem endpoint_11_75_window_2 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 2 2 203226672872436836 = some 203226672872436836 := by decide +kernel
private theorem endpoint_11_75_prefix_4 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 4 203226672872436836 = some 203226672872436836 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 2 2 203226672872436836 203226672872436836 203226672872436836 endpoint_11_75_window_0 endpoint_11_75_window_2
private theorem endpoint_11_75_window_4 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 4 2 203226672872436836 = some 203226672872436836 := by decide +kernel
private theorem endpoint_11_75_prefix_6 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 6 203226672872436836 = some 203226672872436836 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 4 2 203226672872436836 203226672872436836 203226672872436836 endpoint_11_75_prefix_4 endpoint_11_75_window_4
private theorem endpoint_11_75_window_6 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 6 2 203226672872436836 = some 203226672872436836 := by decide +kernel
private theorem endpoint_11_75_prefix_8 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 8 203226672872436836 = some 203226672872436836 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 6 2 203226672872436836 203226672872436836 203226672872436836 endpoint_11_75_prefix_6 endpoint_11_75_window_6
private theorem endpoint_11_75_window_8 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 8 2 203226672872436836 = some 203226672872436836 := by decide +kernel
private theorem endpoint_11_75_prefix_10 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 10 203226672872436836 = some 203226672872436836 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 8 2 203226672872436836 203226672872436836 203226672872436836 endpoint_11_75_prefix_8 endpoint_11_75_window_8

def endpoint_11_75 : CertifiedEndpoint :=
  ⟨⟨11, 75, 1942⟩, 203226672872436836, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_11_75_flag endpoint_11_75_sources 10 203226672872436836 203226672872436836 rfl endpoint_11_75_base endpoint_11_75_prefix_10) (by decide)⟩
private def endpoint_11_76_flag : Flag := ⟨11, 76, 1859⟩
private def endpoint_11_76_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_11_76_base : receiptBase endpoint_11_76_flag endpoint_11_76_sources = some 196958278766479584 := by decide +kernel
private theorem endpoint_11_76_window_0 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 2 196958278766479584 = some 196958278766479584 := by decide +kernel
private theorem endpoint_11_76_window_2 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 2 2 196958278766479584 = some 196958278766479584 := by decide +kernel
private theorem endpoint_11_76_prefix_4 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 4 196958278766479584 = some 196958278766479584 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 2 2 196958278766479584 196958278766479584 196958278766479584 endpoint_11_76_window_0 endpoint_11_76_window_2
private theorem endpoint_11_76_window_4 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 4 2 196958278766479584 = some 196958278766479584 := by decide +kernel
private theorem endpoint_11_76_prefix_6 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 6 196958278766479584 = some 196958278766479584 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 4 2 196958278766479584 196958278766479584 196958278766479584 endpoint_11_76_prefix_4 endpoint_11_76_window_4
private theorem endpoint_11_76_window_6 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 6 2 196958278766479584 = some 196958278766479584 := by decide +kernel
private theorem endpoint_11_76_prefix_8 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 8 196958278766479584 = some 196958278766479584 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 6 2 196958278766479584 196958278766479584 196958278766479584 endpoint_11_76_prefix_6 endpoint_11_76_window_6
private theorem endpoint_11_76_window_8 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 8 2 196958278766479584 = some 196958278766479584 := by decide +kernel
private theorem endpoint_11_76_prefix_10 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 10 196958278766479584 = some 196958278766479584 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 8 2 196958278766479584 196958278766479584 196958278766479584 endpoint_11_76_prefix_8 endpoint_11_76_window_8

def endpoint_11_76 : CertifiedEndpoint :=
  ⟨⟨11, 76, 1859⟩, 196958278766479584, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_11_76_flag endpoint_11_76_sources 10 196958278766479584 196958278766479584 rfl endpoint_11_76_base endpoint_11_76_prefix_10) (by decide)⟩
private def endpoint_11_77_flag : Flag := ⟨11, 77, 1772⟩
private def endpoint_11_77_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_11_77_base : receiptBase endpoint_11_77_flag endpoint_11_77_sources = some 191654168344223544 := by decide +kernel
private theorem endpoint_11_77_window_0 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 2 191654168344223544 = some 191654168344223544 := by decide +kernel
private theorem endpoint_11_77_window_2 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 2 2 191654168344223544 = some 191654168344223544 := by decide +kernel
private theorem endpoint_11_77_prefix_4 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 4 191654168344223544 = some 191654168344223544 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 2 2 191654168344223544 191654168344223544 191654168344223544 endpoint_11_77_window_0 endpoint_11_77_window_2
private theorem endpoint_11_77_window_4 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 4 2 191654168344223544 = some 191654168344223544 := by decide +kernel
private theorem endpoint_11_77_prefix_6 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 6 191654168344223544 = some 191654168344223544 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 4 2 191654168344223544 191654168344223544 191654168344223544 endpoint_11_77_prefix_4 endpoint_11_77_window_4
private theorem endpoint_11_77_window_6 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 6 2 191654168344223544 = some 191654168344223544 := by decide +kernel
private theorem endpoint_11_77_prefix_8 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 8 191654168344223544 = some 191654168344223544 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 6 2 191654168344223544 191654168344223544 191654168344223544 endpoint_11_77_prefix_6 endpoint_11_77_window_6
private theorem endpoint_11_77_window_8 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 8 2 191654168344223544 = some 191654168344223544 := by decide +kernel
private theorem endpoint_11_77_prefix_10 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 10 191654168344223544 = some 191654168344223544 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 8 2 191654168344223544 191654168344223544 191654168344223544 endpoint_11_77_prefix_8 endpoint_11_77_window_8

def endpoint_11_77 : CertifiedEndpoint :=
  ⟨⟨11, 77, 1772⟩, 191654168344223544, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_11_77_flag endpoint_11_77_sources 10 191654168344223544 191654168344223544 rfl endpoint_11_77_base endpoint_11_77_prefix_10) (by decide)⟩
private def endpoint_11_78_flag : Flag := ⟨11, 78, 1683⟩
private def endpoint_11_78_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_11_78_base : receiptBase endpoint_11_78_flag endpoint_11_78_sources = some 184226799067671517 := by decide +kernel
private theorem endpoint_11_78_window_0 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 2 184226799067671517 = some 184226799067671517 := by decide +kernel
private theorem endpoint_11_78_window_2 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 2 2 184226799067671517 = some 184226799067671517 := by decide +kernel
private theorem endpoint_11_78_prefix_4 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 4 184226799067671517 = some 184226799067671517 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 2 2 184226799067671517 184226799067671517 184226799067671517 endpoint_11_78_window_0 endpoint_11_78_window_2
private theorem endpoint_11_78_window_4 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 4 2 184226799067671517 = some 184226799067671517 := by decide +kernel
private theorem endpoint_11_78_prefix_6 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 6 184226799067671517 = some 184226799067671517 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 4 2 184226799067671517 184226799067671517 184226799067671517 endpoint_11_78_prefix_4 endpoint_11_78_window_4
private theorem endpoint_11_78_window_6 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 6 2 184226799067671517 = some 184226799067671517 := by decide +kernel
private theorem endpoint_11_78_prefix_8 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 8 184226799067671517 = some 184226799067671517 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 6 2 184226799067671517 184226799067671517 184226799067671517 endpoint_11_78_prefix_6 endpoint_11_78_window_6
private theorem endpoint_11_78_window_8 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 8 2 184226799067671517 = some 184226799067671517 := by decide +kernel
private theorem endpoint_11_78_prefix_10 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 10 184226799067671517 = some 184226799067671517 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 8 2 184226799067671517 184226799067671517 184226799067671517 endpoint_11_78_prefix_8 endpoint_11_78_window_8

def endpoint_11_78 : CertifiedEndpoint :=
  ⟨⟨11, 78, 1683⟩, 184226799067671517, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_11_78_flag endpoint_11_78_sources 10 184226799067671517 184226799067671517 rfl endpoint_11_78_base endpoint_11_78_prefix_10) (by decide)⟩
private def endpoint_11_79_flag : Flag := ⟨11, 79, 1591⟩
private def endpoint_11_79_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_11_79_base : receiptBase endpoint_11_79_flag endpoint_11_79_sources = some 176246990919191977 := by decide +kernel
private theorem endpoint_11_79_window_0 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 2 176246990919191977 = some 176246990919191977 := by decide +kernel
private theorem endpoint_11_79_window_2 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 2 2 176246990919191977 = some 176246990919191977 := by decide +kernel
private theorem endpoint_11_79_prefix_4 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 4 176246990919191977 = some 176246990919191977 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 2 2 176246990919191977 176246990919191977 176246990919191977 endpoint_11_79_window_0 endpoint_11_79_window_2
private theorem endpoint_11_79_window_4 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 4 2 176246990919191977 = some 176246990919191977 := by decide +kernel
private theorem endpoint_11_79_prefix_6 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 6 176246990919191977 = some 176246990919191977 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 4 2 176246990919191977 176246990919191977 176246990919191977 endpoint_11_79_prefix_4 endpoint_11_79_window_4
private theorem endpoint_11_79_window_6 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 6 2 176246990919191977 = some 176246990919191977 := by decide +kernel
private theorem endpoint_11_79_prefix_8 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 8 176246990919191977 = some 176246990919191977 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 6 2 176246990919191977 176246990919191977 176246990919191977 endpoint_11_79_prefix_6 endpoint_11_79_window_6
private theorem endpoint_11_79_window_8 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 8 2 176246990919191977 = some 176246990919191977 := by decide +kernel
private theorem endpoint_11_79_prefix_10 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 10 176246990919191977 = some 176246990919191977 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 8 2 176246990919191977 176246990919191977 176246990919191977 endpoint_11_79_prefix_8 endpoint_11_79_window_8

def endpoint_11_79 : CertifiedEndpoint :=
  ⟨⟨11, 79, 1591⟩, 176246990919191977, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_11_79_flag endpoint_11_79_sources 10 176246990919191977 176246990919191977 rfl endpoint_11_79_base endpoint_11_79_prefix_10) (by decide)⟩
private def endpoint_11_80_flag : Flag := ⟨11, 80, 1497⟩
private def endpoint_11_80_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_11_80_base : receiptBase endpoint_11_80_flag endpoint_11_80_sources = some 170785100629656570 := by decide +kernel
private theorem endpoint_11_80_window_0 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 2 170785100629656570 = some 170785100629656570 := by decide +kernel
private theorem endpoint_11_80_window_2 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 2 2 170785100629656570 = some 170785100629656570 := by decide +kernel
private theorem endpoint_11_80_prefix_4 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 4 170785100629656570 = some 170785100629656570 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 2 2 170785100629656570 170785100629656570 170785100629656570 endpoint_11_80_window_0 endpoint_11_80_window_2
private theorem endpoint_11_80_window_4 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 4 2 170785100629656570 = some 170785100629656570 := by decide +kernel
private theorem endpoint_11_80_prefix_6 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 6 170785100629656570 = some 170785100629656570 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 4 2 170785100629656570 170785100629656570 170785100629656570 endpoint_11_80_prefix_4 endpoint_11_80_window_4
private theorem endpoint_11_80_window_6 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 6 2 170785100629656570 = some 170785100629656570 := by decide +kernel
private theorem endpoint_11_80_prefix_8 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 8 170785100629656570 = some 170785100629656570 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 6 2 170785100629656570 170785100629656570 170785100629656570 endpoint_11_80_prefix_6 endpoint_11_80_window_6
private theorem endpoint_11_80_window_8 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 8 2 170785100629656570 = some 170785100629656570 := by decide +kernel
private theorem endpoint_11_80_prefix_10 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 10 170785100629656570 = some 170785100629656570 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 8 2 170785100629656570 170785100629656570 170785100629656570 endpoint_11_80_prefix_8 endpoint_11_80_window_8

def endpoint_11_80 : CertifiedEndpoint :=
  ⟨⟨11, 80, 1497⟩, 170785100629656570, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_11_80_flag endpoint_11_80_sources 10 170785100629656570 170785100629656570 rfl endpoint_11_80_base endpoint_11_80_prefix_10) (by decide)⟩
private def endpoint_11_81_flag : Flag := ⟨11, 81, 1400⟩
private def endpoint_11_81_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_11_81_base : receiptBase endpoint_11_81_flag endpoint_11_81_sources = some 161557819646623990 := by decide +kernel
private theorem endpoint_11_81_window_0 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 2 161557819646623990 = some 161557819646623990 := by decide +kernel
private theorem endpoint_11_81_window_2 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 2 2 161557819646623990 = some 161557819646623990 := by decide +kernel
private theorem endpoint_11_81_prefix_4 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 4 161557819646623990 = some 161557819646623990 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 2 2 161557819646623990 161557819646623990 161557819646623990 endpoint_11_81_window_0 endpoint_11_81_window_2
private theorem endpoint_11_81_window_4 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 4 2 161557819646623990 = some 161557819646623990 := by decide +kernel
private theorem endpoint_11_81_prefix_6 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 6 161557819646623990 = some 161557819646623990 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 4 2 161557819646623990 161557819646623990 161557819646623990 endpoint_11_81_prefix_4 endpoint_11_81_window_4
private theorem endpoint_11_81_window_6 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 6 2 161557819646623990 = some 161557819646623990 := by decide +kernel
private theorem endpoint_11_81_prefix_8 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 8 161557819646623990 = some 161557819646623990 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 6 2 161557819646623990 161557819646623990 161557819646623990 endpoint_11_81_prefix_6 endpoint_11_81_window_6
private theorem endpoint_11_81_window_8 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 8 2 161557819646623990 = some 161557819646623990 := by decide +kernel
private theorem endpoint_11_81_prefix_10 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 10 161557819646623990 = some 161557819646623990 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 8 2 161557819646623990 161557819646623990 161557819646623990 endpoint_11_81_prefix_8 endpoint_11_81_window_8

def endpoint_11_81 : CertifiedEndpoint :=
  ⟨⟨11, 81, 1400⟩, 161557819646623990, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_11_81_flag endpoint_11_81_sources 10 161557819646623990 161557819646623990 rfl endpoint_11_81_base endpoint_11_81_prefix_10) (by decide)⟩
private def endpoint_11_82_flag : Flag := ⟨11, 82, 1300⟩
private def endpoint_11_82_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_11_82_base : receiptBase endpoint_11_82_flag endpoint_11_82_sources = some 152884906782857294 := by decide +kernel
private theorem endpoint_11_82_window_0 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 2 152884906782857294 = some 152884906782857294 := by decide +kernel
private theorem endpoint_11_82_window_2 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 2 2 152884906782857294 = some 152884906782857294 := by decide +kernel
private theorem endpoint_11_82_prefix_4 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 4 152884906782857294 = some 152884906782857294 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 2 2 152884906782857294 152884906782857294 152884906782857294 endpoint_11_82_window_0 endpoint_11_82_window_2
private theorem endpoint_11_82_window_4 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 4 2 152884906782857294 = some 152884906782857294 := by decide +kernel
private theorem endpoint_11_82_prefix_6 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 6 152884906782857294 = some 152884906782857294 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 4 2 152884906782857294 152884906782857294 152884906782857294 endpoint_11_82_prefix_4 endpoint_11_82_window_4
private theorem endpoint_11_82_window_6 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 6 2 152884906782857294 = some 152884906782857294 := by decide +kernel
private theorem endpoint_11_82_prefix_8 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 8 152884906782857294 = some 152884906782857294 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 6 2 152884906782857294 152884906782857294 152884906782857294 endpoint_11_82_prefix_6 endpoint_11_82_window_6
private theorem endpoint_11_82_window_8 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 8 2 152884906782857294 = some 152884906782857294 := by decide +kernel
private theorem endpoint_11_82_prefix_10 : receiptWindow endpoint_11_82_flag endpoint_11_82_sources 0 10 152884906782857294 = some 152884906782857294 :=
  join_receipt_window endpoint_11_82_flag endpoint_11_82_sources 0 8 2 152884906782857294 152884906782857294 152884906782857294 endpoint_11_82_prefix_8 endpoint_11_82_window_8

def endpoint_11_82 : CertifiedEndpoint :=
  ⟨⟨11, 82, 1300⟩, 152884906782857294, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_11_82_flag endpoint_11_82_sources 10 152884906782857294 152884906782857294 rfl endpoint_11_82_base endpoint_11_82_prefix_10) (by decide)⟩
def endpoint_11_83 : CertifiedEndpoint :=
  ⟨⟨11, 83, 1198⟩, 241122201592975849, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_84 : CertifiedEndpoint :=
  ⟨⟨11, 84, 1092⟩, 221703202487500708, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_85 : CertifiedEndpoint :=
  ⟨⟨11, 85, 985⟩, 201491564452864454, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_86 : CertifiedEndpoint :=
  ⟨⟨11, 86, 874⟩, 179827641199097734, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_87 : CertifiedEndpoint :=
  ⟨⟨11, 87, 761⟩, 157118623071219346, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_88 : CertifiedEndpoint :=
  ⟨⟨11, 88, 645⟩, 133125626561067945, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_89 : CertifiedEndpoint :=
  ⟨⟨11, 89, 526⟩, 107824221282422953, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_90 : CertifiedEndpoint :=
  ⟨⟨11, 90, 405⟩, 81418002407793769, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_91 : CertifiedEndpoint :=
  ⟨⟨11, 91, 280⟩, 53429202920857703, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_92 : CertifiedEndpoint :=
  ⟨⟨11, 92, 154⟩, 24525612573657634, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_12 : CertifiedEndpoint :=
  ⟨⟨12, 12, 4096⟩, 83204252104466376, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_13 : CertifiedEndpoint :=
  ⟨⟨12, 13, 4077⟩, 86761339088619706, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_14 : CertifiedEndpoint :=
  ⟨⟨12, 14, 4057⟩, 90259239898598875, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_15 : CertifiedEndpoint :=
  ⟨⟨12, 15, 4037⟩, 101768879737083950, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_16 : CertifiedEndpoint :=
  ⟨⟨12, 16, 4017⟩, 113156659716398171, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_17 : CertifiedEndpoint :=
  ⟨⟨12, 17, 3997⟩, 124422579836541538, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_18 : CertifiedEndpoint :=
  ⟨⟨12, 18, 3976⟩, 135532451269623148, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_19 : CertifiedEndpoint :=
  ⟨⟨12, 19, 3955⟩, 146514518460159716, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_20 : CertifiedEndpoint :=
  ⟨⟨12, 20, 3935⟩, 157408914619416333, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_21 : CertifiedEndpoint :=
  ⟨⟨12, 21, 3913⟩, 168095240113597726, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_22 : CertifiedEndpoint :=
  ⟨⟨12, 22, 3892⟩, 178693894576499168, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_23 : CertifiedEndpoint :=
  ⟨⟨12, 23, 3870⟩, 189115695010529195, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_24 : CertifiedEndpoint :=
  ⟨⟨12, 24, 3849⟩, 199455768796653459, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_25 : CertifiedEndpoint :=
  ⟨⟨12, 25, 3826⟩, 209558050000831559, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_26 : CertifiedEndpoint :=
  ⟨⟨12, 26, 3804⟩, 219578604557103896, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_27 : CertifiedEndpoint :=
  ⟨⟨12, 27, 3781⟩, 229404471934382254, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_28 : CertifiedEndpoint :=
  ⟨⟨12, 28, 3758⟩, 239090646302367194, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_29 : CertifiedEndpoint :=
  ⟨⟨12, 29, 3735⟩, 248637127661058716, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_12_30_flag : Flag := ⟨12, 30, 3712⟩
private def endpoint_12_30_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_30_base : receiptBase endpoint_12_30_flag endpoint_12_30_sources = some 172030771207795650 := by decide +kernel
private theorem endpoint_12_30_window_0 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 2 172030771207795650 = some 172030771207795650 := by decide +kernel
private theorem endpoint_12_30_window_2 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 2 2 172030771207795650 = some 172030771207795650 := by decide +kernel
private theorem endpoint_12_30_prefix_4 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 4 172030771207795650 = some 172030771207795650 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 2 2 172030771207795650 172030771207795650 172030771207795650 endpoint_12_30_window_0 endpoint_12_30_window_2
private theorem endpoint_12_30_window_4 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 4 2 172030771207795650 = some 172030771207795650 := by decide +kernel
private theorem endpoint_12_30_prefix_6 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 6 172030771207795650 = some 172030771207795650 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 4 2 172030771207795650 172030771207795650 172030771207795650 endpoint_12_30_prefix_4 endpoint_12_30_window_4
private theorem endpoint_12_30_window_6 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 6 2 172030771207795650 = some 172030771207795650 := by decide +kernel
private theorem endpoint_12_30_prefix_8 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 8 172030771207795650 = some 172030771207795650 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 6 2 172030771207795650 172030771207795650 172030771207795650 endpoint_12_30_prefix_6 endpoint_12_30_window_6
private theorem endpoint_12_30_window_8 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 8 2 172030771207795650 = some 172030771207795650 := by decide +kernel
private theorem endpoint_12_30_prefix_10 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 10 172030771207795650 = some 172030771207795650 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 8 2 172030771207795650 172030771207795650 172030771207795650 endpoint_12_30_prefix_8 endpoint_12_30_window_8
private theorem endpoint_12_30_window_10 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 10 1 172030771207795650 = some 172030771207795650 := by decide +kernel
private theorem endpoint_12_30_prefix_11 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 11 172030771207795650 = some 172030771207795650 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 10 1 172030771207795650 172030771207795650 172030771207795650 endpoint_12_30_prefix_10 endpoint_12_30_window_10

def endpoint_12_30 : CertifiedEndpoint :=
  ⟨⟨12, 30, 3712⟩, 172030771207795650, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_30_flag endpoint_12_30_sources 11 172030771207795650 172030771207795650 rfl endpoint_12_30_base endpoint_12_30_prefix_11) (by decide)⟩
private def endpoint_12_31_flag : Flag := ⟨12, 31, 3688⟩
private def endpoint_12_31_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_31_base : receiptBase endpoint_12_31_flag endpoint_12_31_sources = some 175536948123896008 := by decide +kernel
private theorem endpoint_12_31_window_0 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 2 175536948123896008 = some 175536948123896008 := by decide +kernel
private theorem endpoint_12_31_window_2 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 2 2 175536948123896008 = some 175536948123896008 := by decide +kernel
private theorem endpoint_12_31_prefix_4 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 4 175536948123896008 = some 175536948123896008 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 2 2 175536948123896008 175536948123896008 175536948123896008 endpoint_12_31_window_0 endpoint_12_31_window_2
private theorem endpoint_12_31_window_4 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 4 2 175536948123896008 = some 175536948123896008 := by decide +kernel
private theorem endpoint_12_31_prefix_6 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 6 175536948123896008 = some 175536948123896008 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 4 2 175536948123896008 175536948123896008 175536948123896008 endpoint_12_31_prefix_4 endpoint_12_31_window_4
private theorem endpoint_12_31_window_6 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 6 2 175536948123896008 = some 175536948123896008 := by decide +kernel
private theorem endpoint_12_31_prefix_8 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 8 175536948123896008 = some 175536948123896008 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 6 2 175536948123896008 175536948123896008 175536948123896008 endpoint_12_31_prefix_6 endpoint_12_31_window_6
private theorem endpoint_12_31_window_8 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 8 2 175536948123896008 = some 175536948123896008 := by decide +kernel
private theorem endpoint_12_31_prefix_10 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 10 175536948123896008 = some 175536948123896008 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 8 2 175536948123896008 175536948123896008 175536948123896008 endpoint_12_31_prefix_8 endpoint_12_31_window_8
private theorem endpoint_12_31_window_10 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 10 1 175536948123896008 = some 175536948123896008 := by decide +kernel
private theorem endpoint_12_31_prefix_11 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 11 175536948123896008 = some 175536948123896008 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 10 1 175536948123896008 175536948123896008 175536948123896008 endpoint_12_31_prefix_10 endpoint_12_31_window_10

def endpoint_12_31 : CertifiedEndpoint :=
  ⟨⟨12, 31, 3688⟩, 175536948123896008, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_31_flag endpoint_12_31_sources 11 175536948123896008 175536948123896008 rfl endpoint_12_31_base endpoint_12_31_prefix_11) (by decide)⟩
private def endpoint_12_32_flag : Flag := ⟨12, 32, 3664⟩
private def endpoint_12_32_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_32_base : receiptBase endpoint_12_32_flag endpoint_12_32_sources = some 178983283506388132 := by decide +kernel
private theorem endpoint_12_32_window_0 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 2 178983283506388132 = some 178983283506388132 := by decide +kernel
private theorem endpoint_12_32_window_2 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 2 2 178983283506388132 = some 178983283506388132 := by decide +kernel
private theorem endpoint_12_32_prefix_4 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 4 178983283506388132 = some 178983283506388132 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 2 2 178983283506388132 178983283506388132 178983283506388132 endpoint_12_32_window_0 endpoint_12_32_window_2
private theorem endpoint_12_32_window_4 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 4 2 178983283506388132 = some 178983283506388132 := by decide +kernel
private theorem endpoint_12_32_prefix_6 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 6 178983283506388132 = some 178983283506388132 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 4 2 178983283506388132 178983283506388132 178983283506388132 endpoint_12_32_prefix_4 endpoint_12_32_window_4
private theorem endpoint_12_32_window_6 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 6 2 178983283506388132 = some 178983283506388132 := by decide +kernel
private theorem endpoint_12_32_prefix_8 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 8 178983283506388132 = some 178983283506388132 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 6 2 178983283506388132 178983283506388132 178983283506388132 endpoint_12_32_prefix_6 endpoint_12_32_window_6
private theorem endpoint_12_32_window_8 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 8 2 178983283506388132 = some 178983283506388132 := by decide +kernel
private theorem endpoint_12_32_prefix_10 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 10 178983283506388132 = some 178983283506388132 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 8 2 178983283506388132 178983283506388132 178983283506388132 endpoint_12_32_prefix_8 endpoint_12_32_window_8
private theorem endpoint_12_32_window_10 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 10 1 178983283506388132 = some 178983283506388132 := by decide +kernel
private theorem endpoint_12_32_prefix_11 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 11 178983283506388132 = some 178983283506388132 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 10 1 178983283506388132 178983283506388132 178983283506388132 endpoint_12_32_prefix_10 endpoint_12_32_window_10

def endpoint_12_32 : CertifiedEndpoint :=
  ⟨⟨12, 32, 3664⟩, 178983283506388132, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_32_flag endpoint_12_32_sources 11 178983283506388132 178983283506388132 rfl endpoint_12_32_base endpoint_12_32_prefix_11) (by decide)⟩
private def endpoint_12_33_flag : Flag := ⟨12, 33, 3639⟩
private def endpoint_12_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_33_base : receiptBase endpoint_12_33_flag endpoint_12_33_sources = some 182320453535920736 := by decide +kernel
private theorem endpoint_12_33_window_0 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 2 182320453535920736 = some 182320453535920736 := by decide +kernel
private theorem endpoint_12_33_window_2 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 2 2 182320453535920736 = some 182320453535920736 := by decide +kernel
private theorem endpoint_12_33_prefix_4 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 4 182320453535920736 = some 182320453535920736 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 2 2 182320453535920736 182320453535920736 182320453535920736 endpoint_12_33_window_0 endpoint_12_33_window_2
private theorem endpoint_12_33_window_4 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 4 2 182320453535920736 = some 182320453535920736 := by decide +kernel
private theorem endpoint_12_33_prefix_6 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 6 182320453535920736 = some 182320453535920736 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 4 2 182320453535920736 182320453535920736 182320453535920736 endpoint_12_33_prefix_4 endpoint_12_33_window_4
private theorem endpoint_12_33_window_6 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 6 2 182320453535920736 = some 182320453535920736 := by decide +kernel
private theorem endpoint_12_33_prefix_8 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 8 182320453535920736 = some 182320453535920736 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 6 2 182320453535920736 182320453535920736 182320453535920736 endpoint_12_33_prefix_6 endpoint_12_33_window_6
private theorem endpoint_12_33_window_8 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 8 2 182320453535920736 = some 182320453535920736 := by decide +kernel
private theorem endpoint_12_33_prefix_10 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 10 182320453535920736 = some 182320453535920736 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 8 2 182320453535920736 182320453535920736 182320453535920736 endpoint_12_33_prefix_8 endpoint_12_33_window_8
private theorem endpoint_12_33_window_10 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 10 1 182320453535920736 = some 182320453535920736 := by decide +kernel
private theorem endpoint_12_33_prefix_11 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 11 182320453535920736 = some 182320453535920736 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 10 1 182320453535920736 182320453535920736 182320453535920736 endpoint_12_33_prefix_10 endpoint_12_33_window_10

def endpoint_12_33 : CertifiedEndpoint :=
  ⟨⟨12, 33, 3639⟩, 182320453535920736, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_33_flag endpoint_12_33_sources 11 182320453535920736 182320453535920736 rfl endpoint_12_33_base endpoint_12_33_prefix_11) (by decide)⟩
private def endpoint_12_34_flag : Flag := ⟨12, 34, 3614⟩
private def endpoint_12_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_34_base : receiptBase endpoint_12_34_flag endpoint_12_34_sources = some 185595339703926606 := by decide +kernel
private theorem endpoint_12_34_window_0 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 2 185595339703926606 = some 185595339703926606 := by decide +kernel
private theorem endpoint_12_34_window_2 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 2 2 185595339703926606 = some 185595339703926606 := by decide +kernel
private theorem endpoint_12_34_prefix_4 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 4 185595339703926606 = some 185595339703926606 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 2 2 185595339703926606 185595339703926606 185595339703926606 endpoint_12_34_window_0 endpoint_12_34_window_2
private theorem endpoint_12_34_window_4 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 4 2 185595339703926606 = some 185595339703926606 := by decide +kernel
private theorem endpoint_12_34_prefix_6 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 6 185595339703926606 = some 185595339703926606 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 4 2 185595339703926606 185595339703926606 185595339703926606 endpoint_12_34_prefix_4 endpoint_12_34_window_4
private theorem endpoint_12_34_window_6 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 6 2 185595339703926606 = some 185595339703926606 := by decide +kernel
private theorem endpoint_12_34_prefix_8 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 8 185595339703926606 = some 185595339703926606 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 6 2 185595339703926606 185595339703926606 185595339703926606 endpoint_12_34_prefix_6 endpoint_12_34_window_6
private theorem endpoint_12_34_window_8 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 8 2 185595339703926606 = some 185595339703926606 := by decide +kernel
private theorem endpoint_12_34_prefix_10 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 10 185595339703926606 = some 185595339703926606 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 8 2 185595339703926606 185595339703926606 185595339703926606 endpoint_12_34_prefix_8 endpoint_12_34_window_8
private theorem endpoint_12_34_window_10 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 10 1 185595339703926606 = some 185595339703926606 := by decide +kernel
private theorem endpoint_12_34_prefix_11 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 11 185595339703926606 = some 185595339703926606 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 10 1 185595339703926606 185595339703926606 185595339703926606 endpoint_12_34_prefix_10 endpoint_12_34_window_10

def endpoint_12_34 : CertifiedEndpoint :=
  ⟨⟨12, 34, 3614⟩, 185595339703926606, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_34_flag endpoint_12_34_sources 11 185595339703926606 185595339703926606 rfl endpoint_12_34_base endpoint_12_34_prefix_11) (by decide)⟩
private def endpoint_12_35_flag : Flag := ⟨12, 35, 3589⟩
private def endpoint_12_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_35_base : receiptBase endpoint_12_35_flag endpoint_12_35_sources = some 188807942010405742 := by decide +kernel
private theorem endpoint_12_35_window_0 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 2 188807942010405742 = some 188807942010405742 := by decide +kernel
private theorem endpoint_12_35_window_2 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 2 2 188807942010405742 = some 188807942010405742 := by decide +kernel
private theorem endpoint_12_35_prefix_4 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 4 188807942010405742 = some 188807942010405742 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 2 2 188807942010405742 188807942010405742 188807942010405742 endpoint_12_35_window_0 endpoint_12_35_window_2
private theorem endpoint_12_35_window_4 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 4 2 188807942010405742 = some 188807942010405742 := by decide +kernel
private theorem endpoint_12_35_prefix_6 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 6 188807942010405742 = some 188807942010405742 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 4 2 188807942010405742 188807942010405742 188807942010405742 endpoint_12_35_prefix_4 endpoint_12_35_window_4
private theorem endpoint_12_35_window_6 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 6 2 188807942010405742 = some 188807942010405742 := by decide +kernel
private theorem endpoint_12_35_prefix_8 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 8 188807942010405742 = some 188807942010405742 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 6 2 188807942010405742 188807942010405742 188807942010405742 endpoint_12_35_prefix_6 endpoint_12_35_window_6
private theorem endpoint_12_35_window_8 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 8 2 188807942010405742 = some 188807942010405742 := by decide +kernel
private theorem endpoint_12_35_prefix_10 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 10 188807942010405742 = some 188807942010405742 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 8 2 188807942010405742 188807942010405742 188807942010405742 endpoint_12_35_prefix_8 endpoint_12_35_window_8
private theorem endpoint_12_35_window_10 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 10 1 188807942010405742 = some 188807942010405742 := by decide +kernel
private theorem endpoint_12_35_prefix_11 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 11 188807942010405742 = some 188807942010405742 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 10 1 188807942010405742 188807942010405742 188807942010405742 endpoint_12_35_prefix_10 endpoint_12_35_window_10

def endpoint_12_35 : CertifiedEndpoint :=
  ⟨⟨12, 35, 3589⟩, 188807942010405742, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_35_flag endpoint_12_35_sources 11 188807942010405742 188807942010405742 rfl endpoint_12_35_base endpoint_12_35_prefix_11) (by decide)⟩
private def endpoint_12_36_flag : Flag := ⟨12, 36, 3563⟩
private def endpoint_12_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_36_base : receiptBase endpoint_12_36_flag endpoint_12_36_sources = some 191905273144129112 := by decide +kernel
private theorem endpoint_12_36_window_0 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 2 191905273144129112 = some 191905273144129112 := by decide +kernel
private theorem endpoint_12_36_window_2 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 2 2 191905273144129112 = some 191905273144129112 := by decide +kernel
private theorem endpoint_12_36_prefix_4 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 4 191905273144129112 = some 191905273144129112 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 2 2 191905273144129112 191905273144129112 191905273144129112 endpoint_12_36_window_0 endpoint_12_36_window_2
private theorem endpoint_12_36_window_4 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 4 2 191905273144129112 = some 191905273144129112 := by decide +kernel
private theorem endpoint_12_36_prefix_6 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 6 191905273144129112 = some 191905273144129112 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 4 2 191905273144129112 191905273144129112 191905273144129112 endpoint_12_36_prefix_4 endpoint_12_36_window_4
private theorem endpoint_12_36_window_6 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 6 2 191905273144129112 = some 191905273144129112 := by decide +kernel
private theorem endpoint_12_36_prefix_8 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 8 191905273144129112 = some 191905273144129112 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 6 2 191905273144129112 191905273144129112 191905273144129112 endpoint_12_36_prefix_6 endpoint_12_36_window_6
private theorem endpoint_12_36_window_8 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 8 2 191905273144129112 = some 191905273144129112 := by decide +kernel
private theorem endpoint_12_36_prefix_10 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 10 191905273144129112 = some 191905273144129112 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 8 2 191905273144129112 191905273144129112 191905273144129112 endpoint_12_36_prefix_8 endpoint_12_36_window_8
private theorem endpoint_12_36_window_10 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 10 1 191905273144129112 = some 191905273144129112 := by decide +kernel
private theorem endpoint_12_36_prefix_11 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 11 191905273144129112 = some 191905273144129112 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 10 1 191905273144129112 191905273144129112 191905273144129112 endpoint_12_36_prefix_10 endpoint_12_36_window_10

def endpoint_12_36 : CertifiedEndpoint :=
  ⟨⟨12, 36, 3563⟩, 191905273144129112, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_36_flag endpoint_12_36_sources 11 191905273144129112 191905273144129112 rfl endpoint_12_36_base endpoint_12_36_prefix_11) (by decide)⟩
private def endpoint_12_37_flag : Flag := ⟨12, 37, 3537⟩
private def endpoint_12_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_37_base : receiptBase endpoint_12_37_flag endpoint_12_37_sources = some 194937878088407249 := by decide +kernel
private theorem endpoint_12_37_window_0 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 2 194937878088407249 = some 194937878088407249 := by decide +kernel
private theorem endpoint_12_37_window_2 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 2 2 194937878088407249 = some 194937878088407249 := by decide +kernel
private theorem endpoint_12_37_prefix_4 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 4 194937878088407249 = some 194937878088407249 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 2 2 194937878088407249 194937878088407249 194937878088407249 endpoint_12_37_window_0 endpoint_12_37_window_2
private theorem endpoint_12_37_window_4 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 4 2 194937878088407249 = some 194937878088407249 := by decide +kernel
private theorem endpoint_12_37_prefix_6 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 6 194937878088407249 = some 194937878088407249 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 4 2 194937878088407249 194937878088407249 194937878088407249 endpoint_12_37_prefix_4 endpoint_12_37_window_4
private theorem endpoint_12_37_window_6 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 6 2 194937878088407249 = some 194937878088407249 := by decide +kernel
private theorem endpoint_12_37_prefix_8 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 8 194937878088407249 = some 194937878088407249 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 6 2 194937878088407249 194937878088407249 194937878088407249 endpoint_12_37_prefix_6 endpoint_12_37_window_6
private theorem endpoint_12_37_window_8 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 8 2 194937878088407249 = some 194937878088407249 := by decide +kernel
private theorem endpoint_12_37_prefix_10 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 10 194937878088407249 = some 194937878088407249 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 8 2 194937878088407249 194937878088407249 194937878088407249 endpoint_12_37_prefix_8 endpoint_12_37_window_8
private theorem endpoint_12_37_window_10 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 10 1 194937878088407249 = some 194937878088407249 := by decide +kernel
private theorem endpoint_12_37_prefix_11 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 11 194937878088407249 = some 194937878088407249 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 10 1 194937878088407249 194937878088407249 194937878088407249 endpoint_12_37_prefix_10 endpoint_12_37_window_10

def endpoint_12_37 : CertifiedEndpoint :=
  ⟨⟨12, 37, 3537⟩, 194937878088407249, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_37_flag endpoint_12_37_sources 11 194937878088407249 194937878088407249 rfl endpoint_12_37_base endpoint_12_37_prefix_11) (by decide)⟩
private def endpoint_12_38_flag : Flag := ⟨12, 38, 3511⟩
private def endpoint_12_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_38_base : receiptBase endpoint_12_38_flag endpoint_12_38_sources = some 197905756843240154 := by decide +kernel
private theorem endpoint_12_38_window_0 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 2 197905756843240154 = some 197905756843240154 := by decide +kernel
private theorem endpoint_12_38_window_2 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 2 2 197905756843240154 = some 197905756843240154 := by decide +kernel
private theorem endpoint_12_38_prefix_4 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 4 197905756843240154 = some 197905756843240154 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 2 2 197905756843240154 197905756843240154 197905756843240154 endpoint_12_38_window_0 endpoint_12_38_window_2
private theorem endpoint_12_38_window_4 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 4 2 197905756843240154 = some 197905756843240154 := by decide +kernel
private theorem endpoint_12_38_prefix_6 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 6 197905756843240154 = some 197905756843240154 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 4 2 197905756843240154 197905756843240154 197905756843240154 endpoint_12_38_prefix_4 endpoint_12_38_window_4
private theorem endpoint_12_38_window_6 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 6 2 197905756843240154 = some 197905756843240154 := by decide +kernel
private theorem endpoint_12_38_prefix_8 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 8 197905756843240154 = some 197905756843240154 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 6 2 197905756843240154 197905756843240154 197905756843240154 endpoint_12_38_prefix_6 endpoint_12_38_window_6
private theorem endpoint_12_38_window_8 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 8 2 197905756843240154 = some 197905756843240154 := by decide +kernel
private theorem endpoint_12_38_prefix_10 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 10 197905756843240154 = some 197905756843240154 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 8 2 197905756843240154 197905756843240154 197905756843240154 endpoint_12_38_prefix_8 endpoint_12_38_window_8
private theorem endpoint_12_38_window_10 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 10 1 197905756843240154 = some 197905756843240154 := by decide +kernel
private theorem endpoint_12_38_prefix_11 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 11 197905756843240154 = some 197905756843240154 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 10 1 197905756843240154 197905756843240154 197905756843240154 endpoint_12_38_prefix_10 endpoint_12_38_window_10

def endpoint_12_38 : CertifiedEndpoint :=
  ⟨⟨12, 38, 3511⟩, 197905756843240154, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_38_flag endpoint_12_38_sources 11 197905756843240154 197905756843240154 rfl endpoint_12_38_base endpoint_12_38_prefix_11) (by decide)⟩
private def endpoint_12_39_flag : Flag := ⟨12, 39, 3484⟩
private def endpoint_12_39_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_39_base : receiptBase endpoint_12_39_flag endpoint_12_39_sources = some 201546757169462970 := by decide +kernel
private theorem endpoint_12_39_window_0 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 2 201546757169462970 = some 201546757169462970 := by decide +kernel
private theorem endpoint_12_39_window_2 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 2 2 201546757169462970 = some 201546757169462970 := by decide +kernel
private theorem endpoint_12_39_prefix_4 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 4 201546757169462970 = some 201546757169462970 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 2 2 201546757169462970 201546757169462970 201546757169462970 endpoint_12_39_window_0 endpoint_12_39_window_2
private theorem endpoint_12_39_window_4 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 4 2 201546757169462970 = some 201546757169462970 := by decide +kernel
private theorem endpoint_12_39_prefix_6 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 6 201546757169462970 = some 201546757169462970 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 4 2 201546757169462970 201546757169462970 201546757169462970 endpoint_12_39_prefix_4 endpoint_12_39_window_4
private theorem endpoint_12_39_window_6 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 6 2 201546757169462970 = some 201546757169462970 := by decide +kernel
private theorem endpoint_12_39_prefix_8 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 8 201546757169462970 = some 201546757169462970 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 6 2 201546757169462970 201546757169462970 201546757169462970 endpoint_12_39_prefix_6 endpoint_12_39_window_6
private theorem endpoint_12_39_window_8 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 8 2 201546757169462970 = some 201546757169462970 := by decide +kernel
private theorem endpoint_12_39_prefix_10 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 10 201546757169462970 = some 201546757169462970 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 8 2 201546757169462970 201546757169462970 201546757169462970 endpoint_12_39_prefix_8 endpoint_12_39_window_8
private theorem endpoint_12_39_window_10 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 10 1 201546757169462970 = some 201546757169462970 := by decide +kernel
private theorem endpoint_12_39_prefix_11 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 11 201546757169462970 = some 201546757169462970 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 10 1 201546757169462970 201546757169462970 201546757169462970 endpoint_12_39_prefix_10 endpoint_12_39_window_10

def endpoint_12_39 : CertifiedEndpoint :=
  ⟨⟨12, 39, 3484⟩, 201546757169462970, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_39_flag endpoint_12_39_sources 11 201546757169462970 201546757169462970 rfl endpoint_12_39_base endpoint_12_39_prefix_11) (by decide)⟩
private def endpoint_12_40_flag : Flag := ⟨12, 40, 3456⟩
private def endpoint_12_40_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_40_base : receiptBase endpoint_12_40_flag endpoint_12_40_sources = some 204234957404354175 := by decide +kernel
private theorem endpoint_12_40_window_0 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 2 204234957404354175 = some 204234957404354175 := by decide +kernel
private theorem endpoint_12_40_window_2 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 2 2 204234957404354175 = some 204234957404354175 := by decide +kernel
private theorem endpoint_12_40_prefix_4 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 4 204234957404354175 = some 204234957404354175 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 2 2 204234957404354175 204234957404354175 204234957404354175 endpoint_12_40_window_0 endpoint_12_40_window_2
private theorem endpoint_12_40_window_4 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 4 2 204234957404354175 = some 204234957404354175 := by decide +kernel
private theorem endpoint_12_40_prefix_6 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 6 204234957404354175 = some 204234957404354175 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 4 2 204234957404354175 204234957404354175 204234957404354175 endpoint_12_40_prefix_4 endpoint_12_40_window_4
private theorem endpoint_12_40_window_6 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 6 2 204234957404354175 = some 204234957404354175 := by decide +kernel
private theorem endpoint_12_40_prefix_8 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 8 204234957404354175 = some 204234957404354175 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 6 2 204234957404354175 204234957404354175 204234957404354175 endpoint_12_40_prefix_6 endpoint_12_40_window_6
private theorem endpoint_12_40_window_8 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 8 2 204234957404354175 = some 204234957404354175 := by decide +kernel
private theorem endpoint_12_40_prefix_10 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 10 204234957404354175 = some 204234957404354175 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 8 2 204234957404354175 204234957404354175 204234957404354175 endpoint_12_40_prefix_8 endpoint_12_40_window_8
private theorem endpoint_12_40_window_10 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 10 1 204234957404354175 = some 204234957404354175 := by decide +kernel
private theorem endpoint_12_40_prefix_11 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 11 204234957404354175 = some 204234957404354175 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 10 1 204234957404354175 204234957404354175 204234957404354175 endpoint_12_40_prefix_10 endpoint_12_40_window_10

def endpoint_12_40 : CertifiedEndpoint :=
  ⟨⟨12, 40, 3456⟩, 204234957404354175, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_40_flag endpoint_12_40_sources 11 204234957404354175 204234957404354175 rfl endpoint_12_40_base endpoint_12_40_prefix_11) (by decide)⟩
private def endpoint_12_41_flag : Flag := ⟨12, 41, 3429⟩
private def endpoint_12_41_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_41_base : receiptBase endpoint_12_41_flag endpoint_12_41_sources = some 206913217977133405 := by decide +kernel
private theorem endpoint_12_41_window_0 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 2 206913217977133405 = some 206913217977133405 := by decide +kernel
private theorem endpoint_12_41_window_2 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 2 2 206913217977133405 = some 206913217977133405 := by decide +kernel
private theorem endpoint_12_41_prefix_4 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 4 206913217977133405 = some 206913217977133405 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 2 2 206913217977133405 206913217977133405 206913217977133405 endpoint_12_41_window_0 endpoint_12_41_window_2
private theorem endpoint_12_41_window_4 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 4 2 206913217977133405 = some 206913217977133405 := by decide +kernel
private theorem endpoint_12_41_prefix_6 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 6 206913217977133405 = some 206913217977133405 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 4 2 206913217977133405 206913217977133405 206913217977133405 endpoint_12_41_prefix_4 endpoint_12_41_window_4
private theorem endpoint_12_41_window_6 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 6 2 206913217977133405 = some 206913217977133405 := by decide +kernel
private theorem endpoint_12_41_prefix_8 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 8 206913217977133405 = some 206913217977133405 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 6 2 206913217977133405 206913217977133405 206913217977133405 endpoint_12_41_prefix_6 endpoint_12_41_window_6
private theorem endpoint_12_41_window_8 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 8 2 206913217977133405 = some 206913217977133405 := by decide +kernel
private theorem endpoint_12_41_prefix_10 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 10 206913217977133405 = some 206913217977133405 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 8 2 206913217977133405 206913217977133405 206913217977133405 endpoint_12_41_prefix_8 endpoint_12_41_window_8
private theorem endpoint_12_41_window_10 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 10 1 206913217977133405 = some 206913217977133405 := by decide +kernel
private theorem endpoint_12_41_prefix_11 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 11 206913217977133405 = some 206913217977133405 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 10 1 206913217977133405 206913217977133405 206913217977133405 endpoint_12_41_prefix_10 endpoint_12_41_window_10

def endpoint_12_41 : CertifiedEndpoint :=
  ⟨⟨12, 41, 3429⟩, 206913217977133405, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_41_flag endpoint_12_41_sources 11 206913217977133405 206913217977133405 rfl endpoint_12_41_base endpoint_12_41_prefix_11) (by decide)⟩
private def endpoint_12_42_flag : Flag := ⟨12, 42, 3400⟩
private def endpoint_12_42_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_42_base : receiptBase endpoint_12_42_flag endpoint_12_42_sources = some 209403308139690186 := by decide +kernel
private theorem endpoint_12_42_window_0 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 2 209403308139690186 = some 209403308139690186 := by decide +kernel
private theorem endpoint_12_42_window_2 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 2 2 209403308139690186 = some 209403308139690186 := by decide +kernel
private theorem endpoint_12_42_prefix_4 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 4 209403308139690186 = some 209403308139690186 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 2 2 209403308139690186 209403308139690186 209403308139690186 endpoint_12_42_window_0 endpoint_12_42_window_2
private theorem endpoint_12_42_window_4 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 4 2 209403308139690186 = some 209403308139690186 := by decide +kernel
private theorem endpoint_12_42_prefix_6 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 6 209403308139690186 = some 209403308139690186 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 4 2 209403308139690186 209403308139690186 209403308139690186 endpoint_12_42_prefix_4 endpoint_12_42_window_4
private theorem endpoint_12_42_window_6 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 6 2 209403308139690186 = some 209403308139690186 := by decide +kernel
private theorem endpoint_12_42_prefix_8 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 8 209403308139690186 = some 209403308139690186 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 6 2 209403308139690186 209403308139690186 209403308139690186 endpoint_12_42_prefix_6 endpoint_12_42_window_6
private theorem endpoint_12_42_window_8 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 8 2 209403308139690186 = some 209403308139690186 := by decide +kernel
private theorem endpoint_12_42_prefix_10 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 10 209403308139690186 = some 209403308139690186 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 8 2 209403308139690186 209403308139690186 209403308139690186 endpoint_12_42_prefix_8 endpoint_12_42_window_8
private theorem endpoint_12_42_window_10 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 10 1 209403308139690186 = some 209403308139690186 := by decide +kernel
private theorem endpoint_12_42_prefix_11 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 11 209403308139690186 = some 209403308139690186 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 10 1 209403308139690186 209403308139690186 209403308139690186 endpoint_12_42_prefix_10 endpoint_12_42_window_10

def endpoint_12_42 : CertifiedEndpoint :=
  ⟨⟨12, 42, 3400⟩, 209403308139690186, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_42_flag endpoint_12_42_sources 11 209403308139690186 209403308139690186 rfl endpoint_12_42_base endpoint_12_42_prefix_11) (by decide)⟩
private def endpoint_12_43_flag : Flag := ⟨12, 43, 3371⟩
private def endpoint_12_43_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_43_base : receiptBase endpoint_12_43_flag endpoint_12_43_sources = some 211821615060537391 := by decide +kernel
private theorem endpoint_12_43_window_0 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 2 211821615060537391 = some 212392385681707662 := by decide +kernel
private theorem endpoint_12_43_window_2 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 2 2 212392385681707662 = some 212392385681707662 := by decide +kernel
private theorem endpoint_12_43_prefix_4 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 4 211821615060537391 = some 212392385681707662 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 2 2 211821615060537391 212392385681707662 212392385681707662 endpoint_12_43_window_0 endpoint_12_43_window_2
private theorem endpoint_12_43_window_4 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 4 2 212392385681707662 = some 212392385681707662 := by decide +kernel
private theorem endpoint_12_43_prefix_6 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 6 211821615060537391 = some 212392385681707662 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 4 2 211821615060537391 212392385681707662 212392385681707662 endpoint_12_43_prefix_4 endpoint_12_43_window_4
private theorem endpoint_12_43_window_6 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 6 2 212392385681707662 = some 212392385681707662 := by decide +kernel
private theorem endpoint_12_43_prefix_8 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 8 211821615060537391 = some 212392385681707662 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 6 2 211821615060537391 212392385681707662 212392385681707662 endpoint_12_43_prefix_6 endpoint_12_43_window_6
private theorem endpoint_12_43_window_8 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 8 2 212392385681707662 = some 212392385681707662 := by decide +kernel
private theorem endpoint_12_43_prefix_10 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 10 211821615060537391 = some 212392385681707662 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 8 2 211821615060537391 212392385681707662 212392385681707662 endpoint_12_43_prefix_8 endpoint_12_43_window_8
private theorem endpoint_12_43_window_10 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 10 1 212392385681707662 = some 212392385681707662 := by decide +kernel
private theorem endpoint_12_43_prefix_11 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 11 211821615060537391 = some 212392385681707662 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 10 1 211821615060537391 212392385681707662 212392385681707662 endpoint_12_43_prefix_10 endpoint_12_43_window_10

def endpoint_12_43 : CertifiedEndpoint :=
  ⟨⟨12, 43, 3371⟩, 212392385681707662, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_43_flag endpoint_12_43_sources 11 211821615060537391 212392385681707662 rfl endpoint_12_43_base endpoint_12_43_prefix_11) (by decide)⟩
private def endpoint_12_44_flag : Flag := ⟨12, 44, 3342⟩
private def endpoint_12_44_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_44_base : receiptBase endpoint_12_44_flag endpoint_12_44_sources = some 214168138739675019 := by decide +kernel
private theorem endpoint_12_44_window_0 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 2 214168138739675019 = some 217292026550509720 := by decide +kernel
private theorem endpoint_12_44_window_2 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 2 2 217292026550509720 = some 217292026550509720 := by decide +kernel
private theorem endpoint_12_44_prefix_4 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 4 214168138739675019 = some 217292026550509720 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 2 2 214168138739675019 217292026550509720 217292026550509720 endpoint_12_44_window_0 endpoint_12_44_window_2
private theorem endpoint_12_44_window_4 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 4 2 217292026550509720 = some 217292026550509720 := by decide +kernel
private theorem endpoint_12_44_prefix_6 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 6 214168138739675019 = some 217292026550509720 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 4 2 214168138739675019 217292026550509720 217292026550509720 endpoint_12_44_prefix_4 endpoint_12_44_window_4
private theorem endpoint_12_44_window_6 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 6 2 217292026550509720 = some 217292026550509720 := by decide +kernel
private theorem endpoint_12_44_prefix_8 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 8 214168138739675019 = some 217292026550509720 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 6 2 214168138739675019 217292026550509720 217292026550509720 endpoint_12_44_prefix_6 endpoint_12_44_window_6
private theorem endpoint_12_44_window_8 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 8 2 217292026550509720 = some 217292026550509720 := by decide +kernel
private theorem endpoint_12_44_prefix_10 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 10 214168138739675019 = some 217292026550509720 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 8 2 214168138739675019 217292026550509720 217292026550509720 endpoint_12_44_prefix_8 endpoint_12_44_window_8
private theorem endpoint_12_44_window_10 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 10 1 217292026550509720 = some 217292026550509720 := by decide +kernel
private theorem endpoint_12_44_prefix_11 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 11 214168138739675019 = some 217292026550509720 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 10 1 214168138739675019 217292026550509720 217292026550509720 endpoint_12_44_prefix_10 endpoint_12_44_window_10

def endpoint_12_44 : CertifiedEndpoint :=
  ⟨⟨12, 44, 3342⟩, 217292026550509720, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_44_flag endpoint_12_44_sources 11 214168138739675019 217292026550509720 rfl endpoint_12_44_base endpoint_12_44_prefix_11) (by decide)⟩
private def endpoint_12_45_flag : Flag := ⟨12, 45, 3312⟩
private def endpoint_12_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_45_base : receiptBase endpoint_12_45_flag endpoint_12_45_sources = some 216378602267278026 := by decide +kernel
private theorem endpoint_12_45_window_0 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 2 216378602267278026 = some 222104211059456523 := by decide +kernel
private theorem endpoint_12_45_window_2 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 2 2 222104211059456523 = some 222104211059456523 := by decide +kernel
private theorem endpoint_12_45_prefix_4 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 4 216378602267278026 = some 222104211059456523 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 2 2 216378602267278026 222104211059456523 222104211059456523 endpoint_12_45_window_0 endpoint_12_45_window_2
private theorem endpoint_12_45_window_4 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 4 2 222104211059456523 = some 222104211059456523 := by decide +kernel
private theorem endpoint_12_45_prefix_6 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 6 216378602267278026 = some 222104211059456523 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 4 2 216378602267278026 222104211059456523 222104211059456523 endpoint_12_45_prefix_4 endpoint_12_45_window_4
private theorem endpoint_12_45_window_6 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 6 2 222104211059456523 = some 222104211059456523 := by decide +kernel
private theorem endpoint_12_45_prefix_8 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 8 216378602267278026 = some 222104211059456523 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 6 2 216378602267278026 222104211059456523 222104211059456523 endpoint_12_45_prefix_6 endpoint_12_45_window_6
private theorem endpoint_12_45_window_8 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 8 2 222104211059456523 = some 222104211059456523 := by decide +kernel
private theorem endpoint_12_45_prefix_10 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 10 216378602267278026 = some 222104211059456523 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 8 2 216378602267278026 222104211059456523 222104211059456523 endpoint_12_45_prefix_8 endpoint_12_45_window_8
private theorem endpoint_12_45_window_10 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 10 1 222104211059456523 = some 222104211059456523 := by decide +kernel
private theorem endpoint_12_45_prefix_11 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 11 216378602267278026 = some 222104211059456523 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 10 1 216378602267278026 222104211059456523 222104211059456523 endpoint_12_45_prefix_10 endpoint_12_45_window_10

def endpoint_12_45 : CertifiedEndpoint :=
  ⟨⟨12, 45, 3312⟩, 222104211059456523, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_45_flag endpoint_12_45_sources 11 216378602267278026 222104211059456523 rfl endpoint_12_45_base endpoint_12_45_prefix_11) (by decide)⟩
private def endpoint_12_46_flag : Flag := ⟨12, 46, 3281⟩
private def endpoint_12_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_46_base : receiptBase endpoint_12_46_flag endpoint_12_46_sources = some 218449355648005247 := by decide +kernel
private theorem endpoint_12_46_window_0 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 2 218449355648005247 = some 226826284851322194 := by decide +kernel
private theorem endpoint_12_46_window_2 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 2 2 226826284851322194 = some 226826284851322194 := by decide +kernel
private theorem endpoint_12_46_prefix_4 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 4 218449355648005247 = some 226826284851322194 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 2 2 218449355648005247 226826284851322194 226826284851322194 endpoint_12_46_window_0 endpoint_12_46_window_2
private theorem endpoint_12_46_window_4 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 4 2 226826284851322194 = some 226826284851322194 := by decide +kernel
private theorem endpoint_12_46_prefix_6 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 6 218449355648005247 = some 226826284851322194 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 4 2 218449355648005247 226826284851322194 226826284851322194 endpoint_12_46_prefix_4 endpoint_12_46_window_4
private theorem endpoint_12_46_window_6 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 6 2 226826284851322194 = some 226826284851322194 := by decide +kernel
private theorem endpoint_12_46_prefix_8 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 8 218449355648005247 = some 226826284851322194 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 6 2 218449355648005247 226826284851322194 226826284851322194 endpoint_12_46_prefix_6 endpoint_12_46_window_6
private theorem endpoint_12_46_window_8 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 8 2 226826284851322194 = some 226826284851322194 := by decide +kernel
private theorem endpoint_12_46_prefix_10 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 10 218449355648005247 = some 226826284851322194 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 8 2 218449355648005247 226826284851322194 226826284851322194 endpoint_12_46_prefix_8 endpoint_12_46_window_8
private theorem endpoint_12_46_window_10 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 10 1 226826284851322194 = some 226826284851322194 := by decide +kernel
private theorem endpoint_12_46_prefix_11 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 11 218449355648005247 = some 226826284851322194 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 10 1 218449355648005247 226826284851322194 226826284851322194 endpoint_12_46_prefix_10 endpoint_12_46_window_10

def endpoint_12_46 : CertifiedEndpoint :=
  ⟨⟨12, 46, 3281⟩, 226826284851322194, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_46_flag endpoint_12_46_sources 11 218449355648005247 226826284851322194 rfl endpoint_12_46_base endpoint_12_46_prefix_11) (by decide)⟩
private def endpoint_12_47_flag : Flag := ⟨12, 47, 3250⟩
private def endpoint_12_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_47_base : receiptBase endpoint_12_47_flag endpoint_12_47_sources = some 220443459126568006 := by decide +kernel
private theorem endpoint_12_47_window_0 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 2 220443459126568006 = some 231490787439828565 := by decide +kernel
private theorem endpoint_12_47_window_2 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 2 2 231490787439828565 = some 231490787439828565 := by decide +kernel
private theorem endpoint_12_47_prefix_4 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 4 220443459126568006 = some 231490787439828565 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 2 2 220443459126568006 231490787439828565 231490787439828565 endpoint_12_47_window_0 endpoint_12_47_window_2
private theorem endpoint_12_47_window_4 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 4 2 231490787439828565 = some 231490787439828565 := by decide +kernel
private theorem endpoint_12_47_prefix_6 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 6 220443459126568006 = some 231490787439828565 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 4 2 220443459126568006 231490787439828565 231490787439828565 endpoint_12_47_prefix_4 endpoint_12_47_window_4
private theorem endpoint_12_47_window_6 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 6 2 231490787439828565 = some 231490787439828565 := by decide +kernel
private theorem endpoint_12_47_prefix_8 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 8 220443459126568006 = some 231490787439828565 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 6 2 220443459126568006 231490787439828565 231490787439828565 endpoint_12_47_prefix_6 endpoint_12_47_window_6
private theorem endpoint_12_47_window_8 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 8 2 231490787439828565 = some 231490787439828565 := by decide +kernel
private theorem endpoint_12_47_prefix_10 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 10 220443459126568006 = some 231490787439828565 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 8 2 220443459126568006 231490787439828565 231490787439828565 endpoint_12_47_prefix_8 endpoint_12_47_window_8
private theorem endpoint_12_47_window_10 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 10 1 231490787439828565 = some 231490787439828565 := by decide +kernel
private theorem endpoint_12_47_prefix_11 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 11 220443459126568006 = some 231490787439828565 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 10 1 220443459126568006 231490787439828565 231490787439828565 endpoint_12_47_prefix_10 endpoint_12_47_window_10

def endpoint_12_47 : CertifiedEndpoint :=
  ⟨⟨12, 47, 3250⟩, 231490787439828565, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_47_flag endpoint_12_47_sources 11 220443459126568006 231490787439828565 rfl endpoint_12_47_base endpoint_12_47_prefix_11) (by decide)⟩
private def endpoint_12_48_flag : Flag := ⟨12, 48, 3217⟩
private def endpoint_12_48_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_48_base : receiptBase endpoint_12_48_flag endpoint_12_48_sources = some 222738441058306133 := by decide +kernel
private theorem endpoint_12_48_window_0 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 2 222738441058306133 = some 228167429346152844 := by decide +kernel
private theorem endpoint_12_48_window_2 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 2 2 228167429346152844 = some 228167429346152844 := by decide +kernel
private theorem endpoint_12_48_prefix_4 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 4 222738441058306133 = some 228167429346152844 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 2 2 222738441058306133 228167429346152844 228167429346152844 endpoint_12_48_window_0 endpoint_12_48_window_2
private theorem endpoint_12_48_window_4 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 4 2 228167429346152844 = some 228167429346152844 := by decide +kernel
private theorem endpoint_12_48_prefix_6 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 6 222738441058306133 = some 228167429346152844 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 4 2 222738441058306133 228167429346152844 228167429346152844 endpoint_12_48_prefix_4 endpoint_12_48_window_4
private theorem endpoint_12_48_window_6 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 6 2 228167429346152844 = some 228167429346152844 := by decide +kernel
private theorem endpoint_12_48_prefix_8 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 8 222738441058306133 = some 228167429346152844 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 6 2 222738441058306133 228167429346152844 228167429346152844 endpoint_12_48_prefix_6 endpoint_12_48_window_6
private theorem endpoint_12_48_window_8 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 8 2 228167429346152844 = some 228167429346152844 := by decide +kernel
private theorem endpoint_12_48_prefix_10 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 10 222738441058306133 = some 228167429346152844 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 8 2 222738441058306133 228167429346152844 228167429346152844 endpoint_12_48_prefix_8 endpoint_12_48_window_8
private theorem endpoint_12_48_window_10 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 10 1 228167429346152844 = some 228167429346152844 := by decide +kernel
private theorem endpoint_12_48_prefix_11 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 11 222738441058306133 = some 228167429346152844 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 10 1 222738441058306133 228167429346152844 228167429346152844 endpoint_12_48_prefix_10 endpoint_12_48_window_10

def endpoint_12_48 : CertifiedEndpoint :=
  ⟨⟨12, 48, 3217⟩, 228167429346152844, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_48_flag endpoint_12_48_sources 11 222738441058306133 228167429346152844 rfl endpoint_12_48_base endpoint_12_48_prefix_11) (by decide)⟩
private def endpoint_12_49_flag : Flag := ⟨12, 49, 3184⟩
private def endpoint_12_49_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_49_base : receiptBase endpoint_12_49_flag endpoint_12_49_sources = some 224447123577776930 := by decide +kernel
private theorem endpoint_12_49_window_0 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 2 224447123577776930 = some 232450804103541611 := by decide +kernel
private theorem endpoint_12_49_window_2 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 2 2 232450804103541611 = some 232450804103541611 := by decide +kernel
private theorem endpoint_12_49_prefix_4 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 4 224447123577776930 = some 232450804103541611 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 2 2 224447123577776930 232450804103541611 232450804103541611 endpoint_12_49_window_0 endpoint_12_49_window_2
private theorem endpoint_12_49_window_4 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 4 2 232450804103541611 = some 232450804103541611 := by decide +kernel
private theorem endpoint_12_49_prefix_6 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 6 224447123577776930 = some 232450804103541611 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 4 2 224447123577776930 232450804103541611 232450804103541611 endpoint_12_49_prefix_4 endpoint_12_49_window_4
private theorem endpoint_12_49_window_6 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 6 2 232450804103541611 = some 232450804103541611 := by decide +kernel
private theorem endpoint_12_49_prefix_8 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 8 224447123577776930 = some 232450804103541611 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 6 2 224447123577776930 232450804103541611 232450804103541611 endpoint_12_49_prefix_6 endpoint_12_49_window_6
private theorem endpoint_12_49_window_8 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 8 2 232450804103541611 = some 232450804103541611 := by decide +kernel
private theorem endpoint_12_49_prefix_10 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 10 224447123577776930 = some 232450804103541611 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 8 2 224447123577776930 232450804103541611 232450804103541611 endpoint_12_49_prefix_8 endpoint_12_49_window_8
private theorem endpoint_12_49_window_10 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 10 1 232450804103541611 = some 232450804103541611 := by decide +kernel
private theorem endpoint_12_49_prefix_11 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 11 224447123577776930 = some 232450804103541611 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 10 1 224447123577776930 232450804103541611 232450804103541611 endpoint_12_49_prefix_10 endpoint_12_49_window_10

def endpoint_12_49 : CertifiedEndpoint :=
  ⟨⟨12, 49, 3184⟩, 232450804103541611, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_49_flag endpoint_12_49_sources 11 224447123577776930 232450804103541611 rfl endpoint_12_49_base endpoint_12_49_prefix_11) (by decide)⟩
private def endpoint_12_50_flag : Flag := ⟨12, 50, 3151⟩
private def endpoint_12_50_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_50_base : receiptBase endpoint_12_50_flag endpoint_12_50_sources = some 226073983510601466 := by decide +kernel
private theorem endpoint_12_50_window_0 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 2 226073983510601466 = some 236673068514603242 := by decide +kernel
private theorem endpoint_12_50_window_2 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 2 2 236673068514603242 = some 236673068514603242 := by decide +kernel
private theorem endpoint_12_50_prefix_4 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 4 226073983510601466 = some 236673068514603242 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 2 2 226073983510601466 236673068514603242 236673068514603242 endpoint_12_50_window_0 endpoint_12_50_window_2
private theorem endpoint_12_50_window_4 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 4 2 236673068514603242 = some 236673068514603242 := by decide +kernel
private theorem endpoint_12_50_prefix_6 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 6 226073983510601466 = some 236673068514603242 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 4 2 226073983510601466 236673068514603242 236673068514603242 endpoint_12_50_prefix_4 endpoint_12_50_window_4
private theorem endpoint_12_50_window_6 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 6 2 236673068514603242 = some 236673068514603242 := by decide +kernel
private theorem endpoint_12_50_prefix_8 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 8 226073983510601466 = some 236673068514603242 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 6 2 226073983510601466 236673068514603242 236673068514603242 endpoint_12_50_prefix_6 endpoint_12_50_window_6
private theorem endpoint_12_50_window_8 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 8 2 236673068514603242 = some 236673068514603242 := by decide +kernel
private theorem endpoint_12_50_prefix_10 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 10 226073983510601466 = some 236673068514603242 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 8 2 226073983510601466 236673068514603242 236673068514603242 endpoint_12_50_prefix_8 endpoint_12_50_window_8
private theorem endpoint_12_50_window_10 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 10 1 236673068514603242 = some 236673068514603242 := by decide +kernel
private theorem endpoint_12_50_prefix_11 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 11 226073983510601466 = some 236673068514603242 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 10 1 226073983510601466 236673068514603242 236673068514603242 endpoint_12_50_prefix_10 endpoint_12_50_window_10

def endpoint_12_50 : CertifiedEndpoint :=
  ⟨⟨12, 50, 3151⟩, 236673068514603242, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_50_flag endpoint_12_50_sources 11 226073983510601466 236673068514603242 rfl endpoint_12_50_base endpoint_12_50_prefix_11) (by decide)⟩
private def endpoint_12_51_flag : Flag := ⟨12, 51, 3116⟩
private def endpoint_12_51_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_51_base : receiptBase endpoint_12_51_flag endpoint_12_51_sources = some 227475516027333527 := by decide +kernel
private theorem endpoint_12_51_window_0 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 2 227475516027333527 = some 240756756551506647 := by decide +kernel
private theorem endpoint_12_51_window_2 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 2 2 240756756551506647 = some 240756756551506647 := by decide +kernel
private theorem endpoint_12_51_prefix_4 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 4 227475516027333527 = some 240756756551506647 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 2 2 227475516027333527 240756756551506647 240756756551506647 endpoint_12_51_window_0 endpoint_12_51_window_2
private theorem endpoint_12_51_window_4 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 4 2 240756756551506647 = some 240756756551506647 := by decide +kernel
private theorem endpoint_12_51_prefix_6 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 6 227475516027333527 = some 240756756551506647 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 4 2 227475516027333527 240756756551506647 240756756551506647 endpoint_12_51_prefix_4 endpoint_12_51_window_4
private theorem endpoint_12_51_window_6 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 6 2 240756756551506647 = some 240756756551506647 := by decide +kernel
private theorem endpoint_12_51_prefix_8 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 8 227475516027333527 = some 240756756551506647 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 6 2 227475516027333527 240756756551506647 240756756551506647 endpoint_12_51_prefix_6 endpoint_12_51_window_6
private theorem endpoint_12_51_window_8 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 8 2 240756756551506647 = some 240756756551506647 := by decide +kernel
private theorem endpoint_12_51_prefix_10 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 10 227475516027333527 = some 240756756551506647 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 8 2 227475516027333527 240756756551506647 240756756551506647 endpoint_12_51_prefix_8 endpoint_12_51_window_8
private theorem endpoint_12_51_window_10 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 10 1 240756756551506647 = some 240756756551506647 := by decide +kernel
private theorem endpoint_12_51_prefix_11 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 11 227475516027333527 = some 240756756551506647 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 10 1 227475516027333527 240756756551506647 240756756551506647 endpoint_12_51_prefix_10 endpoint_12_51_window_10

def endpoint_12_51 : CertifiedEndpoint :=
  ⟨⟨12, 51, 3116⟩, 240756756551506647, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_51_flag endpoint_12_51_sources 11 227475516027333527 240756756551506647 rfl endpoint_12_51_base endpoint_12_51_prefix_11) (by decide)⟩
private def endpoint_12_52_flag : Flag := ⟨12, 52, 3081⟩
private def endpoint_12_52_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_12_52_base : receiptBase endpoint_12_52_flag endpoint_12_52_sources = some 229631970558000105 := by decide +kernel
private theorem endpoint_12_52_window_0 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 2 229631970558000105 = some 240797662158660872 := by decide +kernel
private theorem endpoint_12_52_window_2 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 2 2 240797662158660872 = some 240797662158660872 := by decide +kernel
private theorem endpoint_12_52_prefix_4 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 4 229631970558000105 = some 240797662158660872 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 2 2 229631970558000105 240797662158660872 240797662158660872 endpoint_12_52_window_0 endpoint_12_52_window_2
private theorem endpoint_12_52_window_4 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 4 2 240797662158660872 = some 240797662158660872 := by decide +kernel
private theorem endpoint_12_52_prefix_6 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 6 229631970558000105 = some 240797662158660872 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 4 2 229631970558000105 240797662158660872 240797662158660872 endpoint_12_52_prefix_4 endpoint_12_52_window_4
private theorem endpoint_12_52_window_6 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 6 2 240797662158660872 = some 240797662158660872 := by decide +kernel
private theorem endpoint_12_52_prefix_8 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 8 229631970558000105 = some 240797662158660872 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 6 2 229631970558000105 240797662158660872 240797662158660872 endpoint_12_52_prefix_6 endpoint_12_52_window_6
private theorem endpoint_12_52_window_8 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 8 2 240797662158660872 = some 240797662158660872 := by decide +kernel
private theorem endpoint_12_52_prefix_10 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 10 229631970558000105 = some 240797662158660872 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 8 2 229631970558000105 240797662158660872 240797662158660872 endpoint_12_52_prefix_8 endpoint_12_52_window_8
private theorem endpoint_12_52_window_10 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 10 1 240797662158660872 = some 240797662158660872 := by decide +kernel
private theorem endpoint_12_52_prefix_11 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 11 229631970558000105 = some 240797662158660872 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 10 1 229631970558000105 240797662158660872 240797662158660872 endpoint_12_52_prefix_10 endpoint_12_52_window_10

def endpoint_12_52 : CertifiedEndpoint :=
  ⟨⟨12, 52, 3081⟩, 240797662158660872, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_12_52_flag endpoint_12_52_sources 11 229631970558000105 240797662158660872 rfl endpoint_12_52_base endpoint_12_52_prefix_11) (by decide)⟩
private def endpoint_12_53_flag : Flag := ⟨12, 53, 3044⟩
private def endpoint_12_53_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_53_base : receiptBase endpoint_12_53_flag endpoint_12_53_sources = some 232383280111145154 := by decide +kernel
private theorem endpoint_12_53_window_0 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 2 232383280111145154 = some 237637207729501345 := by decide +kernel
private theorem endpoint_12_53_window_2 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 2 2 237637207729501345 = some 237637207729501345 := by decide +kernel
private theorem endpoint_12_53_prefix_4 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 4 232383280111145154 = some 237637207729501345 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 2 2 232383280111145154 237637207729501345 237637207729501345 endpoint_12_53_window_0 endpoint_12_53_window_2
private theorem endpoint_12_53_window_4 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 4 2 237637207729501345 = some 237637207729501345 := by decide +kernel
private theorem endpoint_12_53_prefix_6 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 6 232383280111145154 = some 237637207729501345 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 4 2 232383280111145154 237637207729501345 237637207729501345 endpoint_12_53_prefix_4 endpoint_12_53_window_4
private theorem endpoint_12_53_window_6 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 6 2 237637207729501345 = some 237637207729501345 := by decide +kernel
private theorem endpoint_12_53_prefix_8 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 8 232383280111145154 = some 237637207729501345 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 6 2 232383280111145154 237637207729501345 237637207729501345 endpoint_12_53_prefix_6 endpoint_12_53_window_6
private theorem endpoint_12_53_window_8 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 8 2 237637207729501345 = some 237637207729501345 := by decide +kernel
private theorem endpoint_12_53_prefix_10 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 10 232383280111145154 = some 237637207729501345 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 8 2 232383280111145154 237637207729501345 237637207729501345 endpoint_12_53_prefix_8 endpoint_12_53_window_8
private theorem endpoint_12_53_window_10 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 10 1 237637207729501345 = some 237637207729501345 := by decide +kernel
private theorem endpoint_12_53_prefix_11 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 11 232383280111145154 = some 237637207729501345 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 10 1 232383280111145154 237637207729501345 237637207729501345 endpoint_12_53_prefix_10 endpoint_12_53_window_10

def endpoint_12_53 : CertifiedEndpoint :=
  ⟨⟨12, 53, 3044⟩, 237637207729501345, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_53_flag endpoint_12_53_sources 11 232383280111145154 237637207729501345 rfl endpoint_12_53_base endpoint_12_53_prefix_11) (by decide)⟩
private def endpoint_12_54_flag : Flag := ⟨12, 54, 3006⟩
private def endpoint_12_54_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_54_base : receiptBase endpoint_12_54_flag endpoint_12_54_sources = some 233252770495510306 := by decide +kernel
private theorem endpoint_12_54_window_0 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 2 233252770495510306 = some 241163154403546860 := by decide +kernel
private theorem endpoint_12_54_window_2 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 2 2 241163154403546860 = some 241163154403546860 := by decide +kernel
private theorem endpoint_12_54_prefix_4 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 4 233252770495510306 = some 241163154403546860 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 2 2 233252770495510306 241163154403546860 241163154403546860 endpoint_12_54_window_0 endpoint_12_54_window_2
private theorem endpoint_12_54_window_4 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 4 2 241163154403546860 = some 241163154403546860 := by decide +kernel
private theorem endpoint_12_54_prefix_6 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 6 233252770495510306 = some 241163154403546860 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 4 2 233252770495510306 241163154403546860 241163154403546860 endpoint_12_54_prefix_4 endpoint_12_54_window_4
private theorem endpoint_12_54_window_6 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 6 2 241163154403546860 = some 241163154403546860 := by decide +kernel
private theorem endpoint_12_54_prefix_8 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 8 233252770495510306 = some 241163154403546860 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 6 2 233252770495510306 241163154403546860 241163154403546860 endpoint_12_54_prefix_6 endpoint_12_54_window_6
private theorem endpoint_12_54_window_8 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 8 2 241163154403546860 = some 241163154403546860 := by decide +kernel
private theorem endpoint_12_54_prefix_10 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 10 233252770495510306 = some 241163154403546860 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 8 2 233252770495510306 241163154403546860 241163154403546860 endpoint_12_54_prefix_8 endpoint_12_54_window_8
private theorem endpoint_12_54_window_10 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 10 1 241163154403546860 = some 241163154403546860 := by decide +kernel
private theorem endpoint_12_54_prefix_11 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 11 233252770495510306 = some 241163154403546860 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 10 1 233252770495510306 241163154403546860 241163154403546860 endpoint_12_54_prefix_10 endpoint_12_54_window_10

def endpoint_12_54 : CertifiedEndpoint :=
  ⟨⟨12, 54, 3006⟩, 241163154403546860, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_54_flag endpoint_12_54_sources 11 233252770495510306 241163154403546860 rfl endpoint_12_54_base endpoint_12_54_prefix_11) (by decide)⟩
private def endpoint_12_55_flag : Flag := ⟨12, 55, 2968⟩
private def endpoint_12_55_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_55_base : receiptBase endpoint_12_55_flag endpoint_12_55_sources = some 234027885019349603 := by decide +kernel
private theorem endpoint_12_55_window_0 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 2 234027885019349603 = some 244619142873845649 := by decide +kernel
private theorem endpoint_12_55_window_2 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 2 2 244619142873845649 = some 244619142873845649 := by decide +kernel
private theorem endpoint_12_55_prefix_4 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 4 234027885019349603 = some 244619142873845649 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 2 2 234027885019349603 244619142873845649 244619142873845649 endpoint_12_55_window_0 endpoint_12_55_window_2
private theorem endpoint_12_55_window_4 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 4 2 244619142873845649 = some 244619142873845649 := by decide +kernel
private theorem endpoint_12_55_prefix_6 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 6 234027885019349603 = some 244619142873845649 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 4 2 234027885019349603 244619142873845649 244619142873845649 endpoint_12_55_prefix_4 endpoint_12_55_window_4
private theorem endpoint_12_55_window_6 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 6 2 244619142873845649 = some 244619142873845649 := by decide +kernel
private theorem endpoint_12_55_prefix_8 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 8 234027885019349603 = some 244619142873845649 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 6 2 234027885019349603 244619142873845649 244619142873845649 endpoint_12_55_prefix_6 endpoint_12_55_window_6
private theorem endpoint_12_55_window_8 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 8 2 244619142873845649 = some 244619142873845649 := by decide +kernel
private theorem endpoint_12_55_prefix_10 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 10 234027885019349603 = some 244619142873845649 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 8 2 234027885019349603 244619142873845649 244619142873845649 endpoint_12_55_prefix_8 endpoint_12_55_window_8
private theorem endpoint_12_55_window_10 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 10 1 244619142873845649 = some 244619142873845649 := by decide +kernel
private theorem endpoint_12_55_prefix_11 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 11 234027885019349603 = some 244619142873845649 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 10 1 234027885019349603 244619142873845649 244619142873845649 endpoint_12_55_prefix_10 endpoint_12_55_window_10

def endpoint_12_55 : CertifiedEndpoint :=
  ⟨⟨12, 55, 2968⟩, 244619142873845649, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_55_flag endpoint_12_55_sources 11 234027885019349603 244619142873845649 rfl endpoint_12_55_base endpoint_12_55_prefix_11) (by decide)⟩
private def endpoint_12_56_flag : Flag := ⟨12, 56, 2927⟩
private def endpoint_12_56_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_56_base : receiptBase endpoint_12_56_flag endpoint_12_56_sources = some 234471781852164912 := by decide +kernel
private theorem endpoint_12_56_window_0 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 2 234471781852164912 = some 247875702312521692 := by decide +kernel
private theorem endpoint_12_56_window_2 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 2 2 247875702312521692 = some 247875702312521692 := by decide +kernel
private theorem endpoint_12_56_prefix_4 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 4 234471781852164912 = some 247875702312521692 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 2 2 234471781852164912 247875702312521692 247875702312521692 endpoint_12_56_window_0 endpoint_12_56_window_2
private theorem endpoint_12_56_window_4 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 4 2 247875702312521692 = some 247875702312521692 := by decide +kernel
private theorem endpoint_12_56_prefix_6 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 6 234471781852164912 = some 247875702312521692 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 4 2 234471781852164912 247875702312521692 247875702312521692 endpoint_12_56_prefix_4 endpoint_12_56_window_4
private theorem endpoint_12_56_window_6 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 6 2 247875702312521692 = some 247875702312521692 := by decide +kernel
private theorem endpoint_12_56_prefix_8 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 8 234471781852164912 = some 247875702312521692 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 6 2 234471781852164912 247875702312521692 247875702312521692 endpoint_12_56_prefix_6 endpoint_12_56_window_6
private theorem endpoint_12_56_window_8 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 8 2 247875702312521692 = some 247875702312521692 := by decide +kernel
private theorem endpoint_12_56_prefix_10 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 10 234471781852164912 = some 247875702312521692 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 8 2 234471781852164912 247875702312521692 247875702312521692 endpoint_12_56_prefix_8 endpoint_12_56_window_8
private theorem endpoint_12_56_window_10 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 10 1 247875702312521692 = some 247875702312521692 := by decide +kernel
private theorem endpoint_12_56_prefix_11 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 11 234471781852164912 = some 247875702312521692 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 10 1 234471781852164912 247875702312521692 247875702312521692 endpoint_12_56_prefix_10 endpoint_12_56_window_10

def endpoint_12_56 : CertifiedEndpoint :=
  ⟨⟨12, 56, 2927⟩, 247875702312521692, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_56_flag endpoint_12_56_sources 11 234471781852164912 247875702312521692 rfl endpoint_12_56_base endpoint_12_56_prefix_11) (by decide)⟩
private def endpoint_12_57_flag : Flag := ⟨12, 57, 2886⟩
private def endpoint_12_57_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_12_57_base : receiptBase endpoint_12_57_flag endpoint_12_57_sources = some 235765791376745178 := by decide +kernel
private theorem endpoint_12_57_window_0 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 2 235765791376745178 = some 243602866341550164 := by decide +kernel
private theorem endpoint_12_57_window_2 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 2 2 243602866341550164 = some 243602866341550164 := by decide +kernel
private theorem endpoint_12_57_prefix_4 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 4 235765791376745178 = some 243602866341550164 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 2 2 235765791376745178 243602866341550164 243602866341550164 endpoint_12_57_window_0 endpoint_12_57_window_2
private theorem endpoint_12_57_window_4 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 4 2 243602866341550164 = some 243602866341550164 := by decide +kernel
private theorem endpoint_12_57_prefix_6 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 6 235765791376745178 = some 243602866341550164 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 4 2 235765791376745178 243602866341550164 243602866341550164 endpoint_12_57_prefix_4 endpoint_12_57_window_4
private theorem endpoint_12_57_window_6 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 6 2 243602866341550164 = some 243602866341550164 := by decide +kernel
private theorem endpoint_12_57_prefix_8 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 8 235765791376745178 = some 243602866341550164 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 6 2 235765791376745178 243602866341550164 243602866341550164 endpoint_12_57_prefix_6 endpoint_12_57_window_6
private theorem endpoint_12_57_window_8 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 8 2 243602866341550164 = some 243602866341550164 := by decide +kernel
private theorem endpoint_12_57_prefix_10 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 10 235765791376745178 = some 243602866341550164 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 8 2 235765791376745178 243602866341550164 243602866341550164 endpoint_12_57_prefix_8 endpoint_12_57_window_8
private theorem endpoint_12_57_window_10 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 10 1 243602866341550164 = some 243602866341550164 := by decide +kernel
private theorem endpoint_12_57_prefix_11 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 11 235765791376745178 = some 243602866341550164 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 10 1 235765791376745178 243602866341550164 243602866341550164 endpoint_12_57_prefix_10 endpoint_12_57_window_10

def endpoint_12_57 : CertifiedEndpoint :=
  ⟨⟨12, 57, 2886⟩, 243602866341550164, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_12_57_flag endpoint_12_57_sources 11 235765791376745178 243602866341550164 rfl endpoint_12_57_base endpoint_12_57_prefix_11) (by decide)⟩
private def endpoint_12_58_flag : Flag := ⟨12, 58, 2843⟩
private def endpoint_12_58_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_12_58_base : receiptBase endpoint_12_58_flag endpoint_12_58_sources = some 235846852166914067 := by decide +kernel
private theorem endpoint_12_58_window_0 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 2 235846852166914067 = some 246470833084724208 := by decide +kernel
private theorem endpoint_12_58_window_2 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 2 2 246470833084724208 = some 246470833084724208 := by decide +kernel
private theorem endpoint_12_58_prefix_4 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 4 235846852166914067 = some 246470833084724208 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 2 2 235846852166914067 246470833084724208 246470833084724208 endpoint_12_58_window_0 endpoint_12_58_window_2
private theorem endpoint_12_58_window_4 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 4 2 246470833084724208 = some 246470833084724208 := by decide +kernel
private theorem endpoint_12_58_prefix_6 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 6 235846852166914067 = some 246470833084724208 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 4 2 235846852166914067 246470833084724208 246470833084724208 endpoint_12_58_prefix_4 endpoint_12_58_window_4
private theorem endpoint_12_58_window_6 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 6 2 246470833084724208 = some 246470833084724208 := by decide +kernel
private theorem endpoint_12_58_prefix_8 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 8 235846852166914067 = some 246470833084724208 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 6 2 235846852166914067 246470833084724208 246470833084724208 endpoint_12_58_prefix_6 endpoint_12_58_window_6
private theorem endpoint_12_58_window_8 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 8 2 246470833084724208 = some 246470833084724208 := by decide +kernel
private theorem endpoint_12_58_prefix_10 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 10 235846852166914067 = some 246470833084724208 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 8 2 235846852166914067 246470833084724208 246470833084724208 endpoint_12_58_prefix_8 endpoint_12_58_window_8
private theorem endpoint_12_58_window_10 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 10 1 246470833084724208 = some 246470833084724208 := by decide +kernel
private theorem endpoint_12_58_prefix_11 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 11 235846852166914067 = some 246470833084724208 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 10 1 235846852166914067 246470833084724208 246470833084724208 endpoint_12_58_prefix_10 endpoint_12_58_window_10

def endpoint_12_58 : CertifiedEndpoint :=
  ⟨⟨12, 58, 2843⟩, 246470833084724208, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_12_58_flag endpoint_12_58_sources 11 235846852166914067 246470833084724208 rfl endpoint_12_58_base endpoint_12_58_prefix_11) (by decide)⟩
private def endpoint_12_59_flag : Flag := ⟨12, 59, 2798⟩
private def endpoint_12_59_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_12_59_base : receiptBase endpoint_12_59_flag endpoint_12_59_sources = some 235654409387231647 := by decide +kernel
private theorem endpoint_12_59_window_0 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 2 235654409387231647 = some 249168371167029502 := by decide +kernel
private theorem endpoint_12_59_window_2 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 2 2 249168371167029502 = some 249168371167029502 := by decide +kernel
private theorem endpoint_12_59_prefix_4 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 4 235654409387231647 = some 249168371167029502 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 2 2 235654409387231647 249168371167029502 249168371167029502 endpoint_12_59_window_0 endpoint_12_59_window_2
private theorem endpoint_12_59_window_4 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 4 2 249168371167029502 = some 249168371167029502 := by decide +kernel
private theorem endpoint_12_59_prefix_6 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 6 235654409387231647 = some 249168371167029502 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 4 2 235654409387231647 249168371167029502 249168371167029502 endpoint_12_59_prefix_4 endpoint_12_59_window_4
private theorem endpoint_12_59_window_6 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 6 2 249168371167029502 = some 249168371167029502 := by decide +kernel
private theorem endpoint_12_59_prefix_8 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 8 235654409387231647 = some 249168371167029502 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 6 2 235654409387231647 249168371167029502 249168371167029502 endpoint_12_59_prefix_6 endpoint_12_59_window_6
private theorem endpoint_12_59_window_8 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 8 2 249168371167029502 = some 249168371167029502 := by decide +kernel
private theorem endpoint_12_59_prefix_10 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 10 235654409387231647 = some 249168371167029502 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 8 2 235654409387231647 249168371167029502 249168371167029502 endpoint_12_59_prefix_8 endpoint_12_59_window_8
private theorem endpoint_12_59_window_10 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 10 1 249168371167029502 = some 249168371167029502 := by decide +kernel
private theorem endpoint_12_59_prefix_11 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 11 235654409387231647 = some 249168371167029502 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 10 1 235654409387231647 249168371167029502 249168371167029502 endpoint_12_59_prefix_10 endpoint_12_59_window_10

def endpoint_12_59 : CertifiedEndpoint :=
  ⟨⟨12, 59, 2798⟩, 249168371167029502, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_12_59_flag endpoint_12_59_sources 11 235654409387231647 249168371167029502 rfl endpoint_12_59_base endpoint_12_59_prefix_11) (by decide)⟩
private def endpoint_12_60_flag : Flag := ⟨12, 60, 2751⟩
private def endpoint_12_60_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_12_60_base : receiptBase endpoint_12_60_flag endpoint_12_60_sources = some 236196967408752645 := by decide +kernel
private theorem endpoint_12_60_window_0 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 2 236196967408752645 = some 246034279687862412 := by decide +kernel
private theorem endpoint_12_60_window_2 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 2 2 246034279687862412 = some 246034279687862412 := by decide +kernel
private theorem endpoint_12_60_prefix_4 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 4 236196967408752645 = some 246034279687862412 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 2 2 236196967408752645 246034279687862412 246034279687862412 endpoint_12_60_window_0 endpoint_12_60_window_2
private theorem endpoint_12_60_window_4 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 4 2 246034279687862412 = some 246034279687862412 := by decide +kernel
private theorem endpoint_12_60_prefix_6 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 6 236196967408752645 = some 246034279687862412 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 4 2 236196967408752645 246034279687862412 246034279687862412 endpoint_12_60_prefix_4 endpoint_12_60_window_4
private theorem endpoint_12_60_window_6 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 6 2 246034279687862412 = some 246034279687862412 := by decide +kernel
private theorem endpoint_12_60_prefix_8 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 8 236196967408752645 = some 246034279687862412 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 6 2 236196967408752645 246034279687862412 246034279687862412 endpoint_12_60_prefix_6 endpoint_12_60_window_6
private theorem endpoint_12_60_window_8 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 8 2 246034279687862412 = some 246034279687862412 := by decide +kernel
private theorem endpoint_12_60_prefix_10 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 10 236196967408752645 = some 246034279687862412 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 8 2 236196967408752645 246034279687862412 246034279687862412 endpoint_12_60_prefix_8 endpoint_12_60_window_8
private theorem endpoint_12_60_window_10 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 10 1 246034279687862412 = some 246034279687862412 := by decide +kernel
private theorem endpoint_12_60_prefix_11 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 11 236196967408752645 = some 246034279687862412 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 10 1 236196967408752645 246034279687862412 246034279687862412 endpoint_12_60_prefix_10 endpoint_12_60_window_10

def endpoint_12_60 : CertifiedEndpoint :=
  ⟨⟨12, 60, 2751⟩, 246034279687862412, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_12_60_flag endpoint_12_60_sources 11 236196967408752645 246034279687862412 rfl endpoint_12_60_base endpoint_12_60_prefix_11) (by decide)⟩
private def endpoint_12_61_flag : Flag := ⟨12, 61, 2703⟩
private def endpoint_12_61_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_12_61_base : receiptBase endpoint_12_61_flag endpoint_12_61_sources = some 235520878011373772 := by decide +kernel
private theorem endpoint_12_61_window_0 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 2 235520878011373772 = some 248316492482688865 := by decide +kernel
private theorem endpoint_12_61_window_2 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 2 2 248316492482688865 = some 248316492482688865 := by decide +kernel
private theorem endpoint_12_61_prefix_4 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 4 235520878011373772 = some 248316492482688865 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 2 2 235520878011373772 248316492482688865 248316492482688865 endpoint_12_61_window_0 endpoint_12_61_window_2
private theorem endpoint_12_61_window_4 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 4 2 248316492482688865 = some 248316492482688865 := by decide +kernel
private theorem endpoint_12_61_prefix_6 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 6 235520878011373772 = some 248316492482688865 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 4 2 235520878011373772 248316492482688865 248316492482688865 endpoint_12_61_prefix_4 endpoint_12_61_window_4
private theorem endpoint_12_61_window_6 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 6 2 248316492482688865 = some 248316492482688865 := by decide +kernel
private theorem endpoint_12_61_prefix_8 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 8 235520878011373772 = some 248316492482688865 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 6 2 235520878011373772 248316492482688865 248316492482688865 endpoint_12_61_prefix_6 endpoint_12_61_window_6
private theorem endpoint_12_61_window_8 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 8 2 248316492482688865 = some 248316492482688865 := by decide +kernel
private theorem endpoint_12_61_prefix_10 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 10 235520878011373772 = some 248316492482688865 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 8 2 235520878011373772 248316492482688865 248316492482688865 endpoint_12_61_prefix_8 endpoint_12_61_window_8
private theorem endpoint_12_61_window_10 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 10 1 248316492482688865 = some 248316492482688865 := by decide +kernel
private theorem endpoint_12_61_prefix_11 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 11 235520878011373772 = some 248316492482688865 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 10 1 235520878011373772 248316492482688865 248316492482688865 endpoint_12_61_prefix_10 endpoint_12_61_window_10

def endpoint_12_61 : CertifiedEndpoint :=
  ⟨⟨12, 61, 2703⟩, 248316492482688865, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_12_61_flag endpoint_12_61_sources 11 235520878011373772 248316492482688865 rfl endpoint_12_61_base endpoint_12_61_prefix_11) (by decide)⟩
private def endpoint_12_62_flag : Flag := ⟨12, 62, 2652⟩
private def endpoint_12_62_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_12_62_base : receiptBase endpoint_12_62_flag endpoint_12_62_sources = some 235526978135760665 := by decide +kernel
private theorem endpoint_12_62_window_0 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 2 235526978135760665 = some 246419837743384716 := by decide +kernel
private theorem endpoint_12_62_window_2 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 2 2 246419837743384716 = some 246419837743384716 := by decide +kernel
private theorem endpoint_12_62_prefix_4 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 4 235526978135760665 = some 246419837743384716 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 2 2 235526978135760665 246419837743384716 246419837743384716 endpoint_12_62_window_0 endpoint_12_62_window_2
private theorem endpoint_12_62_window_4 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 4 2 246419837743384716 = some 246419837743384716 := by decide +kernel
private theorem endpoint_12_62_prefix_6 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 6 235526978135760665 = some 246419837743384716 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 4 2 235526978135760665 246419837743384716 246419837743384716 endpoint_12_62_prefix_4 endpoint_12_62_window_4
private theorem endpoint_12_62_window_6 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 6 2 246419837743384716 = some 246419837743384716 := by decide +kernel
private theorem endpoint_12_62_prefix_8 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 8 235526978135760665 = some 246419837743384716 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 6 2 235526978135760665 246419837743384716 246419837743384716 endpoint_12_62_prefix_6 endpoint_12_62_window_6
private theorem endpoint_12_62_window_8 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 8 2 246419837743384716 = some 246419837743384716 := by decide +kernel
private theorem endpoint_12_62_prefix_10 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 10 235526978135760665 = some 246419837743384716 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 8 2 235526978135760665 246419837743384716 246419837743384716 endpoint_12_62_prefix_8 endpoint_12_62_window_8
private theorem endpoint_12_62_window_10 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 10 1 246419837743384716 = some 246419837743384716 := by decide +kernel
private theorem endpoint_12_62_prefix_11 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 11 235526978135760665 = some 246419837743384716 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 10 1 235526978135760665 246419837743384716 246419837743384716 endpoint_12_62_prefix_10 endpoint_12_62_window_10

def endpoint_12_62 : CertifiedEndpoint :=
  ⟨⟨12, 62, 2652⟩, 246419837743384716, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_12_62_flag endpoint_12_62_sources 11 235526978135760665 246419837743384716 rfl endpoint_12_62_base endpoint_12_62_prefix_11) (by decide)⟩
private def endpoint_12_63_flag : Flag := ⟨12, 63, 2598⟩
private def endpoint_12_63_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_12_63_base : receiptBase endpoint_12_63_flag endpoint_12_63_sources = some 235170861703217725 := by decide +kernel
private theorem endpoint_12_63_window_0 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 2 235170861703217725 = some 245581515139692000 := by decide +kernel
private theorem endpoint_12_63_window_2 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 2 2 245581515139692000 = some 245581515139692000 := by decide +kernel
private theorem endpoint_12_63_prefix_4 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 4 235170861703217725 = some 245581515139692000 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 2 2 235170861703217725 245581515139692000 245581515139692000 endpoint_12_63_window_0 endpoint_12_63_window_2
private theorem endpoint_12_63_window_4 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 4 2 245581515139692000 = some 245581515139692000 := by decide +kernel
private theorem endpoint_12_63_prefix_6 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 6 235170861703217725 = some 245581515139692000 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 4 2 235170861703217725 245581515139692000 245581515139692000 endpoint_12_63_prefix_4 endpoint_12_63_window_4
private theorem endpoint_12_63_window_6 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 6 2 245581515139692000 = some 245581515139692000 := by decide +kernel
private theorem endpoint_12_63_prefix_8 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 8 235170861703217725 = some 245581515139692000 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 6 2 235170861703217725 245581515139692000 245581515139692000 endpoint_12_63_prefix_6 endpoint_12_63_window_6
private theorem endpoint_12_63_window_8 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 8 2 245581515139692000 = some 245581515139692000 := by decide +kernel
private theorem endpoint_12_63_prefix_10 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 10 235170861703217725 = some 245581515139692000 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 8 2 235170861703217725 245581515139692000 245581515139692000 endpoint_12_63_prefix_8 endpoint_12_63_window_8
private theorem endpoint_12_63_window_10 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 10 1 245581515139692000 = some 245581515139692000 := by decide +kernel
private theorem endpoint_12_63_prefix_11 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 11 235170861703217725 = some 245581515139692000 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 10 1 235170861703217725 245581515139692000 245581515139692000 endpoint_12_63_prefix_10 endpoint_12_63_window_10

def endpoint_12_63 : CertifiedEndpoint :=
  ⟨⟨12, 63, 2598⟩, 245581515139692000, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_12_63_flag endpoint_12_63_sources 11 235170861703217725 245581515139692000 rfl endpoint_12_63_base endpoint_12_63_prefix_11) (by decide)⟩
private def endpoint_12_64_flag : Flag := ⟨12, 64, 2543⟩
private def endpoint_12_64_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_64_base : receiptBase endpoint_12_64_flag endpoint_12_64_sources = some 234460329734286724 := by decide +kernel
private theorem endpoint_12_64_window_0 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 2 234460329734286724 = some 239890496563885460 := by decide +kernel
private theorem endpoint_12_64_window_2 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 2 2 239890496563885460 = some 239890496563885460 := by decide +kernel
private theorem endpoint_12_64_prefix_4 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 4 234460329734286724 = some 239890496563885460 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 2 2 234460329734286724 239890496563885460 239890496563885460 endpoint_12_64_window_0 endpoint_12_64_window_2
private theorem endpoint_12_64_window_4 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 4 2 239890496563885460 = some 239890496563885460 := by decide +kernel
private theorem endpoint_12_64_prefix_6 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 6 234460329734286724 = some 239890496563885460 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 4 2 234460329734286724 239890496563885460 239890496563885460 endpoint_12_64_prefix_4 endpoint_12_64_window_4
private theorem endpoint_12_64_window_6 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 6 2 239890496563885460 = some 239890496563885460 := by decide +kernel
private theorem endpoint_12_64_prefix_8 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 8 234460329734286724 = some 239890496563885460 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 6 2 234460329734286724 239890496563885460 239890496563885460 endpoint_12_64_prefix_6 endpoint_12_64_window_6
private theorem endpoint_12_64_window_8 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 8 2 239890496563885460 = some 239890496563885460 := by decide +kernel
private theorem endpoint_12_64_prefix_10 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 10 234460329734286724 = some 239890496563885460 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 8 2 234460329734286724 239890496563885460 239890496563885460 endpoint_12_64_prefix_8 endpoint_12_64_window_8
private theorem endpoint_12_64_window_10 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 10 1 239890496563885460 = some 239890496563885460 := by decide +kernel
private theorem endpoint_12_64_prefix_11 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 11 234460329734286724 = some 239890496563885460 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 10 1 234460329734286724 239890496563885460 239890496563885460 endpoint_12_64_prefix_10 endpoint_12_64_window_10

def endpoint_12_64 : CertifiedEndpoint :=
  ⟨⟨12, 64, 2543⟩, 239890496563885460, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_64_flag endpoint_12_64_sources 11 234460329734286724 239890496563885460 rfl endpoint_12_64_base endpoint_12_64_prefix_11) (by decide)⟩
private def endpoint_12_65_flag : Flag := ⟨12, 65, 2485⟩
private def endpoint_12_65_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_65_base : receiptBase endpoint_12_65_flag endpoint_12_65_sources = some 232349906083748798 := by decide +kernel
private theorem endpoint_12_65_window_0 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 2 232349906083748798 = some 241053386654554796 := by decide +kernel
private theorem endpoint_12_65_window_2 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 2 2 241053386654554796 = some 241053386654554796 := by decide +kernel
private theorem endpoint_12_65_prefix_4 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 4 232349906083748798 = some 241053386654554796 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 2 2 232349906083748798 241053386654554796 241053386654554796 endpoint_12_65_window_0 endpoint_12_65_window_2
private theorem endpoint_12_65_window_4 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 4 2 241053386654554796 = some 241053386654554796 := by decide +kernel
private theorem endpoint_12_65_prefix_6 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 6 232349906083748798 = some 241053386654554796 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 4 2 232349906083748798 241053386654554796 241053386654554796 endpoint_12_65_prefix_4 endpoint_12_65_window_4
private theorem endpoint_12_65_window_6 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 6 2 241053386654554796 = some 241053386654554796 := by decide +kernel
private theorem endpoint_12_65_prefix_8 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 8 232349906083748798 = some 241053386654554796 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 6 2 232349906083748798 241053386654554796 241053386654554796 endpoint_12_65_prefix_6 endpoint_12_65_window_6
private theorem endpoint_12_65_window_8 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 8 2 241053386654554796 = some 241053386654554796 := by decide +kernel
private theorem endpoint_12_65_prefix_10 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 10 232349906083748798 = some 241053386654554796 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 8 2 232349906083748798 241053386654554796 241053386654554796 endpoint_12_65_prefix_8 endpoint_12_65_window_8
private theorem endpoint_12_65_window_10 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 10 1 241053386654554796 = some 241053386654554796 := by decide +kernel
private theorem endpoint_12_65_prefix_11 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 11 232349906083748798 = some 241053386654554796 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 10 1 232349906083748798 241053386654554796 241053386654554796 endpoint_12_65_prefix_10 endpoint_12_65_window_10

def endpoint_12_65 : CertifiedEndpoint :=
  ⟨⟨12, 65, 2485⟩, 241053386654554796, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_65_flag endpoint_12_65_sources 11 232349906083748798 241053386654554796 rfl endpoint_12_65_base endpoint_12_65_prefix_11) (by decide)⟩
private def endpoint_12_66_flag : Flag := ⟨12, 66, 2424⟩
private def endpoint_12_66_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_66_base : receiptBase endpoint_12_66_flag endpoint_12_66_sources = some 229809962473708789 := by decide +kernel
private theorem endpoint_12_66_window_0 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 2 229809962473708789 = some 241954912711664256 := by decide +kernel
private theorem endpoint_12_66_window_2 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 2 2 241954912711664256 = some 241954912711664256 := by decide +kernel
private theorem endpoint_12_66_prefix_4 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 4 229809962473708789 = some 241954912711664256 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 2 2 229809962473708789 241954912711664256 241954912711664256 endpoint_12_66_window_0 endpoint_12_66_window_2
private theorem endpoint_12_66_window_4 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 4 2 241954912711664256 = some 241954912711664256 := by decide +kernel
private theorem endpoint_12_66_prefix_6 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 6 229809962473708789 = some 241954912711664256 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 4 2 229809962473708789 241954912711664256 241954912711664256 endpoint_12_66_prefix_4 endpoint_12_66_window_4
private theorem endpoint_12_66_window_6 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 6 2 241954912711664256 = some 241954912711664256 := by decide +kernel
private theorem endpoint_12_66_prefix_8 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 8 229809962473708789 = some 241954912711664256 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 6 2 229809962473708789 241954912711664256 241954912711664256 endpoint_12_66_prefix_6 endpoint_12_66_window_6
private theorem endpoint_12_66_window_8 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 8 2 241954912711664256 = some 241954912711664256 := by decide +kernel
private theorem endpoint_12_66_prefix_10 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 10 229809962473708789 = some 241954912711664256 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 8 2 229809962473708789 241954912711664256 241954912711664256 endpoint_12_66_prefix_8 endpoint_12_66_window_8
private theorem endpoint_12_66_window_10 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 10 1 241954912711664256 = some 241954912711664256 := by decide +kernel
private theorem endpoint_12_66_prefix_11 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 11 229809962473708789 = some 241954912711664256 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 10 1 229809962473708789 241954912711664256 241954912711664256 endpoint_12_66_prefix_10 endpoint_12_66_window_10

def endpoint_12_66 : CertifiedEndpoint :=
  ⟨⟨12, 66, 2424⟩, 241954912711664256, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_66_flag endpoint_12_66_sources 11 229809962473708789 241954912711664256 rfl endpoint_12_66_base endpoint_12_66_prefix_11) (by decide)⟩
private def endpoint_12_67_flag : Flag := ⟨12, 67, 2362⟩
private def endpoint_12_67_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_67_base : receiptBase endpoint_12_67_flag endpoint_12_67_sources = some 227018839347494696 := by decide +kernel
private theorem endpoint_12_67_window_0 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 2 227018839347494696 = some 242692890835109987 := by decide +kernel
private theorem endpoint_12_67_window_2 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 2 2 242692890835109987 = some 242692890835109987 := by decide +kernel
private theorem endpoint_12_67_prefix_4 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 4 227018839347494696 = some 242692890835109987 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 2 2 227018839347494696 242692890835109987 242692890835109987 endpoint_12_67_window_0 endpoint_12_67_window_2
private theorem endpoint_12_67_window_4 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 4 2 242692890835109987 = some 242692890835109987 := by decide +kernel
private theorem endpoint_12_67_prefix_6 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 6 227018839347494696 = some 242692890835109987 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 4 2 227018839347494696 242692890835109987 242692890835109987 endpoint_12_67_prefix_4 endpoint_12_67_window_4
private theorem endpoint_12_67_window_6 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 6 2 242692890835109987 = some 242692890835109987 := by decide +kernel
private theorem endpoint_12_67_prefix_8 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 8 227018839347494696 = some 242692890835109987 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 6 2 227018839347494696 242692890835109987 242692890835109987 endpoint_12_67_prefix_6 endpoint_12_67_window_6
private theorem endpoint_12_67_window_8 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 8 2 242692890835109987 = some 242692890835109987 := by decide +kernel
private theorem endpoint_12_67_prefix_10 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 10 227018839347494696 = some 242692890835109987 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 8 2 227018839347494696 242692890835109987 242692890835109987 endpoint_12_67_prefix_8 endpoint_12_67_window_8
private theorem endpoint_12_67_window_10 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 10 1 242692890835109987 = some 242692890835109987 := by decide +kernel
private theorem endpoint_12_67_prefix_11 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 11 227018839347494696 = some 242692890835109987 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 10 1 227018839347494696 242692890835109987 242692890835109987 endpoint_12_67_prefix_10 endpoint_12_67_window_10

def endpoint_12_67 : CertifiedEndpoint :=
  ⟨⟨12, 67, 2362⟩, 242692890835109987, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_67_flag endpoint_12_67_sources 11 227018839347494696 242692890835109987 rfl endpoint_12_67_base endpoint_12_67_prefix_11) (by decide)⟩
private def endpoint_12_68_flag : Flag := ⟨12, 68, 2296⟩
private def endpoint_12_68_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_12_68_base : receiptBase endpoint_12_68_flag endpoint_12_68_sources = some 228927145283824989 := by decide +kernel
private theorem endpoint_12_68_window_0 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 2 228927145283824989 = some 230430055067577156 := by decide +kernel
private theorem endpoint_12_68_window_2 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 2 2 230430055067577156 = some 230430055067577156 := by decide +kernel
private theorem endpoint_12_68_prefix_4 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 4 228927145283824989 = some 230430055067577156 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 2 2 228927145283824989 230430055067577156 230430055067577156 endpoint_12_68_window_0 endpoint_12_68_window_2
private theorem endpoint_12_68_window_4 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 4 2 230430055067577156 = some 230430055067577156 := by decide +kernel
private theorem endpoint_12_68_prefix_6 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 6 228927145283824989 = some 230430055067577156 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 4 2 228927145283824989 230430055067577156 230430055067577156 endpoint_12_68_prefix_4 endpoint_12_68_window_4
private theorem endpoint_12_68_window_6 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 6 2 230430055067577156 = some 230430055067577156 := by decide +kernel
private theorem endpoint_12_68_prefix_8 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 8 228927145283824989 = some 230430055067577156 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 6 2 228927145283824989 230430055067577156 230430055067577156 endpoint_12_68_prefix_6 endpoint_12_68_window_6
private theorem endpoint_12_68_window_8 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 8 2 230430055067577156 = some 230430055067577156 := by decide +kernel
private theorem endpoint_12_68_prefix_10 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 10 228927145283824989 = some 230430055067577156 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 8 2 228927145283824989 230430055067577156 230430055067577156 endpoint_12_68_prefix_8 endpoint_12_68_window_8
private theorem endpoint_12_68_window_10 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 10 1 230430055067577156 = some 230430055067577156 := by decide +kernel
private theorem endpoint_12_68_prefix_11 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 11 228927145283824989 = some 230430055067577156 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 10 1 228927145283824989 230430055067577156 230430055067577156 endpoint_12_68_prefix_10 endpoint_12_68_window_10

def endpoint_12_68 : CertifiedEndpoint :=
  ⟨⟨12, 68, 2296⟩, 230430055067577156, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_12_68_flag endpoint_12_68_sources 11 228927145283824989 230430055067577156 rfl endpoint_12_68_base endpoint_12_68_prefix_11) (by decide)⟩
private def endpoint_12_69_flag : Flag := ⟨12, 69, 2228⟩
private def endpoint_12_69_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_12_69_base : receiptBase endpoint_12_69_flag endpoint_12_69_sources = some 225192580205952818 := by decide +kernel
private theorem endpoint_12_69_window_0 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 2 225192580205952818 = some 230404926983113914 := by decide +kernel
private theorem endpoint_12_69_window_2 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 2 2 230404926983113914 = some 230404926983113914 := by decide +kernel
private theorem endpoint_12_69_prefix_4 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 4 225192580205952818 = some 230404926983113914 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 2 2 225192580205952818 230404926983113914 230404926983113914 endpoint_12_69_window_0 endpoint_12_69_window_2
private theorem endpoint_12_69_window_4 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 4 2 230404926983113914 = some 230404926983113914 := by decide +kernel
private theorem endpoint_12_69_prefix_6 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 6 225192580205952818 = some 230404926983113914 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 4 2 225192580205952818 230404926983113914 230404926983113914 endpoint_12_69_prefix_4 endpoint_12_69_window_4
private theorem endpoint_12_69_window_6 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 6 2 230404926983113914 = some 230404926983113914 := by decide +kernel
private theorem endpoint_12_69_prefix_8 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 8 225192580205952818 = some 230404926983113914 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 6 2 225192580205952818 230404926983113914 230404926983113914 endpoint_12_69_prefix_6 endpoint_12_69_window_6
private theorem endpoint_12_69_window_8 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 8 2 230404926983113914 = some 230404926983113914 := by decide +kernel
private theorem endpoint_12_69_prefix_10 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 10 225192580205952818 = some 230404926983113914 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 8 2 225192580205952818 230404926983113914 230404926983113914 endpoint_12_69_prefix_8 endpoint_12_69_window_8
private theorem endpoint_12_69_window_10 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 10 1 230404926983113914 = some 230404926983113914 := by decide +kernel
private theorem endpoint_12_69_prefix_11 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 11 225192580205952818 = some 230404926983113914 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 10 1 225192580205952818 230404926983113914 230404926983113914 endpoint_12_69_prefix_10 endpoint_12_69_window_10

def endpoint_12_69 : CertifiedEndpoint :=
  ⟨⟨12, 69, 2228⟩, 230404926983113914, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_12_69_flag endpoint_12_69_sources 11 225192580205952818 230404926983113914 rfl endpoint_12_69_base endpoint_12_69_prefix_11) (by decide)⟩
private def endpoint_12_70_flag : Flag := ⟨12, 70, 2158⟩
private def endpoint_12_70_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_12_70_base : receiptBase endpoint_12_70_flag endpoint_12_70_sources = some 221083778218313848 := by decide +kernel
private theorem endpoint_12_70_window_0 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 2 221083778218313848 = some 230145665664360874 := by decide +kernel
private theorem endpoint_12_70_window_2 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 2 2 230145665664360874 = some 230145665664360874 := by decide +kernel
private theorem endpoint_12_70_prefix_4 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 4 221083778218313848 = some 230145665664360874 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 2 2 221083778218313848 230145665664360874 230145665664360874 endpoint_12_70_window_0 endpoint_12_70_window_2
private theorem endpoint_12_70_window_4 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 4 2 230145665664360874 = some 230145665664360874 := by decide +kernel
private theorem endpoint_12_70_prefix_6 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 6 221083778218313848 = some 230145665664360874 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 4 2 221083778218313848 230145665664360874 230145665664360874 endpoint_12_70_prefix_4 endpoint_12_70_window_4
private theorem endpoint_12_70_window_6 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 6 2 230145665664360874 = some 230145665664360874 := by decide +kernel
private theorem endpoint_12_70_prefix_8 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 8 221083778218313848 = some 230145665664360874 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 6 2 221083778218313848 230145665664360874 230145665664360874 endpoint_12_70_prefix_6 endpoint_12_70_window_6
private theorem endpoint_12_70_window_8 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 8 2 230145665664360874 = some 230145665664360874 := by decide +kernel
private theorem endpoint_12_70_prefix_10 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 10 221083778218313848 = some 230145665664360874 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 8 2 221083778218313848 230145665664360874 230145665664360874 endpoint_12_70_prefix_8 endpoint_12_70_window_8
private theorem endpoint_12_70_window_10 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 10 1 230145665664360874 = some 230145665664360874 := by decide +kernel
private theorem endpoint_12_70_prefix_11 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 11 221083778218313848 = some 230145665664360874 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 10 1 221083778218313848 230145665664360874 230145665664360874 endpoint_12_70_prefix_10 endpoint_12_70_window_10

def endpoint_12_70 : CertifiedEndpoint :=
  ⟨⟨12, 70, 2158⟩, 230145665664360874, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_12_70_flag endpoint_12_70_sources 11 221083778218313848 230145665664360874 rfl endpoint_12_70_base endpoint_12_70_prefix_11) (by decide)⟩
private def endpoint_12_71_flag : Flag := ⟨12, 71, 2085⟩
private def endpoint_12_71_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_12_71_base : receiptBase endpoint_12_71_flag endpoint_12_71_sources = some 217822719084812301 := by decide +kernel
private theorem endpoint_12_71_window_0 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 2 217822719084812301 = some 217822719084812301 := by decide +kernel
private theorem endpoint_12_71_window_2 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 2 2 217822719084812301 = some 217822719084812301 := by decide +kernel
private theorem endpoint_12_71_prefix_4 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 4 217822719084812301 = some 217822719084812301 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 2 2 217822719084812301 217822719084812301 217822719084812301 endpoint_12_71_window_0 endpoint_12_71_window_2
private theorem endpoint_12_71_window_4 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 4 2 217822719084812301 = some 217822719084812301 := by decide +kernel
private theorem endpoint_12_71_prefix_6 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 6 217822719084812301 = some 217822719084812301 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 4 2 217822719084812301 217822719084812301 217822719084812301 endpoint_12_71_prefix_4 endpoint_12_71_window_4
private theorem endpoint_12_71_window_6 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 6 2 217822719084812301 = some 217822719084812301 := by decide +kernel
private theorem endpoint_12_71_prefix_8 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 8 217822719084812301 = some 217822719084812301 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 6 2 217822719084812301 217822719084812301 217822719084812301 endpoint_12_71_prefix_6 endpoint_12_71_window_6
private theorem endpoint_12_71_window_8 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 8 2 217822719084812301 = some 217822719084812301 := by decide +kernel
private theorem endpoint_12_71_prefix_10 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 10 217822719084812301 = some 217822719084812301 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 8 2 217822719084812301 217822719084812301 217822719084812301 endpoint_12_71_prefix_8 endpoint_12_71_window_8
private theorem endpoint_12_71_window_10 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 10 1 217822719084812301 = some 217822719084812301 := by decide +kernel
private theorem endpoint_12_71_prefix_11 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 11 217822719084812301 = some 217822719084812301 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 10 1 217822719084812301 217822719084812301 217822719084812301 endpoint_12_71_prefix_10 endpoint_12_71_window_10

def endpoint_12_71 : CertifiedEndpoint :=
  ⟨⟨12, 71, 2085⟩, 217822719084812301, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_12_71_flag endpoint_12_71_sources 11 217822719084812301 217822719084812301 rfl endpoint_12_71_base endpoint_12_71_prefix_11) (by decide)⟩
private def endpoint_12_72_flag : Flag := ⟨12, 72, 2010⟩
private def endpoint_12_72_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_12_72_base : receiptBase endpoint_12_72_flag endpoint_12_72_sources = some 212727953104407416 := by decide +kernel
private theorem endpoint_12_72_window_0 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 2 212727953104407416 = some 216722229444228960 := by decide +kernel
private theorem endpoint_12_72_window_2 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 2 2 216722229444228960 = some 216722229444228960 := by decide +kernel
private theorem endpoint_12_72_prefix_4 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 4 212727953104407416 = some 216722229444228960 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 2 2 212727953104407416 216722229444228960 216722229444228960 endpoint_12_72_window_0 endpoint_12_72_window_2
private theorem endpoint_12_72_window_4 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 4 2 216722229444228960 = some 216722229444228960 := by decide +kernel
private theorem endpoint_12_72_prefix_6 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 6 212727953104407416 = some 216722229444228960 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 4 2 212727953104407416 216722229444228960 216722229444228960 endpoint_12_72_prefix_4 endpoint_12_72_window_4
private theorem endpoint_12_72_window_6 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 6 2 216722229444228960 = some 216722229444228960 := by decide +kernel
private theorem endpoint_12_72_prefix_8 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 8 212727953104407416 = some 216722229444228960 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 6 2 212727953104407416 216722229444228960 216722229444228960 endpoint_12_72_prefix_6 endpoint_12_72_window_6
private theorem endpoint_12_72_window_8 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 8 2 216722229444228960 = some 216722229444228960 := by decide +kernel
private theorem endpoint_12_72_prefix_10 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 10 212727953104407416 = some 216722229444228960 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 8 2 212727953104407416 216722229444228960 216722229444228960 endpoint_12_72_prefix_8 endpoint_12_72_window_8
private theorem endpoint_12_72_window_10 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 10 1 216722229444228960 = some 216722229444228960 := by decide +kernel
private theorem endpoint_12_72_prefix_11 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 11 212727953104407416 = some 216722229444228960 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 10 1 212727953104407416 216722229444228960 216722229444228960 endpoint_12_72_prefix_10 endpoint_12_72_window_10

def endpoint_12_72 : CertifiedEndpoint :=
  ⟨⟨12, 72, 2010⟩, 216722229444228960, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_12_72_flag endpoint_12_72_sources 11 212727953104407416 216722229444228960 rfl endpoint_12_72_base endpoint_12_72_prefix_11) (by decide)⟩
private def endpoint_12_73_flag : Flag := ⟨12, 73, 1932⟩
private def endpoint_12_73_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_12_73_base : receiptBase endpoint_12_73_flag endpoint_12_73_sources = some 208628544174688357 := by decide +kernel
private theorem endpoint_12_73_window_0 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 2 208628544174688357 = some 209360674924413665 := by decide +kernel
private theorem endpoint_12_73_window_2 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 2 2 209360674924413665 = some 209360674924413665 := by decide +kernel
private theorem endpoint_12_73_prefix_4 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 4 208628544174688357 = some 209360674924413665 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 2 2 208628544174688357 209360674924413665 209360674924413665 endpoint_12_73_window_0 endpoint_12_73_window_2
private theorem endpoint_12_73_window_4 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 4 2 209360674924413665 = some 209360674924413665 := by decide +kernel
private theorem endpoint_12_73_prefix_6 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 6 208628544174688357 = some 209360674924413665 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 4 2 208628544174688357 209360674924413665 209360674924413665 endpoint_12_73_prefix_4 endpoint_12_73_window_4
private theorem endpoint_12_73_window_6 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 6 2 209360674924413665 = some 209360674924413665 := by decide +kernel
private theorem endpoint_12_73_prefix_8 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 8 208628544174688357 = some 209360674924413665 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 6 2 208628544174688357 209360674924413665 209360674924413665 endpoint_12_73_prefix_6 endpoint_12_73_window_6
private theorem endpoint_12_73_window_8 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 8 2 209360674924413665 = some 209360674924413665 := by decide +kernel
private theorem endpoint_12_73_prefix_10 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 10 208628544174688357 = some 209360674924413665 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 8 2 208628544174688357 209360674924413665 209360674924413665 endpoint_12_73_prefix_8 endpoint_12_73_window_8
private theorem endpoint_12_73_window_10 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 10 1 209360674924413665 = some 209360674924413665 := by decide +kernel
private theorem endpoint_12_73_prefix_11 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 11 208628544174688357 = some 209360674924413665 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 10 1 208628544174688357 209360674924413665 209360674924413665 endpoint_12_73_prefix_10 endpoint_12_73_window_10

def endpoint_12_73 : CertifiedEndpoint :=
  ⟨⟨12, 73, 1932⟩, 209360674924413665, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_12_73_flag endpoint_12_73_sources 11 208628544174688357 209360674924413665 rfl endpoint_12_73_base endpoint_12_73_prefix_11) (by decide)⟩
private def endpoint_12_74_flag : Flag := ⟨12, 74, 1852⟩
private def endpoint_12_74_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_12_74_base : receiptBase endpoint_12_74_flag endpoint_12_74_sources = some 202540732630768794 := by decide +kernel
private theorem endpoint_12_74_window_0 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 2 202540732630768794 = some 207713803265056520 := by decide +kernel
private theorem endpoint_12_74_window_2 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 2 2 207713803265056520 = some 207713803265056520 := by decide +kernel
private theorem endpoint_12_74_prefix_4 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 4 202540732630768794 = some 207713803265056520 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 2 2 202540732630768794 207713803265056520 207713803265056520 endpoint_12_74_window_0 endpoint_12_74_window_2
private theorem endpoint_12_74_window_4 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 4 2 207713803265056520 = some 207713803265056520 := by decide +kernel
private theorem endpoint_12_74_prefix_6 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 6 202540732630768794 = some 207713803265056520 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 4 2 202540732630768794 207713803265056520 207713803265056520 endpoint_12_74_prefix_4 endpoint_12_74_window_4
private theorem endpoint_12_74_window_6 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 6 2 207713803265056520 = some 207713803265056520 := by decide +kernel
private theorem endpoint_12_74_prefix_8 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 8 202540732630768794 = some 207713803265056520 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 6 2 202540732630768794 207713803265056520 207713803265056520 endpoint_12_74_prefix_6 endpoint_12_74_window_6
private theorem endpoint_12_74_window_8 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 8 2 207713803265056520 = some 207713803265056520 := by decide +kernel
private theorem endpoint_12_74_prefix_10 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 10 202540732630768794 = some 207713803265056520 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 8 2 202540732630768794 207713803265056520 207713803265056520 endpoint_12_74_prefix_8 endpoint_12_74_window_8
private theorem endpoint_12_74_window_10 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 10 1 207713803265056520 = some 207713803265056520 := by decide +kernel
private theorem endpoint_12_74_prefix_11 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 11 202540732630768794 = some 207713803265056520 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 10 1 202540732630768794 207713803265056520 207713803265056520 endpoint_12_74_prefix_10 endpoint_12_74_window_10

def endpoint_12_74 : CertifiedEndpoint :=
  ⟨⟨12, 74, 1852⟩, 207713803265056520, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_12_74_flag endpoint_12_74_sources 11 202540732630768794 207713803265056520 rfl endpoint_12_74_base endpoint_12_74_prefix_11) (by decide)⟩
private def endpoint_12_75_flag : Flag := ⟨12, 75, 1768⟩
private def endpoint_12_75_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_12_75_base : receiptBase endpoint_12_75_flag endpoint_12_75_sources = some 197328875960640278 := by decide +kernel
private theorem endpoint_12_75_window_0 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 2 197328875960640278 = some 197328875960640278 := by decide +kernel
private theorem endpoint_12_75_window_2 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 2 2 197328875960640278 = some 197328875960640278 := by decide +kernel
private theorem endpoint_12_75_prefix_4 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 4 197328875960640278 = some 197328875960640278 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 2 2 197328875960640278 197328875960640278 197328875960640278 endpoint_12_75_window_0 endpoint_12_75_window_2
private theorem endpoint_12_75_window_4 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 4 2 197328875960640278 = some 197328875960640278 := by decide +kernel
private theorem endpoint_12_75_prefix_6 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 6 197328875960640278 = some 197328875960640278 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 4 2 197328875960640278 197328875960640278 197328875960640278 endpoint_12_75_prefix_4 endpoint_12_75_window_4
private theorem endpoint_12_75_window_6 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 6 2 197328875960640278 = some 197328875960640278 := by decide +kernel
private theorem endpoint_12_75_prefix_8 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 8 197328875960640278 = some 197328875960640278 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 6 2 197328875960640278 197328875960640278 197328875960640278 endpoint_12_75_prefix_6 endpoint_12_75_window_6
private theorem endpoint_12_75_window_8 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 8 2 197328875960640278 = some 197328875960640278 := by decide +kernel
private theorem endpoint_12_75_prefix_10 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 10 197328875960640278 = some 197328875960640278 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 8 2 197328875960640278 197328875960640278 197328875960640278 endpoint_12_75_prefix_8 endpoint_12_75_window_8
private theorem endpoint_12_75_window_10 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 10 1 197328875960640278 = some 197328875960640278 := by decide +kernel
private theorem endpoint_12_75_prefix_11 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 11 197328875960640278 = some 197328875960640278 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 10 1 197328875960640278 197328875960640278 197328875960640278 endpoint_12_75_prefix_10 endpoint_12_75_window_10

def endpoint_12_75 : CertifiedEndpoint :=
  ⟨⟨12, 75, 1768⟩, 197328875960640278, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_12_75_flag endpoint_12_75_sources 11 197328875960640278 197328875960640278 rfl endpoint_12_75_base endpoint_12_75_prefix_11) (by decide)⟩

def endpointBlock07 : List CertifiedEndpoint := [
  endpoint_11_74, endpoint_11_75, endpoint_11_76, endpoint_11_77, endpoint_11_78, endpoint_11_79,
  endpoint_11_80, endpoint_11_81, endpoint_11_82, endpoint_11_83, endpoint_11_84, endpoint_11_85,
  endpoint_11_86, endpoint_11_87, endpoint_11_88, endpoint_11_89, endpoint_11_90, endpoint_11_91,
  endpoint_11_92, endpoint_12_12, endpoint_12_13, endpoint_12_14, endpoint_12_15, endpoint_12_16,
  endpoint_12_17, endpoint_12_18, endpoint_12_19, endpoint_12_20, endpoint_12_21, endpoint_12_22,
  endpoint_12_23, endpoint_12_24, endpoint_12_25, endpoint_12_26, endpoint_12_27, endpoint_12_28,
  endpoint_12_29, endpoint_12_30, endpoint_12_31, endpoint_12_32, endpoint_12_33, endpoint_12_34,
  endpoint_12_35, endpoint_12_36, endpoint_12_37, endpoint_12_38, endpoint_12_39, endpoint_12_40,
  endpoint_12_41, endpoint_12_42, endpoint_12_43, endpoint_12_44, endpoint_12_45, endpoint_12_46,
  endpoint_12_47, endpoint_12_48, endpoint_12_49, endpoint_12_50, endpoint_12_51, endpoint_12_52,
  endpoint_12_53, endpoint_12_54, endpoint_12_55, endpoint_12_56, endpoint_12_57, endpoint_12_58,
  endpoint_12_59, endpoint_12_60, endpoint_12_61, endpoint_12_62, endpoint_12_63, endpoint_12_64,
  endpoint_12_65, endpoint_12_66, endpoint_12_67, endpoint_12_68, endpoint_12_69, endpoint_12_70,
  endpoint_12_71, endpoint_12_72, endpoint_12_73, endpoint_12_74, endpoint_12_75
]

end ProximityPrize.SubmissionLower.Koala6844Receipts
