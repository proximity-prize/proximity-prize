import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def endpoint_7_34 : CertifiedEndpoint :=
  ⟨⟨7, 34, 4669⟩, 234915114337075369, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_35 : CertifiedEndpoint :=
  ⟨⟨7, 35, 4643⟩, 241360821244035456, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_36 : CertifiedEndpoint :=
  ⟨⟨7, 36, 4616⟩, 247663407588125696, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_37 : CertifiedEndpoint :=
  ⟨⟨7, 37, 4589⟩, 253873392079970066, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_38 : CertifiedEndpoint :=
  ⟨⟨7, 38, 4562⟩, 259990774719568566, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_7_39_flag : Flag := ⟨7, 39, 4534⟩
private def endpoint_7_39_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_39_base : receiptBase endpoint_7_39_flag endpoint_7_39_sources = some 184225705252175470 := by decide +kernel
private theorem endpoint_7_39_w0 : receiptWindow endpoint_7_39_flag endpoint_7_39_sources 0 2 184225705252175470 = some 184225705252175470 := by decide +kernel
private theorem endpoint_7_39_w2 : receiptWindow endpoint_7_39_flag endpoint_7_39_sources 2 2 184225705252175470 = some 184225705252175470 := by decide +kernel
private theorem endpoint_7_39_p4 : receiptWindow endpoint_7_39_flag endpoint_7_39_sources 0 4 184225705252175470 = some 184225705252175470 :=
  join_receipt_window endpoint_7_39_flag endpoint_7_39_sources 0 2 2 184225705252175470 184225705252175470 184225705252175470 endpoint_7_39_w0 endpoint_7_39_w2
private theorem endpoint_7_39_w4 : receiptWindow endpoint_7_39_flag endpoint_7_39_sources 4 2 184225705252175470 = some 184225705252175470 := by decide +kernel
private theorem endpoint_7_39_p6 : receiptWindow endpoint_7_39_flag endpoint_7_39_sources 0 6 184225705252175470 = some 184225705252175470 :=
  join_receipt_window endpoint_7_39_flag endpoint_7_39_sources 0 4 2 184225705252175470 184225705252175470 184225705252175470 endpoint_7_39_p4 endpoint_7_39_w4
def endpoint_7_39 : CertifiedEndpoint :=
  ⟨⟨7, 39, 4534⟩, 184225705252175470, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_39_flag endpoint_7_39_sources 6 184225705252175470 184225705252175470 rfl endpoint_7_39_base endpoint_7_39_p6) (by decide)⟩
private def endpoint_7_40_flag : Flag := ⟨7, 40, 4506⟩
private def endpoint_7_40_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_40_base : receiptBase endpoint_7_40_flag endpoint_7_40_sources = some 187049794161511716 := by decide +kernel
private theorem endpoint_7_40_w0 : receiptWindow endpoint_7_40_flag endpoint_7_40_sources 0 2 187049794161511716 = some 187049794161511716 := by decide +kernel
private theorem endpoint_7_40_w2 : receiptWindow endpoint_7_40_flag endpoint_7_40_sources 2 2 187049794161511716 = some 187049794161511716 := by decide +kernel
private theorem endpoint_7_40_p4 : receiptWindow endpoint_7_40_flag endpoint_7_40_sources 0 4 187049794161511716 = some 187049794161511716 :=
  join_receipt_window endpoint_7_40_flag endpoint_7_40_sources 0 2 2 187049794161511716 187049794161511716 187049794161511716 endpoint_7_40_w0 endpoint_7_40_w2
private theorem endpoint_7_40_w4 : receiptWindow endpoint_7_40_flag endpoint_7_40_sources 4 2 187049794161511716 = some 187049794161511716 := by decide +kernel
private theorem endpoint_7_40_p6 : receiptWindow endpoint_7_40_flag endpoint_7_40_sources 0 6 187049794161511716 = some 187049794161511716 :=
  join_receipt_window endpoint_7_40_flag endpoint_7_40_sources 0 4 2 187049794161511716 187049794161511716 187049794161511716 endpoint_7_40_p4 endpoint_7_40_w4
def endpoint_7_40 : CertifiedEndpoint :=
  ⟨⟨7, 40, 4506⟩, 187049794161511716, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_40_flag endpoint_7_40_sources 6 187049794161511716 187049794161511716 rfl endpoint_7_40_base endpoint_7_40_p6) (by decide)⟩
private def endpoint_7_41_flag : Flag := ⟨7, 41, 4478⟩
private def endpoint_7_41_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_41_base : receiptBase endpoint_7_41_flag endpoint_7_41_sources = some 189824631637039102 := by decide +kernel
private theorem endpoint_7_41_w0 : receiptWindow endpoint_7_41_flag endpoint_7_41_sources 0 2 189824631637039102 = some 189824631637039102 := by decide +kernel
private theorem endpoint_7_41_w2 : receiptWindow endpoint_7_41_flag endpoint_7_41_sources 2 2 189824631637039102 = some 189824631637039102 := by decide +kernel
private theorem endpoint_7_41_p4 : receiptWindow endpoint_7_41_flag endpoint_7_41_sources 0 4 189824631637039102 = some 189824631637039102 :=
  join_receipt_window endpoint_7_41_flag endpoint_7_41_sources 0 2 2 189824631637039102 189824631637039102 189824631637039102 endpoint_7_41_w0 endpoint_7_41_w2
private theorem endpoint_7_41_w4 : receiptWindow endpoint_7_41_flag endpoint_7_41_sources 4 2 189824631637039102 = some 189824631637039102 := by decide +kernel
private theorem endpoint_7_41_p6 : receiptWindow endpoint_7_41_flag endpoint_7_41_sources 0 6 189824631637039102 = some 189824631637039102 :=
  join_receipt_window endpoint_7_41_flag endpoint_7_41_sources 0 4 2 189824631637039102 189824631637039102 189824631637039102 endpoint_7_41_p4 endpoint_7_41_w4
def endpoint_7_41 : CertifiedEndpoint :=
  ⟨⟨7, 41, 4478⟩, 189824631637039102, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_41_flag endpoint_7_41_sources 6 189824631637039102 189824631637039102 rfl endpoint_7_41_base endpoint_7_41_p6) (by decide)⟩
private def endpoint_7_42_flag : Flag := ⟨7, 42, 4449⟩
private def endpoint_7_42_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_42_base : receiptBase endpoint_7_42_flag endpoint_7_42_sources = some 192507511000193690 := by decide +kernel
private theorem endpoint_7_42_w0 : receiptWindow endpoint_7_42_flag endpoint_7_42_sources 0 2 192507511000193690 = some 192507511000193690 := by decide +kernel
private theorem endpoint_7_42_w2 : receiptWindow endpoint_7_42_flag endpoint_7_42_sources 2 2 192507511000193690 = some 192507511000193690 := by decide +kernel
private theorem endpoint_7_42_p4 : receiptWindow endpoint_7_42_flag endpoint_7_42_sources 0 4 192507511000193690 = some 192507511000193690 :=
  join_receipt_window endpoint_7_42_flag endpoint_7_42_sources 0 2 2 192507511000193690 192507511000193690 192507511000193690 endpoint_7_42_w0 endpoint_7_42_w2
private theorem endpoint_7_42_w4 : receiptWindow endpoint_7_42_flag endpoint_7_42_sources 4 2 192507511000193690 = some 192507511000193690 := by decide +kernel
private theorem endpoint_7_42_p6 : receiptWindow endpoint_7_42_flag endpoint_7_42_sources 0 6 192507511000193690 = some 192507511000193690 :=
  join_receipt_window endpoint_7_42_flag endpoint_7_42_sources 0 4 2 192507511000193690 192507511000193690 192507511000193690 endpoint_7_42_p4 endpoint_7_42_w4
def endpoint_7_42 : CertifiedEndpoint :=
  ⟨⟨7, 42, 4449⟩, 192507511000193690, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_42_flag endpoint_7_42_sources 6 192507511000193690 192507511000193690 rfl endpoint_7_42_base endpoint_7_42_p6) (by decide)⟩
private def endpoint_7_43_flag : Flag := ⟨7, 43, 4419⟩
private def endpoint_7_43_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_43_base : receiptBase endpoint_7_43_flag endpoint_7_43_sources = some 195095840070248696 := by decide +kernel
private theorem endpoint_7_43_w0 : receiptWindow endpoint_7_43_flag endpoint_7_43_sources 0 2 195095840070248696 = some 195095840070248696 := by decide +kernel
private theorem endpoint_7_43_w2 : receiptWindow endpoint_7_43_flag endpoint_7_43_sources 2 2 195095840070248696 = some 195095840070248696 := by decide +kernel
private theorem endpoint_7_43_p4 : receiptWindow endpoint_7_43_flag endpoint_7_43_sources 0 4 195095840070248696 = some 195095840070248696 :=
  join_receipt_window endpoint_7_43_flag endpoint_7_43_sources 0 2 2 195095840070248696 195095840070248696 195095840070248696 endpoint_7_43_w0 endpoint_7_43_w2
private theorem endpoint_7_43_w4 : receiptWindow endpoint_7_43_flag endpoint_7_43_sources 4 2 195095840070248696 = some 195095840070248696 := by decide +kernel
private theorem endpoint_7_43_p6 : receiptWindow endpoint_7_43_flag endpoint_7_43_sources 0 6 195095840070248696 = some 195095840070248696 :=
  join_receipt_window endpoint_7_43_flag endpoint_7_43_sources 0 4 2 195095840070248696 195095840070248696 195095840070248696 endpoint_7_43_p4 endpoint_7_43_w4
def endpoint_7_43 : CertifiedEndpoint :=
  ⟨⟨7, 43, 4419⟩, 195095840070248696, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_43_flag endpoint_7_43_sources 6 195095840070248696 195095840070248696 rfl endpoint_7_43_base endpoint_7_43_p6) (by decide)⟩
private def endpoint_7_44_flag : Flag := ⟨7, 44, 4389⟩
private def endpoint_7_44_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_44_base : receiptBase endpoint_7_44_flag endpoint_7_44_sources = some 197631461465525800 := by decide +kernel
private theorem endpoint_7_44_w0 : receiptWindow endpoint_7_44_flag endpoint_7_44_sources 0 2 197631461465525800 = some 197631461465525800 := by decide +kernel
private theorem endpoint_7_44_w2 : receiptWindow endpoint_7_44_flag endpoint_7_44_sources 2 2 197631461465525800 = some 197631461465525800 := by decide +kernel
private theorem endpoint_7_44_p4 : receiptWindow endpoint_7_44_flag endpoint_7_44_sources 0 4 197631461465525800 = some 197631461465525800 :=
  join_receipt_window endpoint_7_44_flag endpoint_7_44_sources 0 2 2 197631461465525800 197631461465525800 197631461465525800 endpoint_7_44_w0 endpoint_7_44_w2
private theorem endpoint_7_44_w4 : receiptWindow endpoint_7_44_flag endpoint_7_44_sources 4 2 197631461465525800 = some 197631461465525800 := by decide +kernel
private theorem endpoint_7_44_p6 : receiptWindow endpoint_7_44_flag endpoint_7_44_sources 0 6 197631461465525800 = some 197631461465525800 :=
  join_receipt_window endpoint_7_44_flag endpoint_7_44_sources 0 4 2 197631461465525800 197631461465525800 197631461465525800 endpoint_7_44_p4 endpoint_7_44_w4
def endpoint_7_44 : CertifiedEndpoint :=
  ⟨⟨7, 44, 4389⟩, 197631461465525800, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_44_flag endpoint_7_44_sources 6 197631461465525800 197631461465525800 rfl endpoint_7_44_base endpoint_7_44_p6) (by decide)⟩
private def endpoint_7_45_flag : Flag := ⟨7, 45, 4359⟩
private def endpoint_7_45_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_45_base : receiptBase endpoint_7_45_flag endpoint_7_45_sources = some 200114375186025000 := by decide +kernel
private theorem endpoint_7_45_w0 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 0 2 200114375186025000 = some 200114375186025000 := by decide +kernel
private theorem endpoint_7_45_w2 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 2 2 200114375186025000 = some 200114375186025000 := by decide +kernel
private theorem endpoint_7_45_p4 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 0 4 200114375186025000 = some 200114375186025000 :=
  join_receipt_window endpoint_7_45_flag endpoint_7_45_sources 0 2 2 200114375186025000 200114375186025000 200114375186025000 endpoint_7_45_w0 endpoint_7_45_w2
private theorem endpoint_7_45_w4 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 4 2 200114375186025000 = some 200114375186025000 := by decide +kernel
private theorem endpoint_7_45_p6 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 0 6 200114375186025000 = some 200114375186025000 :=
  join_receipt_window endpoint_7_45_flag endpoint_7_45_sources 0 4 2 200114375186025000 200114375186025000 200114375186025000 endpoint_7_45_p4 endpoint_7_45_w4
def endpoint_7_45 : CertifiedEndpoint :=
  ⟨⟨7, 45, 4359⟩, 200114375186025000, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_45_flag endpoint_7_45_sources 6 200114375186025000 200114375186025000 rfl endpoint_7_45_base endpoint_7_45_p6) (by decide)⟩
private def endpoint_7_46_flag : Flag := ⟨7, 46, 4328⟩
private def endpoint_7_46_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_46_base : receiptBase endpoint_7_46_flag endpoint_7_46_sources = some 202498418312213316 := by decide +kernel
private theorem endpoint_7_46_w0 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 0 2 202498418312213316 = some 202498418312213316 := by decide +kernel
private theorem endpoint_7_46_w2 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 2 2 202498418312213316 = some 202498418312213316 := by decide +kernel
private theorem endpoint_7_46_p4 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 0 4 202498418312213316 = some 202498418312213316 :=
  join_receipt_window endpoint_7_46_flag endpoint_7_46_sources 0 2 2 202498418312213316 202498418312213316 202498418312213316 endpoint_7_46_w0 endpoint_7_46_w2
private theorem endpoint_7_46_w4 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 4 2 202498418312213316 = some 202498418312213316 := by decide +kernel
private theorem endpoint_7_46_p6 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 0 6 202498418312213316 = some 202498418312213316 :=
  join_receipt_window endpoint_7_46_flag endpoint_7_46_sources 0 4 2 202498418312213316 202498418312213316 202498418312213316 endpoint_7_46_p4 endpoint_7_46_w4
def endpoint_7_46 : CertifiedEndpoint :=
  ⟨⟨7, 46, 4328⟩, 202498418312213316, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_46_flag endpoint_7_46_sources 6 202498418312213316 202498418312213316 rfl endpoint_7_46_base endpoint_7_46_p6) (by decide)⟩
private def endpoint_7_47_flag : Flag := ⟨7, 47, 4296⟩
private def endpoint_7_47_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_47_base : receiptBase endpoint_7_47_flag endpoint_7_47_sources = some 204780998663363965 := by decide +kernel
private theorem endpoint_7_47_w0 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 0 2 204780998663363965 = some 204780998663363965 := by decide +kernel
private theorem endpoint_7_47_w2 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 2 2 204780998663363965 = some 204780998663363965 := by decide +kernel
private theorem endpoint_7_47_p4 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 0 4 204780998663363965 = some 204780998663363965 :=
  join_receipt_window endpoint_7_47_flag endpoint_7_47_sources 0 2 2 204780998663363965 204780998663363965 204780998663363965 endpoint_7_47_w0 endpoint_7_47_w2
private theorem endpoint_7_47_w4 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 4 2 204780998663363965 = some 204780998663363965 := by decide +kernel
private theorem endpoint_7_47_p6 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 0 6 204780998663363965 = some 204780998663363965 :=
  join_receipt_window endpoint_7_47_flag endpoint_7_47_sources 0 4 2 204780998663363965 204780998663363965 204780998663363965 endpoint_7_47_p4 endpoint_7_47_w4
def endpoint_7_47 : CertifiedEndpoint :=
  ⟨⟨7, 47, 4296⟩, 204780998663363965, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_47_flag endpoint_7_47_sources 6 204780998663363965 204780998663363965 rfl endpoint_7_47_base endpoint_7_47_p6) (by decide)⟩
private def endpoint_7_48_flag : Flag := ⟨7, 48, 4264⟩
private def endpoint_7_48_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_48_base : receiptBase endpoint_7_48_flag endpoint_7_48_sources = some 207007415098767669 := by decide +kernel
private theorem endpoint_7_48_w0 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 0 2 207007415098767669 = some 207007415098767669 := by decide +kernel
private theorem endpoint_7_48_w2 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 2 2 207007415098767669 = some 207007415098767669 := by decide +kernel
private theorem endpoint_7_48_p4 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 0 4 207007415098767669 = some 207007415098767669 :=
  join_receipt_window endpoint_7_48_flag endpoint_7_48_sources 0 2 2 207007415098767669 207007415098767669 207007415098767669 endpoint_7_48_w0 endpoint_7_48_w2
private theorem endpoint_7_48_w4 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 4 2 207007415098767669 = some 207007415098767669 := by decide +kernel
private theorem endpoint_7_48_p6 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 0 6 207007415098767669 = some 207007415098767669 :=
  join_receipt_window endpoint_7_48_flag endpoint_7_48_sources 0 4 2 207007415098767669 207007415098767669 207007415098767669 endpoint_7_48_p4 endpoint_7_48_w4
def endpoint_7_48 : CertifiedEndpoint :=
  ⟨⟨7, 48, 4264⟩, 207007415098767669, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_48_flag endpoint_7_48_sources 6 207007415098767669 207007415098767669 rfl endpoint_7_48_base endpoint_7_48_p6) (by decide)⟩
private def endpoint_7_49_flag : Flag := ⟨7, 49, 4231⟩
private def endpoint_7_49_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_49_base : receiptBase endpoint_7_49_flag endpoint_7_49_sources = some 209128912518164663 := by decide +kernel
private theorem endpoint_7_49_w0 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 0 2 209128912518164663 = some 209128912518164663 := by decide +kernel
private theorem endpoint_7_49_w2 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 2 2 209128912518164663 = some 209128912518164663 := by decide +kernel
private theorem endpoint_7_49_p4 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 0 4 209128912518164663 = some 209128912518164663 :=
  join_receipt_window endpoint_7_49_flag endpoint_7_49_sources 0 2 2 209128912518164663 209128912518164663 209128912518164663 endpoint_7_49_w0 endpoint_7_49_w2
private theorem endpoint_7_49_w4 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 4 2 209128912518164663 = some 209128912518164663 := by decide +kernel
private theorem endpoint_7_49_p6 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 0 6 209128912518164663 = some 209128912518164663 :=
  join_receipt_window endpoint_7_49_flag endpoint_7_49_sources 0 4 2 209128912518164663 209128912518164663 209128912518164663 endpoint_7_49_p4 endpoint_7_49_w4
def endpoint_7_49 : CertifiedEndpoint :=
  ⟨⟨7, 49, 4231⟩, 209128912518164663, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_49_flag endpoint_7_49_sources 6 209128912518164663 209128912518164663 rfl endpoint_7_49_base endpoint_7_49_p6) (by decide)⟩
private def endpoint_7_50_flag : Flag := ⟨7, 50, 4198⟩
private def endpoint_7_50_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_50_base : receiptBase endpoint_7_50_flag endpoint_7_50_sources = some 211192517901330189 := by decide +kernel
private theorem endpoint_7_50_w0 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 0 2 211192517901330189 = some 211192517901330189 := by decide +kernel
private theorem endpoint_7_50_w2 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 2 2 211192517901330189 = some 211192517901330189 := by decide +kernel
private theorem endpoint_7_50_p4 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 0 4 211192517901330189 = some 211192517901330189 :=
  join_receipt_window endpoint_7_50_flag endpoint_7_50_sources 0 2 2 211192517901330189 211192517901330189 211192517901330189 endpoint_7_50_w0 endpoint_7_50_w2
private theorem endpoint_7_50_w4 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 4 2 211192517901330189 = some 211192517901330189 := by decide +kernel
private theorem endpoint_7_50_p6 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 0 6 211192517901330189 = some 211192517901330189 :=
  join_receipt_window endpoint_7_50_flag endpoint_7_50_sources 0 4 2 211192517901330189 211192517901330189 211192517901330189 endpoint_7_50_p4 endpoint_7_50_w4
def endpoint_7_50 : CertifiedEndpoint :=
  ⟨⟨7, 50, 4198⟩, 211192517901330189, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_50_flag endpoint_7_50_sources 6 211192517901330189 211192517901330189 rfl endpoint_7_50_base endpoint_7_50_p6) (by decide)⟩
private def endpoint_7_51_flag : Flag := ⟨7, 51, 4164⟩
private def endpoint_7_51_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_51_base : receiptBase endpoint_7_51_flag endpoint_7_51_sources = some 213147748027519964 := by decide +kernel
private theorem endpoint_7_51_w0 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 0 2 213147748027519964 = some 213147748027519964 := by decide +kernel
private theorem endpoint_7_51_w2 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 2 2 213147748027519964 = some 213147748027519964 := by decide +kernel
private theorem endpoint_7_51_p4 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 0 4 213147748027519964 = some 213147748027519964 :=
  join_receipt_window endpoint_7_51_flag endpoint_7_51_sources 0 2 2 213147748027519964 213147748027519964 213147748027519964 endpoint_7_51_w0 endpoint_7_51_w2
private theorem endpoint_7_51_w4 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 4 2 213147748027519964 = some 213147748027519964 := by decide +kernel
private theorem endpoint_7_51_p6 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 0 6 213147748027519964 = some 213147748027519964 :=
  join_receipt_window endpoint_7_51_flag endpoint_7_51_sources 0 4 2 213147748027519964 213147748027519964 213147748027519964 endpoint_7_51_p4 endpoint_7_51_w4
def endpoint_7_51 : CertifiedEndpoint :=
  ⟨⟨7, 51, 4164⟩, 213147748027519964, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_51_flag endpoint_7_51_sources 6 213147748027519964 213147748027519964 rfl endpoint_7_51_base endpoint_7_51_p6) (by decide)⟩
private def endpoint_7_52_flag : Flag := ⟨7, 52, 4129⟩
private def endpoint_7_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_52_base : receiptBase endpoint_7_52_flag endpoint_7_52_sources = some 216389050978991657 := by decide +kernel
private theorem endpoint_7_52_w0 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 0 2 216389050978991657 = some 216389050978991657 := by decide +kernel
private theorem endpoint_7_52_w2 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 2 2 216389050978991657 = some 216389050978991657 := by decide +kernel
private theorem endpoint_7_52_p4 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 0 4 216389050978991657 = some 216389050978991657 :=
  join_receipt_window endpoint_7_52_flag endpoint_7_52_sources 0 2 2 216389050978991657 216389050978991657 216389050978991657 endpoint_7_52_w0 endpoint_7_52_w2
private theorem endpoint_7_52_w4 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 4 2 216389050978991657 = some 216389050978991657 := by decide +kernel
private theorem endpoint_7_52_p6 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 0 6 216389050978991657 = some 216389050978991657 :=
  join_receipt_window endpoint_7_52_flag endpoint_7_52_sources 0 4 2 216389050978991657 216389050978991657 216389050978991657 endpoint_7_52_p4 endpoint_7_52_w4
def endpoint_7_52 : CertifiedEndpoint :=
  ⟨⟨7, 52, 4129⟩, 216389050978991657, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_52_flag endpoint_7_52_sources 6 216389050978991657 216389050978991657 rfl endpoint_7_52_base endpoint_7_52_p6) (by decide)⟩
private def endpoint_7_53_flag : Flag := ⟨7, 53, 4093⟩
private def endpoint_7_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_53_base : receiptBase endpoint_7_53_flag endpoint_7_53_sources = some 218124110316793675 := by decide +kernel
private theorem endpoint_7_53_w0 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 0 2 218124110316793675 = some 218124110316793675 := by decide +kernel
private theorem endpoint_7_53_w2 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 2 2 218124110316793675 = some 218124110316793675 := by decide +kernel
private theorem endpoint_7_53_p4 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 0 4 218124110316793675 = some 218124110316793675 :=
  join_receipt_window endpoint_7_53_flag endpoint_7_53_sources 0 2 2 218124110316793675 218124110316793675 218124110316793675 endpoint_7_53_w0 endpoint_7_53_w2
private theorem endpoint_7_53_w4 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 4 2 218124110316793675 = some 218124110316793675 := by decide +kernel
private theorem endpoint_7_53_p6 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 0 6 218124110316793675 = some 218124110316793675 :=
  join_receipt_window endpoint_7_53_flag endpoint_7_53_sources 0 4 2 218124110316793675 218124110316793675 218124110316793675 endpoint_7_53_p4 endpoint_7_53_w4
def endpoint_7_53 : CertifiedEndpoint :=
  ⟨⟨7, 53, 4093⟩, 218124110316793675, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_53_flag endpoint_7_53_sources 6 218124110316793675 218124110316793675 rfl endpoint_7_53_base endpoint_7_53_p6) (by decide)⟩
private def endpoint_7_54_flag : Flag := ⟨7, 54, 4056⟩
private def endpoint_7_54_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_54_base : receiptBase endpoint_7_54_flag endpoint_7_54_sources = some 219741842021791626 := by decide +kernel
private theorem endpoint_7_54_w0 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 0 2 219741842021791626 = some 219741842021791626 := by decide +kernel
private theorem endpoint_7_54_w2 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 2 2 219741842021791626 = some 219741842021791626 := by decide +kernel
private theorem endpoint_7_54_p4 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 0 4 219741842021791626 = some 219741842021791626 :=
  join_receipt_window endpoint_7_54_flag endpoint_7_54_sources 0 2 2 219741842021791626 219741842021791626 219741842021791626 endpoint_7_54_w0 endpoint_7_54_w2
private theorem endpoint_7_54_w4 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 4 2 219741842021791626 = some 219741842021791626 := by decide +kernel
private theorem endpoint_7_54_p6 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 0 6 219741842021791626 = some 219741842021791626 :=
  join_receipt_window endpoint_7_54_flag endpoint_7_54_sources 0 4 2 219741842021791626 219741842021791626 219741842021791626 endpoint_7_54_p4 endpoint_7_54_w4
def endpoint_7_54 : CertifiedEndpoint :=
  ⟨⟨7, 54, 4056⟩, 219741842021791626, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_54_flag endpoint_7_54_sources 6 219741842021791626 219741842021791626 rfl endpoint_7_54_base endpoint_7_54_p6) (by decide)⟩
private def endpoint_7_55_flag : Flag := ⟨7, 55, 4019⟩
private def endpoint_7_55_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_55_base : receiptBase endpoint_7_55_flag endpoint_7_55_sources = some 221294094040015739 := by decide +kernel
private theorem endpoint_7_55_w0 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 0 2 221294094040015739 = some 221294094040015739 := by decide +kernel
private theorem endpoint_7_55_w2 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 2 2 221294094040015739 = some 221294094040015739 := by decide +kernel
private theorem endpoint_7_55_p4 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 0 4 221294094040015739 = some 221294094040015739 :=
  join_receipt_window endpoint_7_55_flag endpoint_7_55_sources 0 2 2 221294094040015739 221294094040015739 221294094040015739 endpoint_7_55_w0 endpoint_7_55_w2
private theorem endpoint_7_55_w4 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 4 2 221294094040015739 = some 221294094040015739 := by decide +kernel
private theorem endpoint_7_55_p6 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 0 6 221294094040015739 = some 221294094040015739 :=
  join_receipt_window endpoint_7_55_flag endpoint_7_55_sources 0 4 2 221294094040015739 221294094040015739 221294094040015739 endpoint_7_55_p4 endpoint_7_55_w4
def endpoint_7_55 : CertifiedEndpoint :=
  ⟨⟨7, 55, 4019⟩, 221294094040015739, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_55_flag endpoint_7_55_sources 6 221294094040015739 221294094040015739 rfl endpoint_7_55_base endpoint_7_55_p6) (by decide)⟩
private def endpoint_7_56_flag : Flag := ⟨7, 56, 3980⟩
private def endpoint_7_56_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_56_base : receiptBase endpoint_7_56_flag endpoint_7_56_sources = some 222670185979483011 := by decide +kernel
private theorem endpoint_7_56_w0 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 0 2 222670185979483011 = some 222670185979483011 := by decide +kernel
private theorem endpoint_7_56_w2 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 2 2 222670185979483011 = some 222670185979483011 := by decide +kernel
private theorem endpoint_7_56_p4 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 0 4 222670185979483011 = some 222670185979483011 :=
  join_receipt_window endpoint_7_56_flag endpoint_7_56_sources 0 2 2 222670185979483011 222670185979483011 222670185979483011 endpoint_7_56_w0 endpoint_7_56_w2
private theorem endpoint_7_56_w4 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 4 2 222670185979483011 = some 222670185979483011 := by decide +kernel
private theorem endpoint_7_56_p6 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 0 6 222670185979483011 = some 222670185979483011 :=
  join_receipt_window endpoint_7_56_flag endpoint_7_56_sources 0 4 2 222670185979483011 222670185979483011 222670185979483011 endpoint_7_56_p4 endpoint_7_56_w4
def endpoint_7_56 : CertifiedEndpoint :=
  ⟨⟨7, 56, 3980⟩, 222670185979483011, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_56_flag endpoint_7_56_sources 6 222670185979483011 222670185979483011 rfl endpoint_7_56_base endpoint_7_56_p6) (by decide)⟩
private def endpoint_7_57_flag : Flag := ⟨7, 57, 3941⟩
private def endpoint_7_57_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_57_base : receiptBase endpoint_7_57_flag endpoint_7_57_sources = some 223977305982215174 := by decide +kernel
private theorem endpoint_7_57_w0 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 0 2 223977305982215174 = some 223977305982215174 := by decide +kernel
private theorem endpoint_7_57_w2 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 2 2 223977305982215174 = some 223977305982215174 := by decide +kernel
private theorem endpoint_7_57_p4 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 0 4 223977305982215174 = some 223977305982215174 :=
  join_receipt_window endpoint_7_57_flag endpoint_7_57_sources 0 2 2 223977305982215174 223977305982215174 223977305982215174 endpoint_7_57_w0 endpoint_7_57_w2
private theorem endpoint_7_57_w4 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 4 2 223977305982215174 = some 223977305982215174 := by decide +kernel
private theorem endpoint_7_57_p6 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 0 6 223977305982215174 = some 223977305982215174 :=
  join_receipt_window endpoint_7_57_flag endpoint_7_57_sources 0 4 2 223977305982215174 223977305982215174 223977305982215174 endpoint_7_57_p4 endpoint_7_57_w4
def endpoint_7_57 : CertifiedEndpoint :=
  ⟨⟨7, 57, 3941⟩, 223977305982215174, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_57_flag endpoint_7_57_sources 6 223977305982215174 223977305982215174 rfl endpoint_7_57_base endpoint_7_57_p6) (by decide)⟩
private def endpoint_7_58_flag : Flag := ⟨7, 58, 3900⟩
private def endpoint_7_58_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_58_base : receiptBase endpoint_7_58_flag endpoint_7_58_sources = some 225827436010721843 := by decide +kernel
private theorem endpoint_7_58_w0 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 0 2 225827436010721843 = some 225827436010721843 := by decide +kernel
private theorem endpoint_7_58_w2 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 2 2 225827436010721843 = some 225827436010721843 := by decide +kernel
private theorem endpoint_7_58_p4 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 0 4 225827436010721843 = some 225827436010721843 :=
  join_receipt_window endpoint_7_58_flag endpoint_7_58_sources 0 2 2 225827436010721843 225827436010721843 225827436010721843 endpoint_7_58_w0 endpoint_7_58_w2
private theorem endpoint_7_58_w4 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 4 2 225827436010721843 = some 225827436010721843 := by decide +kernel
private theorem endpoint_7_58_p6 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 0 6 225827436010721843 = some 225827436010721843 :=
  join_receipt_window endpoint_7_58_flag endpoint_7_58_sources 0 4 2 225827436010721843 225827436010721843 225827436010721843 endpoint_7_58_p4 endpoint_7_58_w4
def endpoint_7_58 : CertifiedEndpoint :=
  ⟨⟨7, 58, 3900⟩, 225827436010721843, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_58_flag endpoint_7_58_sources 6 225827436010721843 225827436010721843 rfl endpoint_7_58_base endpoint_7_58_p6) (by decide)⟩
private def endpoint_7_59_flag : Flag := ⟨7, 59, 3858⟩
private def endpoint_7_59_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_59_base : receiptBase endpoint_7_59_flag endpoint_7_59_sources = some 226812859687165549 := by decide +kernel
private theorem endpoint_7_59_w0 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 0 2 226812859687165549 = some 226812859687165549 := by decide +kernel
private theorem endpoint_7_59_w2 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 2 2 226812859687165549 = some 226812859687165549 := by decide +kernel
private theorem endpoint_7_59_p4 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 0 4 226812859687165549 = some 226812859687165549 :=
  join_receipt_window endpoint_7_59_flag endpoint_7_59_sources 0 2 2 226812859687165549 226812859687165549 226812859687165549 endpoint_7_59_w0 endpoint_7_59_w2
private theorem endpoint_7_59_w4 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 4 2 226812859687165549 = some 226812859687165549 := by decide +kernel
private theorem endpoint_7_59_p6 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 0 6 226812859687165549 = some 226812859687165549 :=
  join_receipt_window endpoint_7_59_flag endpoint_7_59_sources 0 4 2 226812859687165549 226812859687165549 226812859687165549 endpoint_7_59_p4 endpoint_7_59_w4
def endpoint_7_59 : CertifiedEndpoint :=
  ⟨⟨7, 59, 3858⟩, 226812859687165549, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_59_flag endpoint_7_59_sources 6 226812859687165549 226812859687165549 rfl endpoint_7_59_base endpoint_7_59_p6) (by decide)⟩
private def endpoint_7_60_flag : Flag := ⟨7, 60, 3815⟩
private def endpoint_7_60_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_60_base : receiptBase endpoint_7_60_flag endpoint_7_60_sources = some 227665051592948031 := by decide +kernel
private theorem endpoint_7_60_w0 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 0 2 227665051592948031 = some 227665051592948031 := by decide +kernel
private theorem endpoint_7_60_w2 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 2 2 227665051592948031 = some 227665051592948031 := by decide +kernel
private theorem endpoint_7_60_p4 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 0 4 227665051592948031 = some 227665051592948031 :=
  join_receipt_window endpoint_7_60_flag endpoint_7_60_sources 0 2 2 227665051592948031 227665051592948031 227665051592948031 endpoint_7_60_w0 endpoint_7_60_w2
private theorem endpoint_7_60_w4 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 4 2 227665051592948031 = some 227665051592948031 := by decide +kernel
private theorem endpoint_7_60_p6 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 0 6 227665051592948031 = some 227665051592948031 :=
  join_receipt_window endpoint_7_60_flag endpoint_7_60_sources 0 4 2 227665051592948031 227665051592948031 227665051592948031 endpoint_7_60_p4 endpoint_7_60_w4
def endpoint_7_60 : CertifiedEndpoint :=
  ⟨⟨7, 60, 3815⟩, 227665051592948031, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_60_flag endpoint_7_60_sources 6 227665051592948031 227665051592948031 rfl endpoint_7_60_base endpoint_7_60_p6) (by decide)⟩
private def endpoint_7_61_flag : Flag := ⟨7, 61, 3770⟩
private def endpoint_7_61_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_61_base : receiptBase endpoint_7_61_flag endpoint_7_61_sources = some 228321498019123809 := by decide +kernel
private theorem endpoint_7_61_w0 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 0 2 228321498019123809 = some 228321498019123809 := by decide +kernel
private theorem endpoint_7_61_w2 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 2 2 228321498019123809 = some 228321498019123809 := by decide +kernel
private theorem endpoint_7_61_p4 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 0 4 228321498019123809 = some 228321498019123809 :=
  join_receipt_window endpoint_7_61_flag endpoint_7_61_sources 0 2 2 228321498019123809 228321498019123809 228321498019123809 endpoint_7_61_w0 endpoint_7_61_w2
private theorem endpoint_7_61_w4 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 4 2 228321498019123809 = some 228321498019123809 := by decide +kernel
private theorem endpoint_7_61_p6 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 0 6 228321498019123809 = some 228321498019123809 :=
  join_receipt_window endpoint_7_61_flag endpoint_7_61_sources 0 4 2 228321498019123809 228321498019123809 228321498019123809 endpoint_7_61_p4 endpoint_7_61_w4
def endpoint_7_61 : CertifiedEndpoint :=
  ⟨⟨7, 61, 3770⟩, 228321498019123809, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_61_flag endpoint_7_61_sources 6 228321498019123809 228321498019123809 rfl endpoint_7_61_base endpoint_7_61_p6) (by decide)⟩
private def endpoint_7_62_flag : Flag := ⟨7, 62, 3723⟩
private def endpoint_7_62_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_62_base : receiptBase endpoint_7_62_flag endpoint_7_62_sources = some 228776960590750976 := by decide +kernel
private theorem endpoint_7_62_w0 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 0 2 228776960590750976 = some 228776960590750976 := by decide +kernel
private theorem endpoint_7_62_w2 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 2 2 228776960590750976 = some 228776960590750976 := by decide +kernel
private theorem endpoint_7_62_p4 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 0 4 228776960590750976 = some 228776960590750976 :=
  join_receipt_window endpoint_7_62_flag endpoint_7_62_sources 0 2 2 228776960590750976 228776960590750976 228776960590750976 endpoint_7_62_w0 endpoint_7_62_w2
private theorem endpoint_7_62_w4 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 4 2 228776960590750976 = some 228776960590750976 := by decide +kernel
private theorem endpoint_7_62_p6 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 0 6 228776960590750976 = some 228776960590750976 :=
  join_receipt_window endpoint_7_62_flag endpoint_7_62_sources 0 4 2 228776960590750976 228776960590750976 228776960590750976 endpoint_7_62_p4 endpoint_7_62_w4
def endpoint_7_62 : CertifiedEndpoint :=
  ⟨⟨7, 62, 3723⟩, 228776960590750976, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_62_flag endpoint_7_62_sources 6 228776960590750976 228776960590750976 rfl endpoint_7_62_base endpoint_7_62_p6) (by decide)⟩
private def endpoint_7_63_flag : Flag := ⟨7, 63, 3674⟩
private def endpoint_7_63_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_63_base : receiptBase endpoint_7_63_flag endpoint_7_63_sources = some 231468939631778301 := by decide +kernel
private theorem endpoint_7_63_w0 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 0 2 231468939631778301 = some 231468939631778301 := by decide +kernel
private theorem endpoint_7_63_w2 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 2 2 231468939631778301 = some 231468939631778301 := by decide +kernel
private theorem endpoint_7_63_p4 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 0 4 231468939631778301 = some 231468939631778301 :=
  join_receipt_window endpoint_7_63_flag endpoint_7_63_sources 0 2 2 231468939631778301 231468939631778301 231468939631778301 endpoint_7_63_w0 endpoint_7_63_w2
private theorem endpoint_7_63_w4 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 4 2 231468939631778301 = some 231468939631778301 := by decide +kernel
private theorem endpoint_7_63_p6 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 0 6 231468939631778301 = some 231468939631778301 :=
  join_receipt_window endpoint_7_63_flag endpoint_7_63_sources 0 4 2 231468939631778301 231468939631778301 231468939631778301 endpoint_7_63_p4 endpoint_7_63_w4
def endpoint_7_63 : CertifiedEndpoint :=
  ⟨⟨7, 63, 3674⟩, 231468939631778301, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_63_flag endpoint_7_63_sources 6 231468939631778301 231468939631778301 rfl endpoint_7_63_base endpoint_7_63_p6) (by decide)⟩
private def endpoint_7_64_flag : Flag := ⟨7, 64, 3623⟩
private def endpoint_7_64_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_64_base : receiptBase endpoint_7_64_flag endpoint_7_64_sources = some 231487914307504244 := by decide +kernel
private theorem endpoint_7_64_w0 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 0 2 231487914307504244 = some 231487914307504244 := by decide +kernel
private theorem endpoint_7_64_w2 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 2 2 231487914307504244 = some 231487914307504244 := by decide +kernel
private theorem endpoint_7_64_p4 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 0 4 231487914307504244 = some 231487914307504244 :=
  join_receipt_window endpoint_7_64_flag endpoint_7_64_sources 0 2 2 231487914307504244 231487914307504244 231487914307504244 endpoint_7_64_w0 endpoint_7_64_w2
private theorem endpoint_7_64_w4 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 4 2 231487914307504244 = some 231487914307504244 := by decide +kernel
private theorem endpoint_7_64_p6 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 0 6 231487914307504244 = some 231487914307504244 :=
  join_receipt_window endpoint_7_64_flag endpoint_7_64_sources 0 4 2 231487914307504244 231487914307504244 231487914307504244 endpoint_7_64_p4 endpoint_7_64_w4
def endpoint_7_64 : CertifiedEndpoint :=
  ⟨⟨7, 64, 3623⟩, 231487914307504244, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_64_flag endpoint_7_64_sources 6 231487914307504244 231487914307504244 rfl endpoint_7_64_base endpoint_7_64_p6) (by decide)⟩
private def endpoint_7_65_flag : Flag := ⟨7, 65, 3570⟩
private def endpoint_7_65_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_65_base : receiptBase endpoint_7_65_flag endpoint_7_65_sources = some 231287591642887945 := by decide +kernel
private theorem endpoint_7_65_w0 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 0 2 231287591642887945 = some 231287591642887945 := by decide +kernel
private theorem endpoint_7_65_w2 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 2 2 231287591642887945 = some 231287591642887945 := by decide +kernel
private theorem endpoint_7_65_p4 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 0 4 231287591642887945 = some 231287591642887945 :=
  join_receipt_window endpoint_7_65_flag endpoint_7_65_sources 0 2 2 231287591642887945 231287591642887945 231287591642887945 endpoint_7_65_w0 endpoint_7_65_w2
private theorem endpoint_7_65_w4 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 4 2 231287591642887945 = some 231287591642887945 := by decide +kernel
private theorem endpoint_7_65_p6 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 0 6 231287591642887945 = some 231287591642887945 :=
  join_receipt_window endpoint_7_65_flag endpoint_7_65_sources 0 4 2 231287591642887945 231287591642887945 231287591642887945 endpoint_7_65_p4 endpoint_7_65_w4
def endpoint_7_65 : CertifiedEndpoint :=
  ⟨⟨7, 65, 3570⟩, 231287591642887945, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_65_flag endpoint_7_65_sources 6 231287591642887945 231287591642887945 rfl endpoint_7_65_base endpoint_7_65_p6) (by decide)⟩
private def endpoint_7_66_flag : Flag := ⟨7, 66, 3514⟩
private def endpoint_7_66_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_66_base : receiptBase endpoint_7_66_flag endpoint_7_66_sources = some 230797574544433867 := by decide +kernel
private theorem endpoint_7_66_w0 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 0 2 230797574544433867 = some 230797574544433867 := by decide +kernel
private theorem endpoint_7_66_w2 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 2 2 230797574544433867 = some 230797574544433867 := by decide +kernel
private theorem endpoint_7_66_p4 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 0 4 230797574544433867 = some 230797574544433867 :=
  join_receipt_window endpoint_7_66_flag endpoint_7_66_sources 0 2 2 230797574544433867 230797574544433867 230797574544433867 endpoint_7_66_w0 endpoint_7_66_w2
private theorem endpoint_7_66_w4 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 4 2 230797574544433867 = some 230797574544433867 := by decide +kernel
private theorem endpoint_7_66_p6 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 0 6 230797574544433867 = some 230797574544433867 :=
  join_receipt_window endpoint_7_66_flag endpoint_7_66_sources 0 4 2 230797574544433867 230797574544433867 230797574544433867 endpoint_7_66_p4 endpoint_7_66_w4
def endpoint_7_66 : CertifiedEndpoint :=
  ⟨⟨7, 66, 3514⟩, 230797574544433867, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_66_flag endpoint_7_66_sources 6 230797574544433867 230797574544433867 rfl endpoint_7_66_base endpoint_7_66_p6) (by decide)⟩
private def endpoint_7_67_flag : Flag := ⟨7, 67, 3455⟩
private def endpoint_7_67_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_7_67_base : receiptBase endpoint_7_67_flag endpoint_7_67_sources = some 231687636567784067 := by decide +kernel
private theorem endpoint_7_67_w0 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 0 2 231687636567784067 = some 231687636567784067 := by decide +kernel
private theorem endpoint_7_67_w2 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 2 2 231687636567784067 = some 231687636567784067 := by decide +kernel
private theorem endpoint_7_67_p4 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 0 4 231687636567784067 = some 231687636567784067 :=
  join_receipt_window endpoint_7_67_flag endpoint_7_67_sources 0 2 2 231687636567784067 231687636567784067 231687636567784067 endpoint_7_67_w0 endpoint_7_67_w2
private theorem endpoint_7_67_w4 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 4 2 231687636567784067 = some 231687636567784067 := by decide +kernel
private theorem endpoint_7_67_p6 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 0 6 231687636567784067 = some 231687636567784067 :=
  join_receipt_window endpoint_7_67_flag endpoint_7_67_sources 0 4 2 231687636567784067 231687636567784067 231687636567784067 endpoint_7_67_p4 endpoint_7_67_w4
def endpoint_7_67 : CertifiedEndpoint :=
  ⟨⟨7, 67, 3455⟩, 231687636567784067, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_7_67_flag endpoint_7_67_sources 6 231687636567784067 231687636567784067 rfl endpoint_7_67_base endpoint_7_67_p6) (by decide)⟩
private def endpoint_7_68_flag : Flag := ⟨7, 68, 3393⟩
private def endpoint_7_68_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_7_68_base : receiptBase endpoint_7_68_flag endpoint_7_68_sources = some 230588420539775757 := by decide +kernel
private theorem endpoint_7_68_w0 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 0 2 230588420539775757 = some 230588420539775757 := by decide +kernel
private theorem endpoint_7_68_w2 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 2 2 230588420539775757 = some 230588420539775757 := by decide +kernel
private theorem endpoint_7_68_p4 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 0 4 230588420539775757 = some 230588420539775757 :=
  join_receipt_window endpoint_7_68_flag endpoint_7_68_sources 0 2 2 230588420539775757 230588420539775757 230588420539775757 endpoint_7_68_w0 endpoint_7_68_w2
private theorem endpoint_7_68_w4 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 4 2 230588420539775757 = some 230588420539775757 := by decide +kernel
private theorem endpoint_7_68_p6 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 0 6 230588420539775757 = some 230588420539775757 :=
  join_receipt_window endpoint_7_68_flag endpoint_7_68_sources 0 4 2 230588420539775757 230588420539775757 230588420539775757 endpoint_7_68_p4 endpoint_7_68_w4
def endpoint_7_68 : CertifiedEndpoint :=
  ⟨⟨7, 68, 3393⟩, 230588420539775757, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_7_68_flag endpoint_7_68_sources 6 230588420539775757 230588420539775757 rfl endpoint_7_68_base endpoint_7_68_p6) (by decide)⟩
private def endpoint_7_69_flag : Flag := ⟨7, 69, 3328⟩
private def endpoint_7_69_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_7_69_base : receiptBase endpoint_7_69_flag endpoint_7_69_sources = some 229172905104888451 := by decide +kernel
private theorem endpoint_7_69_w0 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 0 2 229172905104888451 = some 229172905104888451 := by decide +kernel
private theorem endpoint_7_69_w2 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 2 2 229172905104888451 = some 229172905104888451 := by decide +kernel
private theorem endpoint_7_69_p4 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 0 4 229172905104888451 = some 229172905104888451 :=
  join_receipt_window endpoint_7_69_flag endpoint_7_69_sources 0 2 2 229172905104888451 229172905104888451 229172905104888451 endpoint_7_69_w0 endpoint_7_69_w2
private theorem endpoint_7_69_w4 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 4 2 229172905104888451 = some 229172905104888451 := by decide +kernel
private theorem endpoint_7_69_p6 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 0 6 229172905104888451 = some 229172905104888451 :=
  join_receipt_window endpoint_7_69_flag endpoint_7_69_sources 0 4 2 229172905104888451 229172905104888451 229172905104888451 endpoint_7_69_p4 endpoint_7_69_w4
def endpoint_7_69 : CertifiedEndpoint :=
  ⟨⟨7, 69, 3328⟩, 229172905104888451, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_7_69_flag endpoint_7_69_sources 6 229172905104888451 229172905104888451 rfl endpoint_7_69_base endpoint_7_69_p6) (by decide)⟩
private def endpoint_7_70_flag : Flag := ⟨7, 70, 3259⟩
private def endpoint_7_70_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_7_70_base : receiptBase endpoint_7_70_flag endpoint_7_70_sources = some 229059717241160915 := by decide +kernel
private theorem endpoint_7_70_w0 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 0 2 229059717241160915 = some 229059717241160915 := by decide +kernel
private theorem endpoint_7_70_w2 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 2 2 229059717241160915 = some 229059717241160915 := by decide +kernel
private theorem endpoint_7_70_p4 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 0 4 229059717241160915 = some 229059717241160915 :=
  join_receipt_window endpoint_7_70_flag endpoint_7_70_sources 0 2 2 229059717241160915 229059717241160915 229059717241160915 endpoint_7_70_w0 endpoint_7_70_w2
private theorem endpoint_7_70_w4 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 4 2 229059717241160915 = some 229059717241160915 := by decide +kernel
private theorem endpoint_7_70_p6 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 0 6 229059717241160915 = some 229059717241160915 :=
  join_receipt_window endpoint_7_70_flag endpoint_7_70_sources 0 4 2 229059717241160915 229059717241160915 229059717241160915 endpoint_7_70_p4 endpoint_7_70_w4
def endpoint_7_70 : CertifiedEndpoint :=
  ⟨⟨7, 70, 3259⟩, 229059717241160915, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_7_70_flag endpoint_7_70_sources 6 229059717241160915 229059717241160915 rfl endpoint_7_70_base endpoint_7_70_p6) (by decide)⟩
private def endpoint_7_71_flag : Flag := ⟨7, 71, 3188⟩
private def endpoint_7_71_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_7_71_base : receiptBase endpoint_7_71_flag endpoint_7_71_sources = some 228696581626623551 := by decide +kernel
private theorem endpoint_7_71_w0 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 0 2 228696581626623551 = some 228696581626623551 := by decide +kernel
private theorem endpoint_7_71_w2 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 2 2 228696581626623551 = some 228696581626623551 := by decide +kernel
private theorem endpoint_7_71_p4 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 0 4 228696581626623551 = some 228696581626623551 :=
  join_receipt_window endpoint_7_71_flag endpoint_7_71_sources 0 2 2 228696581626623551 228696581626623551 228696581626623551 endpoint_7_71_w0 endpoint_7_71_w2
private theorem endpoint_7_71_w4 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 4 2 228696581626623551 = some 228696581626623551 := by decide +kernel
private theorem endpoint_7_71_p6 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 0 6 228696581626623551 = some 228696581626623551 :=
  join_receipt_window endpoint_7_71_flag endpoint_7_71_sources 0 4 2 228696581626623551 228696581626623551 228696581626623551 endpoint_7_71_p4 endpoint_7_71_w4
def endpoint_7_71 : CertifiedEndpoint :=
  ⟨⟨7, 71, 3188⟩, 228696581626623551, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_7_71_flag endpoint_7_71_sources 6 228696581626623551 228696581626623551 rfl endpoint_7_71_base endpoint_7_71_p6) (by decide)⟩
private def endpoint_7_72_flag : Flag := ⟨7, 72, 3114⟩
private def endpoint_7_72_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_7_72_base : receiptBase endpoint_7_72_flag endpoint_7_72_sources = some 226249976368108931 := by decide +kernel
private theorem endpoint_7_72_w0 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 0 2 226249976368108931 = some 226249976368108931 := by decide +kernel
private theorem endpoint_7_72_w2 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 2 2 226249976368108931 = some 226249976368108931 := by decide +kernel
private theorem endpoint_7_72_p4 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 0 4 226249976368108931 = some 226249976368108931 :=
  join_receipt_window endpoint_7_72_flag endpoint_7_72_sources 0 2 2 226249976368108931 226249976368108931 226249976368108931 endpoint_7_72_w0 endpoint_7_72_w2
private theorem endpoint_7_72_w4 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 4 2 226249976368108931 = some 226249976368108931 := by decide +kernel
private theorem endpoint_7_72_p6 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 0 6 226249976368108931 = some 226249976368108931 :=
  join_receipt_window endpoint_7_72_flag endpoint_7_72_sources 0 4 2 226249976368108931 226249976368108931 226249976368108931 endpoint_7_72_p4 endpoint_7_72_w4
def endpoint_7_72 : CertifiedEndpoint :=
  ⟨⟨7, 72, 3114⟩, 226249976368108931, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_7_72_flag endpoint_7_72_sources 6 226249976368108931 226249976368108931 rfl endpoint_7_72_base endpoint_7_72_p6) (by decide)⟩
private def endpoint_7_73_flag : Flag := ⟨7, 73, 3036⟩
private def endpoint_7_73_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_7_73_base : receiptBase endpoint_7_73_flag endpoint_7_73_sources = some 226719420473741381 := by decide +kernel
private theorem endpoint_7_73_w0 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 0 2 226719420473741381 = some 226719420473741381 := by decide +kernel
private theorem endpoint_7_73_w2 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 2 2 226719420473741381 = some 226719420473741381 := by decide +kernel
private theorem endpoint_7_73_p4 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 0 4 226719420473741381 = some 226719420473741381 :=
  join_receipt_window endpoint_7_73_flag endpoint_7_73_sources 0 2 2 226719420473741381 226719420473741381 226719420473741381 endpoint_7_73_w0 endpoint_7_73_w2
private theorem endpoint_7_73_w4 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 4 2 226719420473741381 = some 226719420473741381 := by decide +kernel
private theorem endpoint_7_73_p6 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 0 6 226719420473741381 = some 226719420473741381 :=
  join_receipt_window endpoint_7_73_flag endpoint_7_73_sources 0 4 2 226719420473741381 226719420473741381 226719420473741381 endpoint_7_73_p4 endpoint_7_73_w4
def endpoint_7_73 : CertifiedEndpoint :=
  ⟨⟨7, 73, 3036⟩, 226719420473741381, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_7_73_flag endpoint_7_73_sources 6 226719420473741381 226719420473741381 rfl endpoint_7_73_base endpoint_7_73_p6) (by decide)⟩
private def endpoint_7_74_flag : Flag := ⟨7, 74, 2955⟩
private def endpoint_7_74_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_7_74_base : receiptBase endpoint_7_74_flag endpoint_7_74_sources = some 223433735936516620 := by decide +kernel
private theorem endpoint_7_74_w0 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 0 2 223433735936516620 = some 223433735936516620 := by decide +kernel
private theorem endpoint_7_74_w2 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 2 2 223433735936516620 = some 223433735936516620 := by decide +kernel
private theorem endpoint_7_74_p4 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 0 4 223433735936516620 = some 223433735936516620 :=
  join_receipt_window endpoint_7_74_flag endpoint_7_74_sources 0 2 2 223433735936516620 223433735936516620 223433735936516620 endpoint_7_74_w0 endpoint_7_74_w2
private theorem endpoint_7_74_w4 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 4 2 223433735936516620 = some 223433735936516620 := by decide +kernel
private theorem endpoint_7_74_p6 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 0 6 223433735936516620 = some 223433735936516620 :=
  join_receipt_window endpoint_7_74_flag endpoint_7_74_sources 0 4 2 223433735936516620 223433735936516620 223433735936516620 endpoint_7_74_p4 endpoint_7_74_w4
def endpoint_7_74 : CertifiedEndpoint :=
  ⟨⟨7, 74, 2955⟩, 223433735936516620, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_7_74_flag endpoint_7_74_sources 6 223433735936516620 223433735936516620 rfl endpoint_7_74_base endpoint_7_74_p6) (by decide)⟩
private def endpoint_7_75_flag : Flag := ⟨7, 75, 2871⟩
private def endpoint_7_75_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_7_75_base : receiptBase endpoint_7_75_flag endpoint_7_75_sources = some 219768680051637424 := by decide +kernel
private theorem endpoint_7_75_w0 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 0 2 219768680051637424 = some 219768680051637424 := by decide +kernel
private theorem endpoint_7_75_w2 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 2 2 219768680051637424 = some 219768680051637424 := by decide +kernel
private theorem endpoint_7_75_p4 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 0 4 219768680051637424 = some 219768680051637424 :=
  join_receipt_window endpoint_7_75_flag endpoint_7_75_sources 0 2 2 219768680051637424 219768680051637424 219768680051637424 endpoint_7_75_w0 endpoint_7_75_w2
private theorem endpoint_7_75_w4 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 4 2 219768680051637424 = some 219768680051637424 := by decide +kernel
private theorem endpoint_7_75_p6 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 0 6 219768680051637424 = some 219768680051637424 :=
  join_receipt_window endpoint_7_75_flag endpoint_7_75_sources 0 4 2 219768680051637424 219768680051637424 219768680051637424 endpoint_7_75_p4 endpoint_7_75_w4
def endpoint_7_75 : CertifiedEndpoint :=
  ⟨⟨7, 75, 2871⟩, 219768680051637424, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_7_75_flag endpoint_7_75_sources 6 219768680051637424 219768680051637424 rfl endpoint_7_75_base endpoint_7_75_p6) (by decide)⟩
private def endpoint_7_76_flag : Flag := ⟨7, 76, 2784⟩
private def endpoint_7_76_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_7_76_base : receiptBase endpoint_7_76_flag endpoint_7_76_sources = some 219631856042905081 := by decide +kernel
private theorem endpoint_7_76_w0 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 0 2 219631856042905081 = some 219631856042905081 := by decide +kernel
private theorem endpoint_7_76_w2 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 2 2 219631856042905081 = some 219631856042905081 := by decide +kernel
private theorem endpoint_7_76_p4 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 0 4 219631856042905081 = some 219631856042905081 :=
  join_receipt_window endpoint_7_76_flag endpoint_7_76_sources 0 2 2 219631856042905081 219631856042905081 219631856042905081 endpoint_7_76_w0 endpoint_7_76_w2
private theorem endpoint_7_76_w4 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 4 2 219631856042905081 = some 219631856042905081 := by decide +kernel
private theorem endpoint_7_76_p6 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 0 6 219631856042905081 = some 219631856042905081 :=
  join_receipt_window endpoint_7_76_flag endpoint_7_76_sources 0 4 2 219631856042905081 219631856042905081 219631856042905081 endpoint_7_76_p4 endpoint_7_76_w4
def endpoint_7_76 : CertifiedEndpoint :=
  ⟨⟨7, 76, 2784⟩, 219631856042905081, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_7_76_flag endpoint_7_76_sources 6 219631856042905081 219631856042905081 rfl endpoint_7_76_base endpoint_7_76_p6) (by decide)⟩
private def endpoint_7_77_flag : Flag := ⟨7, 77, 2694⟩
private def endpoint_7_77_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_7_77_base : receiptBase endpoint_7_77_flag endpoint_7_77_sources = some 215144366781656952 := by decide +kernel
private theorem endpoint_7_77_w0 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 0 2 215144366781656952 = some 215144366781656952 := by decide +kernel
private theorem endpoint_7_77_w2 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 2 2 215144366781656952 = some 215144366781656952 := by decide +kernel
private theorem endpoint_7_77_p4 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 0 4 215144366781656952 = some 215144366781656952 :=
  join_receipt_window endpoint_7_77_flag endpoint_7_77_sources 0 2 2 215144366781656952 215144366781656952 215144366781656952 endpoint_7_77_w0 endpoint_7_77_w2
private theorem endpoint_7_77_w4 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 4 2 215144366781656952 = some 215144366781656952 := by decide +kernel
private theorem endpoint_7_77_p6 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 0 6 215144366781656952 = some 215144366781656952 :=
  join_receipt_window endpoint_7_77_flag endpoint_7_77_sources 0 4 2 215144366781656952 215144366781656952 215144366781656952 endpoint_7_77_p4 endpoint_7_77_w4
def endpoint_7_77 : CertifiedEndpoint :=
  ⟨⟨7, 77, 2694⟩, 215144366781656952, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_7_77_flag endpoint_7_77_sources 6 215144366781656952 215144366781656952 rfl endpoint_7_77_base endpoint_7_77_p6) (by decide)⟩
private def endpoint_7_78_flag : Flag := ⟨7, 78, 2601⟩
private def endpoint_7_78_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_7_78_base : receiptBase endpoint_7_78_flag endpoint_7_78_sources = some 210249741337808580 := by decide +kernel
private theorem endpoint_7_78_w0 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 0 2 210249741337808580 = some 210249741337808580 := by decide +kernel
private theorem endpoint_7_78_w2 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 2 2 210249741337808580 = some 210249741337808580 := by decide +kernel
private theorem endpoint_7_78_p4 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 0 4 210249741337808580 = some 210249741337808580 :=
  join_receipt_window endpoint_7_78_flag endpoint_7_78_sources 0 2 2 210249741337808580 210249741337808580 210249741337808580 endpoint_7_78_w0 endpoint_7_78_w2
private theorem endpoint_7_78_w4 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 4 2 210249741337808580 = some 210249741337808580 := by decide +kernel
private theorem endpoint_7_78_p6 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 0 6 210249741337808580 = some 210249741337808580 :=
  join_receipt_window endpoint_7_78_flag endpoint_7_78_sources 0 4 2 210249741337808580 210249741337808580 210249741337808580 endpoint_7_78_p4 endpoint_7_78_w4
def endpoint_7_78 : CertifiedEndpoint :=
  ⟨⟨7, 78, 2601⟩, 210249741337808580, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_7_78_flag endpoint_7_78_sources 6 210249741337808580 210249741337808580 rfl endpoint_7_78_base endpoint_7_78_p6) (by decide)⟩
private def endpoint_7_79_flag : Flag := ⟨7, 79, 2504⟩
private def endpoint_7_79_sources : Sources := ⟨contact11, contact11, contact13⟩
private theorem endpoint_7_79_base : receiptBase endpoint_7_79_flag endpoint_7_79_sources = some 204912525435470807 := by decide +kernel
private theorem endpoint_7_79_w0 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 0 2 204912525435470807 = some 204912525435470807 := by decide +kernel
private theorem endpoint_7_79_w2 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 2 2 204912525435470807 = some 204912525435470807 := by decide +kernel
private theorem endpoint_7_79_p4 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 0 4 204912525435470807 = some 204912525435470807 :=
  join_receipt_window endpoint_7_79_flag endpoint_7_79_sources 0 2 2 204912525435470807 204912525435470807 204912525435470807 endpoint_7_79_w0 endpoint_7_79_w2
private theorem endpoint_7_79_w4 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 4 2 204912525435470807 = some 204912525435470807 := by decide +kernel
private theorem endpoint_7_79_p6 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 0 6 204912525435470807 = some 204912525435470807 :=
  join_receipt_window endpoint_7_79_flag endpoint_7_79_sources 0 4 2 204912525435470807 204912525435470807 204912525435470807 endpoint_7_79_p4 endpoint_7_79_w4
def endpoint_7_79 : CertifiedEndpoint :=
  ⟨⟨7, 79, 2504⟩, 204912525435470807, .terminal ⟨contact11, contact11, contact13⟩ (finish_receipt_window endpoint_7_79_flag endpoint_7_79_sources 6 204912525435470807 204912525435470807 rfl endpoint_7_79_base endpoint_7_79_p6) (by decide)⟩
private def endpoint_7_80_flag : Flag := ⟨7, 80, 2405⟩
private def endpoint_7_80_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_7_80_base : receiptBase endpoint_7_80_flag endpoint_7_80_sources = some 201404324252014208 := by decide +kernel
private theorem endpoint_7_80_w0 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 0 2 201404324252014208 = some 201404324252014208 := by decide +kernel
private theorem endpoint_7_80_w2 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 2 2 201404324252014208 = some 201404324252014208 := by decide +kernel
private theorem endpoint_7_80_p4 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 0 4 201404324252014208 = some 201404324252014208 :=
  join_receipt_window endpoint_7_80_flag endpoint_7_80_sources 0 2 2 201404324252014208 201404324252014208 201404324252014208 endpoint_7_80_w0 endpoint_7_80_w2
private theorem endpoint_7_80_w4 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 4 2 201404324252014208 = some 201404324252014208 := by decide +kernel
private theorem endpoint_7_80_p6 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 0 6 201404324252014208 = some 201404324252014208 :=
  join_receipt_window endpoint_7_80_flag endpoint_7_80_sources 0 4 2 201404324252014208 201404324252014208 201404324252014208 endpoint_7_80_p4 endpoint_7_80_w4
def endpoint_7_80 : CertifiedEndpoint :=
  ⟨⟨7, 80, 2405⟩, 201404324252014208, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_7_80_flag endpoint_7_80_sources 6 201404324252014208 201404324252014208 rfl endpoint_7_80_base endpoint_7_80_p6) (by decide)⟩
private def endpoint_7_81_flag : Flag := ⟨7, 81, 2302⟩
private def endpoint_7_81_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_7_81_base : receiptBase endpoint_7_81_flag endpoint_7_81_sources = some 195012070233305154 := by decide +kernel
private theorem endpoint_7_81_w0 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 0 2 195012070233305154 = some 195012070233305154 := by decide +kernel
private theorem endpoint_7_81_w2 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 2 2 195012070233305154 = some 195012070233305154 := by decide +kernel
private theorem endpoint_7_81_p4 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 0 4 195012070233305154 = some 195012070233305154 :=
  join_receipt_window endpoint_7_81_flag endpoint_7_81_sources 0 2 2 195012070233305154 195012070233305154 195012070233305154 endpoint_7_81_w0 endpoint_7_81_w2
private theorem endpoint_7_81_w4 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 4 2 195012070233305154 = some 195012070233305154 := by decide +kernel
private theorem endpoint_7_81_p6 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 0 6 195012070233305154 = some 195012070233305154 :=
  join_receipt_window endpoint_7_81_flag endpoint_7_81_sources 0 4 2 195012070233305154 195012070233305154 195012070233305154 endpoint_7_81_p4 endpoint_7_81_w4
def endpoint_7_81 : CertifiedEndpoint :=
  ⟨⟨7, 81, 2302⟩, 195012070233305154, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_7_81_flag endpoint_7_81_sources 6 195012070233305154 195012070233305154 rfl endpoint_7_81_base endpoint_7_81_p6) (by decide)⟩
private def endpoint_7_82_flag : Flag := ⟨7, 82, 2196⟩
private def endpoint_7_82_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_7_82_base : receiptBase endpoint_7_82_flag endpoint_7_82_sources = some 188169361466679648 := by decide +kernel
private theorem endpoint_7_82_w0 : receiptWindow endpoint_7_82_flag endpoint_7_82_sources 0 2 188169361466679648 = some 188169361466679648 := by decide +kernel
private theorem endpoint_7_82_w2 : receiptWindow endpoint_7_82_flag endpoint_7_82_sources 2 2 188169361466679648 = some 188169361466679648 := by decide +kernel
private theorem endpoint_7_82_p4 : receiptWindow endpoint_7_82_flag endpoint_7_82_sources 0 4 188169361466679648 = some 188169361466679648 :=
  join_receipt_window endpoint_7_82_flag endpoint_7_82_sources 0 2 2 188169361466679648 188169361466679648 188169361466679648 endpoint_7_82_w0 endpoint_7_82_w2
private theorem endpoint_7_82_w4 : receiptWindow endpoint_7_82_flag endpoint_7_82_sources 4 2 188169361466679648 = some 188169361466679648 := by decide +kernel
private theorem endpoint_7_82_p6 : receiptWindow endpoint_7_82_flag endpoint_7_82_sources 0 6 188169361466679648 = some 188169361466679648 :=
  join_receipt_window endpoint_7_82_flag endpoint_7_82_sources 0 4 2 188169361466679648 188169361466679648 188169361466679648 endpoint_7_82_p4 endpoint_7_82_w4
def endpoint_7_82 : CertifiedEndpoint :=
  ⟨⟨7, 82, 2196⟩, 188169361466679648, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_7_82_flag endpoint_7_82_sources 6 188169361466679648 188169361466679648 rfl endpoint_7_82_base endpoint_7_82_p6) (by decide)⟩
private def endpoint_7_83_flag : Flag := ⟨7, 83, 2087⟩
private def endpoint_7_83_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_7_83_base : receiptBase endpoint_7_83_flag endpoint_7_83_sources = some 180867692877242244 := by decide +kernel
private theorem endpoint_7_83_w0 : receiptWindow endpoint_7_83_flag endpoint_7_83_sources 0 2 180867692877242244 = some 180867692877242244 := by decide +kernel
private theorem endpoint_7_83_w2 : receiptWindow endpoint_7_83_flag endpoint_7_83_sources 2 2 180867692877242244 = some 180867692877242244 := by decide +kernel
private theorem endpoint_7_83_p4 : receiptWindow endpoint_7_83_flag endpoint_7_83_sources 0 4 180867692877242244 = some 180867692877242244 :=
  join_receipt_window endpoint_7_83_flag endpoint_7_83_sources 0 2 2 180867692877242244 180867692877242244 180867692877242244 endpoint_7_83_w0 endpoint_7_83_w2
private theorem endpoint_7_83_w4 : receiptWindow endpoint_7_83_flag endpoint_7_83_sources 4 2 180867692877242244 = some 180867692877242244 := by decide +kernel
private theorem endpoint_7_83_p6 : receiptWindow endpoint_7_83_flag endpoint_7_83_sources 0 6 180867692877242244 = some 180867692877242244 :=
  join_receipt_window endpoint_7_83_flag endpoint_7_83_sources 0 4 2 180867692877242244 180867692877242244 180867692877242244 endpoint_7_83_p4 endpoint_7_83_w4
def endpoint_7_83 : CertifiedEndpoint :=
  ⟨⟨7, 83, 2087⟩, 180867692877242244, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_7_83_flag endpoint_7_83_sources 6 180867692877242244 180867692877242244 rfl endpoint_7_83_base endpoint_7_83_p6) (by decide)⟩
def endpoint_7_84 : CertifiedEndpoint :=
  ⟨⟨7, 84, 1974⟩, 259978595615312854, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_85 : CertifiedEndpoint :=
  ⟨⟨7, 85, 1859⟩, 247475513646219932, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_86 : CertifiedEndpoint :=
  ⟨⟨7, 86, 1741⟩, 234169295239452321, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_87 : CertifiedEndpoint :=
  ⟨⟨7, 87, 1619⟩, 219905034141854336, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_88 : CertifiedEndpoint :=
  ⟨⟨7, 88, 1494⟩, 204803963205764982, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_89 : CertifiedEndpoint :=
  ⟨⟨7, 89, 1366⟩, 188850929400816753, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_90 : CertifiedEndpoint :=
  ⟨⟨7, 90, 1235⟩, 172030779696642143, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_91 : CertifiedEndpoint :=
  ⟨⟨7, 91, 1100⟩, 154181873159922131, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_92 : CertifiedEndpoint :=
  ⟨⟨7, 92, 963⟩, 135580348896151407, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_93 : CertifiedEndpoint :=
  ⟨⟨7, 93, 822⟩, 115916394399018601, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_94 : CertifiedEndpoint :=
  ⟨⟨7, 94, 678⟩, 95321344541107722, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_95 : CertifiedEndpoint :=
  ⟨⟨7, 95, 531⟩, 73780046292051264, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_96 : CertifiedEndpoint :=
  ⟨⟨7, 96, 381⟩, 51277346621481721, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_97 : CertifiedEndpoint :=
  ⟨⟨7, 97, 227⟩, 27641502575835068, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_8 : CertifiedEndpoint :=
  ⟨⟨8, 8, 5176⟩, 48759738311610248, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_9 : CertifiedEndpoint :=
  ⟨⟨8, 9, 5156⟩, 51798059092858690, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_10 : CertifiedEndpoint :=
  ⟨⟨8, 10, 5135⟩, 54800610446346349, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_11 : CertifiedEndpoint :=
  ⟨⟨8, 11, 5115⟩, 64496632493400276, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_12 : CertifiedEndpoint :=
  ⟨⟨8, 12, 5094⟩, 74098489271288002, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_13 : CertifiedEndpoint :=
  ⟨⟨8, 13, 5072⟩, 83600356656899269, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_14 : CertifiedEndpoint :=
  ⟨⟨8, 14, 5051⟩, 93033313864589513, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_15 : CertifiedEndpoint :=
  ⟨⟨8, 15, 5030⟩, 102382791974366059, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_16 : CertifiedEndpoint :=
  ⟨⟨8, 16, 5008⟩, 111626456568755888, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_17 : CertifiedEndpoint :=
  ⟨⟨8, 17, 4986⟩, 120782759316491847, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_18 : CertifiedEndpoint :=
  ⟨⟨8, 18, 4964⟩, 129851700217573936, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_19 : CertifiedEndpoint :=
  ⟨⟨8, 19, 4941⟩, 138805120731418878, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_20 : CertifiedEndpoint :=
  ⟨⟨8, 20, 4919⟩, 147697396564823141, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_21 : CertifiedEndpoint :=
  ⟨⟨8, 21, 4896⟩, 156470269262250085, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_22 : CertifiedEndpoint :=
  ⟨⟨8, 22, 4873⟩, 165151897364282987, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_23 : CertifiedEndpoint :=
  ⟨⟨8, 23, 4850⟩, 173742280870921847, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_24 : CertifiedEndpoint :=
  ⟨⟨8, 24, 4827⟩, 182241419782166665, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_25 : CertifiedEndpoint :=
  ⟨⟨8, 25, 4803⟩, 190609507311213648, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_26 : CertifiedEndpoint :=
  ⟨⟨8, 26, 4779⟩, 198882467496126417, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_27 : CertifiedEndpoint :=
  ⟨⟨8, 27, 4755⟩, 207060300336904972, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_28 : CertifiedEndpoint :=
  ⟨⟨8, 28, 4730⟩, 215097374923635262, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_29 : CertifiedEndpoint :=
  ⟨⟨8, 29, 4705⟩, 223035439417491166, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_30 : CertifiedEndpoint :=
  ⟨⟨8, 30, 4680⟩, 230874493818472684, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_31 : CertifiedEndpoint :=
  ⟨⟨8, 31, 4655⟩, 238614538126579816, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_32 : CertifiedEndpoint :=
  ⟨⟨8, 32, 4629⟩, 246202175934418167, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_33 : CertifiedEndpoint :=
  ⟨⟨8, 33, 4603⟩, 253686920900641960, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_34 : CertifiedEndpoint :=
  ⟨⟨8, 34, 4577⟩, 261068773025251195, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_8_35_flag : Flag := ⟨8, 35, 4551⟩
private def endpoint_8_35_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_35_base : receiptBase endpoint_8_35_flag endpoint_8_35_sources = some 183592696235517484 := by decide +kernel
private theorem endpoint_8_35_w0 : receiptWindow endpoint_8_35_flag endpoint_8_35_sources 0 2 183592696235517484 = some 183592696235517484 := by decide +kernel
private theorem endpoint_8_35_w2 : receiptWindow endpoint_8_35_flag endpoint_8_35_sources 2 2 183592696235517484 = some 183592696235517484 := by decide +kernel
private theorem endpoint_8_35_p4 : receiptWindow endpoint_8_35_flag endpoint_8_35_sources 0 4 183592696235517484 = some 183592696235517484 :=
  join_receipt_window endpoint_8_35_flag endpoint_8_35_sources 0 2 2 183592696235517484 183592696235517484 183592696235517484 endpoint_8_35_w0 endpoint_8_35_w2
private theorem endpoint_8_35_w4 : receiptWindow endpoint_8_35_flag endpoint_8_35_sources 4 2 183592696235517484 = some 183592696235517484 := by decide +kernel
private theorem endpoint_8_35_p6 : receiptWindow endpoint_8_35_flag endpoint_8_35_sources 0 6 183592696235517484 = some 183592696235517484 :=
  join_receipt_window endpoint_8_35_flag endpoint_8_35_sources 0 4 2 183592696235517484 183592696235517484 183592696235517484 endpoint_8_35_p4 endpoint_8_35_w4
private theorem endpoint_8_35_w6 : receiptWindow endpoint_8_35_flag endpoint_8_35_sources 6 1 183592696235517484 = some 183592696235517484 := by decide +kernel
private theorem endpoint_8_35_p7 : receiptWindow endpoint_8_35_flag endpoint_8_35_sources 0 7 183592696235517484 = some 183592696235517484 :=
  join_receipt_window endpoint_8_35_flag endpoint_8_35_sources 0 6 1 183592696235517484 183592696235517484 183592696235517484 endpoint_8_35_p6 endpoint_8_35_w6
def endpoint_8_35 : CertifiedEndpoint :=
  ⟨⟨8, 35, 4551⟩, 183592696235517484, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_35_flag endpoint_8_35_sources 7 183592696235517484 183592696235517484 rfl endpoint_8_35_base endpoint_8_35_p7) (by decide)⟩
private def endpoint_8_36_flag : Flag := ⟨8, 36, 4524⟩
private def endpoint_8_36_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_36_base : receiptBase endpoint_8_36_flag endpoint_8_36_sources = some 186805762182412048 := by decide +kernel
private theorem endpoint_8_36_w0 : receiptWindow endpoint_8_36_flag endpoint_8_36_sources 0 2 186805762182412048 = some 186805762182412048 := by decide +kernel
private theorem endpoint_8_36_w2 : receiptWindow endpoint_8_36_flag endpoint_8_36_sources 2 2 186805762182412048 = some 186805762182412048 := by decide +kernel
private theorem endpoint_8_36_p4 : receiptWindow endpoint_8_36_flag endpoint_8_36_sources 0 4 186805762182412048 = some 186805762182412048 :=
  join_receipt_window endpoint_8_36_flag endpoint_8_36_sources 0 2 2 186805762182412048 186805762182412048 186805762182412048 endpoint_8_36_w0 endpoint_8_36_w2
private theorem endpoint_8_36_w4 : receiptWindow endpoint_8_36_flag endpoint_8_36_sources 4 2 186805762182412048 = some 186805762182412048 := by decide +kernel
private theorem endpoint_8_36_p6 : receiptWindow endpoint_8_36_flag endpoint_8_36_sources 0 6 186805762182412048 = some 186805762182412048 :=
  join_receipt_window endpoint_8_36_flag endpoint_8_36_sources 0 4 2 186805762182412048 186805762182412048 186805762182412048 endpoint_8_36_p4 endpoint_8_36_w4
private theorem endpoint_8_36_w6 : receiptWindow endpoint_8_36_flag endpoint_8_36_sources 6 1 186805762182412048 = some 186805762182412048 := by decide +kernel
private theorem endpoint_8_36_p7 : receiptWindow endpoint_8_36_flag endpoint_8_36_sources 0 7 186805762182412048 = some 186805762182412048 :=
  join_receipt_window endpoint_8_36_flag endpoint_8_36_sources 0 6 1 186805762182412048 186805762182412048 186805762182412048 endpoint_8_36_p6 endpoint_8_36_w6
def endpoint_8_36 : CertifiedEndpoint :=
  ⟨⟨8, 36, 4524⟩, 186805762182412048, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_36_flag endpoint_8_36_sources 7 186805762182412048 186805762182412048 rfl endpoint_8_36_base endpoint_8_36_p7) (by decide)⟩
private def endpoint_8_37_flag : Flag := ⟨8, 37, 4496⟩
private def endpoint_8_37_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_37_base : receiptBase endpoint_8_37_flag endpoint_8_37_sources = some 189925849806563732 := by decide +kernel
private theorem endpoint_8_37_w0 : receiptWindow endpoint_8_37_flag endpoint_8_37_sources 0 2 189925849806563732 = some 189925849806563732 := by decide +kernel
private theorem endpoint_8_37_w2 : receiptWindow endpoint_8_37_flag endpoint_8_37_sources 2 2 189925849806563732 = some 189925849806563732 := by decide +kernel
private theorem endpoint_8_37_p4 : receiptWindow endpoint_8_37_flag endpoint_8_37_sources 0 4 189925849806563732 = some 189925849806563732 :=
  join_receipt_window endpoint_8_37_flag endpoint_8_37_sources 0 2 2 189925849806563732 189925849806563732 189925849806563732 endpoint_8_37_w0 endpoint_8_37_w2
private theorem endpoint_8_37_w4 : receiptWindow endpoint_8_37_flag endpoint_8_37_sources 4 2 189925849806563732 = some 189925849806563732 := by decide +kernel
private theorem endpoint_8_37_p6 : receiptWindow endpoint_8_37_flag endpoint_8_37_sources 0 6 189925849806563732 = some 189925849806563732 :=
  join_receipt_window endpoint_8_37_flag endpoint_8_37_sources 0 4 2 189925849806563732 189925849806563732 189925849806563732 endpoint_8_37_p4 endpoint_8_37_w4
private theorem endpoint_8_37_w6 : receiptWindow endpoint_8_37_flag endpoint_8_37_sources 6 1 189925849806563732 = some 189925849806563732 := by decide +kernel
private theorem endpoint_8_37_p7 : receiptWindow endpoint_8_37_flag endpoint_8_37_sources 0 7 189925849806563732 = some 189925849806563732 :=
  join_receipt_window endpoint_8_37_flag endpoint_8_37_sources 0 6 1 189925849806563732 189925849806563732 189925849806563732 endpoint_8_37_p6 endpoint_8_37_w6
def endpoint_8_37 : CertifiedEndpoint :=
  ⟨⟨8, 37, 4496⟩, 189925849806563732, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_37_flag endpoint_8_37_sources 7 189925849806563732 189925849806563732 rfl endpoint_8_37_base endpoint_8_37_p7) (by decide)⟩
private def endpoint_8_38_flag : Flag := ⟨8, 38, 4468⟩
private def endpoint_8_38_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_38_base : receiptBase endpoint_8_38_flag endpoint_8_38_sources = some 192992768926963771 := by decide +kernel
private theorem endpoint_8_38_w0 : receiptWindow endpoint_8_38_flag endpoint_8_38_sources 0 2 192992768926963771 = some 192992768926963771 := by decide +kernel
private theorem endpoint_8_38_w2 : receiptWindow endpoint_8_38_flag endpoint_8_38_sources 2 2 192992768926963771 = some 192992768926963771 := by decide +kernel
private theorem endpoint_8_38_p4 : receiptWindow endpoint_8_38_flag endpoint_8_38_sources 0 4 192992768926963771 = some 192992768926963771 :=
  join_receipt_window endpoint_8_38_flag endpoint_8_38_sources 0 2 2 192992768926963771 192992768926963771 192992768926963771 endpoint_8_38_w0 endpoint_8_38_w2
private theorem endpoint_8_38_w4 : receiptWindow endpoint_8_38_flag endpoint_8_38_sources 4 2 192992768926963771 = some 192992768926963771 := by decide +kernel
private theorem endpoint_8_38_p6 : receiptWindow endpoint_8_38_flag endpoint_8_38_sources 0 6 192992768926963771 = some 192992768926963771 :=
  join_receipt_window endpoint_8_38_flag endpoint_8_38_sources 0 4 2 192992768926963771 192992768926963771 192992768926963771 endpoint_8_38_p4 endpoint_8_38_w4
private theorem endpoint_8_38_w6 : receiptWindow endpoint_8_38_flag endpoint_8_38_sources 6 1 192992768926963771 = some 192992768926963771 := by decide +kernel
private theorem endpoint_8_38_p7 : receiptWindow endpoint_8_38_flag endpoint_8_38_sources 0 7 192992768926963771 = some 192992768926963771 :=
  join_receipt_window endpoint_8_38_flag endpoint_8_38_sources 0 6 1 192992768926963771 192992768926963771 192992768926963771 endpoint_8_38_p6 endpoint_8_38_w6
def endpoint_8_38 : CertifiedEndpoint :=
  ⟨⟨8, 38, 4468⟩, 192992768926963771, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_38_flag endpoint_8_38_sources 7 192992768926963771 192992768926963771 rfl endpoint_8_38_base endpoint_8_38_p7) (by decide)⟩
private def endpoint_8_39_flag : Flag := ⟨8, 39, 4440⟩
private def endpoint_8_39_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_39_base : receiptBase endpoint_8_39_flag endpoint_8_39_sources = some 196006519543612167 := by decide +kernel
private theorem endpoint_8_39_w0 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 2 196006519543612167 = some 196006519543612167 := by decide +kernel
private theorem endpoint_8_39_w2 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 2 2 196006519543612167 = some 196006519543612167 := by decide +kernel
private theorem endpoint_8_39_p4 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 4 196006519543612167 = some 196006519543612167 :=
  join_receipt_window endpoint_8_39_flag endpoint_8_39_sources 0 2 2 196006519543612167 196006519543612167 196006519543612167 endpoint_8_39_w0 endpoint_8_39_w2
private theorem endpoint_8_39_w4 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 4 2 196006519543612167 = some 196006519543612167 := by decide +kernel
private theorem endpoint_8_39_p6 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 6 196006519543612167 = some 196006519543612167 :=
  join_receipt_window endpoint_8_39_flag endpoint_8_39_sources 0 4 2 196006519543612167 196006519543612167 196006519543612167 endpoint_8_39_p4 endpoint_8_39_w4
private theorem endpoint_8_39_w6 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 6 1 196006519543612167 = some 196006519543612167 := by decide +kernel
private theorem endpoint_8_39_p7 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 7 196006519543612167 = some 196006519543612167 :=
  join_receipt_window endpoint_8_39_flag endpoint_8_39_sources 0 6 1 196006519543612167 196006519543612167 196006519543612167 endpoint_8_39_p6 endpoint_8_39_w6
def endpoint_8_39 : CertifiedEndpoint :=
  ⟨⟨8, 39, 4440⟩, 196006519543612167, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_39_flag endpoint_8_39_sources 7 196006519543612167 196006519543612167 rfl endpoint_8_39_base endpoint_8_39_p7) (by decide)⟩
private def endpoint_8_40_flag : Flag := ⟨8, 40, 4412⟩
private def endpoint_8_40_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_40_base : receiptBase endpoint_8_40_flag endpoint_8_40_sources = some 198967101656508918 := by decide +kernel
private theorem endpoint_8_40_w0 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 2 198967101656508918 = some 198967101656508918 := by decide +kernel
private theorem endpoint_8_40_w2 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 2 2 198967101656508918 = some 198967101656508918 := by decide +kernel
private theorem endpoint_8_40_p4 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 4 198967101656508918 = some 198967101656508918 :=
  join_receipt_window endpoint_8_40_flag endpoint_8_40_sources 0 2 2 198967101656508918 198967101656508918 198967101656508918 endpoint_8_40_w0 endpoint_8_40_w2
private theorem endpoint_8_40_w4 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 4 2 198967101656508918 = some 198967101656508918 := by decide +kernel
private theorem endpoint_8_40_p6 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 6 198967101656508918 = some 198967101656508918 :=
  join_receipt_window endpoint_8_40_flag endpoint_8_40_sources 0 4 2 198967101656508918 198967101656508918 198967101656508918 endpoint_8_40_p4 endpoint_8_40_w4
private theorem endpoint_8_40_w6 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 6 1 198967101656508918 = some 198967101656508918 := by decide +kernel
private theorem endpoint_8_40_p7 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 7 198967101656508918 = some 198967101656508918 :=
  join_receipt_window endpoint_8_40_flag endpoint_8_40_sources 0 6 1 198967101656508918 198967101656508918 198967101656508918 endpoint_8_40_p6 endpoint_8_40_w6
def endpoint_8_40 : CertifiedEndpoint :=
  ⟨⟨8, 40, 4412⟩, 198967101656508918, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_40_flag endpoint_8_40_sources 7 198967101656508918 198967101656508918 rfl endpoint_8_40_base endpoint_8_40_p7) (by decide)⟩
private def endpoint_8_41_flag : Flag := ⟨8, 41, 4383⟩
private def endpoint_8_41_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_41_base : receiptBase endpoint_8_41_flag endpoint_8_41_sources = some 201829108762057353 := by decide +kernel
private theorem endpoint_8_41_w0 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 2 201829108762057353 = some 201829108762057353 := by decide +kernel
private theorem endpoint_8_41_w2 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 2 2 201829108762057353 = some 201829108762057353 := by decide +kernel
private theorem endpoint_8_41_p4 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 4 201829108762057353 = some 201829108762057353 :=
  join_receipt_window endpoint_8_41_flag endpoint_8_41_sources 0 2 2 201829108762057353 201829108762057353 201829108762057353 endpoint_8_41_w0 endpoint_8_41_w2
private theorem endpoint_8_41_w4 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 4 2 201829108762057353 = some 201829108762057353 := by decide +kernel
private theorem endpoint_8_41_p6 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 6 201829108762057353 = some 201829108762057353 :=
  join_receipt_window endpoint_8_41_flag endpoint_8_41_sources 0 4 2 201829108762057353 201829108762057353 201829108762057353 endpoint_8_41_p4 endpoint_8_41_w4
private theorem endpoint_8_41_w6 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 6 1 201829108762057353 = some 201829108762057353 := by decide +kernel
private theorem endpoint_8_41_p7 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 7 201829108762057353 = some 201829108762057353 :=
  join_receipt_window endpoint_8_41_flag endpoint_8_41_sources 0 6 1 201829108762057353 201829108762057353 201829108762057353 endpoint_8_41_p6 endpoint_8_41_w6
def endpoint_8_41 : CertifiedEndpoint :=
  ⟨⟨8, 41, 4383⟩, 201829108762057353, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_41_flag endpoint_8_41_sources 7 201829108762057353 201829108762057353 rfl endpoint_8_41_base endpoint_8_41_p7) (by decide)⟩
private def endpoint_8_42_flag : Flag := ⟨8, 42, 4353⟩
private def endpoint_8_42_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_42_base : receiptBase endpoint_8_42_flag endpoint_8_42_sources = some 204589742517954753 := by decide +kernel
private theorem endpoint_8_42_w0 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 2 204589742517954753 = some 204589742517954753 := by decide +kernel
private theorem endpoint_8_42_w2 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 2 2 204589742517954753 = some 204589742517954753 := by decide +kernel
private theorem endpoint_8_42_p4 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 4 204589742517954753 = some 204589742517954753 :=
  join_receipt_window endpoint_8_42_flag endpoint_8_42_sources 0 2 2 204589742517954753 204589742517954753 204589742517954753 endpoint_8_42_w0 endpoint_8_42_w2
private theorem endpoint_8_42_w4 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 4 2 204589742517954753 = some 204589742517954753 := by decide +kernel
private theorem endpoint_8_42_p6 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 6 204589742517954753 = some 204589742517954753 :=
  join_receipt_window endpoint_8_42_flag endpoint_8_42_sources 0 4 2 204589742517954753 204589742517954753 204589742517954753 endpoint_8_42_p4 endpoint_8_42_w4
private theorem endpoint_8_42_w6 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 6 1 204589742517954753 = some 204589742517954753 := by decide +kernel
private theorem endpoint_8_42_p7 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 7 204589742517954753 = some 204589742517954753 :=
  join_receipt_window endpoint_8_42_flag endpoint_8_42_sources 0 6 1 204589742517954753 204589742517954753 204589742517954753 endpoint_8_42_p6 endpoint_8_42_w6
def endpoint_8_42 : CertifiedEndpoint :=
  ⟨⟨8, 42, 4353⟩, 204589742517954753, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_42_flag endpoint_8_42_sources 7 204589742517954753 204589742517954753 rfl endpoint_8_42_base endpoint_8_42_p7) (by decide)⟩
private def endpoint_8_43_flag : Flag := ⟨8, 43, 4323⟩
private def endpoint_8_43_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_43_base : receiptBase endpoint_8_43_flag endpoint_8_43_sources = some 207293476647030218 := by decide +kernel
private theorem endpoint_8_43_w0 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 2 207293476647030218 = some 207293476647030218 := by decide +kernel
private theorem endpoint_8_43_w2 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 2 2 207293476647030218 = some 207293476647030218 := by decide +kernel
private theorem endpoint_8_43_p4 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 4 207293476647030218 = some 207293476647030218 :=
  join_receipt_window endpoint_8_43_flag endpoint_8_43_sources 0 2 2 207293476647030218 207293476647030218 207293476647030218 endpoint_8_43_w0 endpoint_8_43_w2
private theorem endpoint_8_43_w4 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 4 2 207293476647030218 = some 207293476647030218 := by decide +kernel
private theorem endpoint_8_43_p6 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 6 207293476647030218 = some 207293476647030218 :=
  join_receipt_window endpoint_8_43_flag endpoint_8_43_sources 0 4 2 207293476647030218 207293476647030218 207293476647030218 endpoint_8_43_p4 endpoint_8_43_w4
private theorem endpoint_8_43_w6 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 6 1 207293476647030218 = some 207293476647030218 := by decide +kernel
private theorem endpoint_8_43_p7 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 7 207293476647030218 = some 207293476647030218 :=
  join_receipt_window endpoint_8_43_flag endpoint_8_43_sources 0 6 1 207293476647030218 207293476647030218 207293476647030218 endpoint_8_43_p6 endpoint_8_43_w6
def endpoint_8_43 : CertifiedEndpoint :=
  ⟨⟨8, 43, 4323⟩, 207293476647030218, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_43_flag endpoint_8_43_sources 7 207293476647030218 207293476647030218 rfl endpoint_8_43_base endpoint_8_43_p7) (by decide)⟩
private def endpoint_8_44_flag : Flag := ⟨8, 44, 4293⟩
private def endpoint_8_44_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_44_base : receiptBase endpoint_8_44_flag endpoint_8_44_sources = some 209940311149283749 := by decide +kernel
private theorem endpoint_8_44_w0 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 2 209940311149283749 = some 209940311149283749 := by decide +kernel
private theorem endpoint_8_44_w2 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 2 2 209940311149283749 = some 209940311149283749 := by decide +kernel
private theorem endpoint_8_44_p4 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 4 209940311149283749 = some 209940311149283749 :=
  join_receipt_window endpoint_8_44_flag endpoint_8_44_sources 0 2 2 209940311149283749 209940311149283749 209940311149283749 endpoint_8_44_w0 endpoint_8_44_w2
private theorem endpoint_8_44_w4 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 4 2 209940311149283749 = some 209940311149283749 := by decide +kernel
private theorem endpoint_8_44_p6 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 6 209940311149283749 = some 209940311149283749 :=
  join_receipt_window endpoint_8_44_flag endpoint_8_44_sources 0 4 2 209940311149283749 209940311149283749 209940311149283749 endpoint_8_44_p4 endpoint_8_44_w4
private theorem endpoint_8_44_w6 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 6 1 209940311149283749 = some 209940311149283749 := by decide +kernel
private theorem endpoint_8_44_p7 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 7 209940311149283749 = some 209940311149283749 :=
  join_receipt_window endpoint_8_44_flag endpoint_8_44_sources 0 6 1 209940311149283749 209940311149283749 209940311149283749 endpoint_8_44_p6 endpoint_8_44_w6
def endpoint_8_44 : CertifiedEndpoint :=
  ⟨⟨8, 44, 4293⟩, 209940311149283749, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_44_flag endpoint_8_44_sources 7 209940311149283749 209940311149283749 rfl endpoint_8_44_base endpoint_8_44_p7) (by decide)⟩
private def endpoint_8_45_flag : Flag := ⟨8, 45, 4262⟩
private def endpoint_8_45_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_45_base : receiptBase endpoint_8_45_flag endpoint_8_45_sources = some 212481108398048381 := by decide +kernel
private theorem endpoint_8_45_w0 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 2 212481108398048381 = some 212481108398048381 := by decide +kernel
private theorem endpoint_8_45_w2 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 2 2 212481108398048381 = some 212481108398048381 := by decide +kernel
private theorem endpoint_8_45_p4 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 4 212481108398048381 = some 212481108398048381 :=
  join_receipt_window endpoint_8_45_flag endpoint_8_45_sources 0 2 2 212481108398048381 212481108398048381 212481108398048381 endpoint_8_45_w0 endpoint_8_45_w2
private theorem endpoint_8_45_w4 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 4 2 212481108398048381 = some 212481108398048381 := by decide +kernel
private theorem endpoint_8_45_p6 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 6 212481108398048381 = some 212481108398048381 :=
  join_receipt_window endpoint_8_45_flag endpoint_8_45_sources 0 4 2 212481108398048381 212481108398048381 212481108398048381 endpoint_8_45_p4 endpoint_8_45_w4
private theorem endpoint_8_45_w6 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 6 1 212481108398048381 = some 212481108398048381 := by decide +kernel
private theorem endpoint_8_45_p7 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 7 212481108398048381 = some 212481108398048381 :=
  join_receipt_window endpoint_8_45_flag endpoint_8_45_sources 0 6 1 212481108398048381 212481108398048381 212481108398048381 endpoint_8_45_p6 endpoint_8_45_w6
def endpoint_8_45 : CertifiedEndpoint :=
  ⟨⟨8, 45, 4262⟩, 212481108398048381, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_45_flag endpoint_8_45_sources 7 212481108398048381 212481108398048381 rfl endpoint_8_45_base endpoint_8_45_p7) (by decide)⟩
private def endpoint_8_46_flag : Flag := ⟨8, 46, 4230⟩
private def endpoint_8_46_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_46_base : receiptBase endpoint_8_46_flag endpoint_8_46_sources = some 214913070051021397 := by decide +kernel
private theorem endpoint_8_46_w0 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 2 214913070051021397 = some 214913070051021397 := by decide +kernel
private theorem endpoint_8_46_w2 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 2 2 214913070051021397 = some 214913070051021397 := by decide +kernel
private theorem endpoint_8_46_p4 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 4 214913070051021397 = some 214913070051021397 :=
  join_receipt_window endpoint_8_46_flag endpoint_8_46_sources 0 2 2 214913070051021397 214913070051021397 214913070051021397 endpoint_8_46_w0 endpoint_8_46_w2
private theorem endpoint_8_46_w4 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 4 2 214913070051021397 = some 214913070051021397 := by decide +kernel
private theorem endpoint_8_46_p6 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 6 214913070051021397 = some 214913070051021397 :=
  join_receipt_window endpoint_8_46_flag endpoint_8_46_sources 0 4 2 214913070051021397 214913070051021397 214913070051021397 endpoint_8_46_p4 endpoint_8_46_w4
private theorem endpoint_8_46_w6 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 6 1 214913070051021397 = some 214913070051021397 := by decide +kernel
private theorem endpoint_8_46_p7 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 7 214913070051021397 = some 214913070051021397 :=
  join_receipt_window endpoint_8_46_flag endpoint_8_46_sources 0 6 1 214913070051021397 214913070051021397 214913070051021397 endpoint_8_46_p6 endpoint_8_46_w6
def endpoint_8_46 : CertifiedEndpoint :=
  ⟨⟨8, 46, 4230⟩, 214913070051021397, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_46_flag endpoint_8_46_sources 7 214913070051021397 214913070051021397 rfl endpoint_8_46_base endpoint_8_46_p7) (by decide)⟩
private def endpoint_8_47_flag : Flag := ⟨8, 47, 4198⟩
private def endpoint_8_47_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_47_base : receiptBase endpoint_8_47_flag endpoint_8_47_sources = some 217284400954102187 := by decide +kernel
private theorem endpoint_8_47_w0 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 2 217284400954102187 = some 217284400954102187 := by decide +kernel
private theorem endpoint_8_47_w2 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 2 2 217284400954102187 = some 217284400954102187 := by decide +kernel
private theorem endpoint_8_47_p4 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 4 217284400954102187 = some 217284400954102187 :=
  join_receipt_window endpoint_8_47_flag endpoint_8_47_sources 0 2 2 217284400954102187 217284400954102187 217284400954102187 endpoint_8_47_w0 endpoint_8_47_w2
private theorem endpoint_8_47_w4 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 4 2 217284400954102187 = some 217284400954102187 := by decide +kernel
private theorem endpoint_8_47_p6 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 6 217284400954102187 = some 217284400954102187 :=
  join_receipt_window endpoint_8_47_flag endpoint_8_47_sources 0 4 2 217284400954102187 217284400954102187 217284400954102187 endpoint_8_47_p4 endpoint_8_47_w4
private theorem endpoint_8_47_w6 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 6 1 217284400954102187 = some 217284400954102187 := by decide +kernel
private theorem endpoint_8_47_p7 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 7 217284400954102187 = some 217284400954102187 :=
  join_receipt_window endpoint_8_47_flag endpoint_8_47_sources 0 6 1 217284400954102187 217284400954102187 217284400954102187 endpoint_8_47_p6 endpoint_8_47_w6
def endpoint_8_47 : CertifiedEndpoint :=
  ⟨⟨8, 47, 4198⟩, 217284400954102187, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_47_flag endpoint_8_47_sources 7 217284400954102187 217284400954102187 rfl endpoint_8_47_base endpoint_8_47_p7) (by decide)⟩
private def endpoint_8_48_flag : Flag := ⟨8, 48, 4165⟩
private def endpoint_8_48_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_48_base : receiptBase endpoint_8_48_flag endpoint_8_48_sources = some 219543165138321071 := by decide +kernel
private theorem endpoint_8_48_w0 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 2 219543165138321071 = some 219543165138321071 := by decide +kernel
private theorem endpoint_8_48_w2 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 2 2 219543165138321071 = some 219543165138321071 := by decide +kernel
private theorem endpoint_8_48_p4 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 4 219543165138321071 = some 219543165138321071 :=
  join_receipt_window endpoint_8_48_flag endpoint_8_48_sources 0 2 2 219543165138321071 219543165138321071 219543165138321071 endpoint_8_48_w0 endpoint_8_48_w2
private theorem endpoint_8_48_w4 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 4 2 219543165138321071 = some 219543165138321071 := by decide +kernel
private theorem endpoint_8_48_p6 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 6 219543165138321071 = some 219543165138321071 :=
  join_receipt_window endpoint_8_48_flag endpoint_8_48_sources 0 4 2 219543165138321071 219543165138321071 219543165138321071 endpoint_8_48_p4 endpoint_8_48_w4
private theorem endpoint_8_48_w6 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 6 1 219543165138321071 = some 219543165138321071 := by decide +kernel
private theorem endpoint_8_48_p7 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 7 219543165138321071 = some 219543165138321071 :=
  join_receipt_window endpoint_8_48_flag endpoint_8_48_sources 0 6 1 219543165138321071 219543165138321071 219543165138321071 endpoint_8_48_p6 endpoint_8_48_w6
def endpoint_8_48 : CertifiedEndpoint :=
  ⟨⟨8, 48, 4165⟩, 219543165138321071, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_48_flag endpoint_8_48_sources 7 219543165138321071 219543165138321071 rfl endpoint_8_48_base endpoint_8_48_p7) (by decide)⟩
private def endpoint_8_49_flag : Flag := ⟨8, 49, 4132⟩
private def endpoint_8_49_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_49_base : receiptBase endpoint_8_49_flag endpoint_8_49_sources = some 221739433011112583 := by decide +kernel
private theorem endpoint_8_49_w0 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 2 221739433011112583 = some 221739433011112583 := by decide +kernel
private theorem endpoint_8_49_w2 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 2 2 221739433011112583 = some 221739433011112583 := by decide +kernel
private theorem endpoint_8_49_p4 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 4 221739433011112583 = some 221739433011112583 :=
  join_receipt_window endpoint_8_49_flag endpoint_8_49_sources 0 2 2 221739433011112583 221739433011112583 221739433011112583 endpoint_8_49_w0 endpoint_8_49_w2
private theorem endpoint_8_49_w4 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 4 2 221739433011112583 = some 221739433011112583 := by decide +kernel
private theorem endpoint_8_49_p6 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 6 221739433011112583 = some 221739433011112583 :=
  join_receipt_window endpoint_8_49_flag endpoint_8_49_sources 0 4 2 221739433011112583 221739433011112583 221739433011112583 endpoint_8_49_p4 endpoint_8_49_w4
private theorem endpoint_8_49_w6 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 6 1 221739433011112583 = some 221739433011112583 := by decide +kernel
private theorem endpoint_8_49_p7 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 7 221739433011112583 = some 221739433011112583 :=
  join_receipt_window endpoint_8_49_flag endpoint_8_49_sources 0 6 1 221739433011112583 221739433011112583 221739433011112583 endpoint_8_49_p6 endpoint_8_49_w6
def endpoint_8_49 : CertifiedEndpoint :=
  ⟨⟨8, 49, 4132⟩, 221739433011112583, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_49_flag endpoint_8_49_sources 7 221739433011112583 221739433011112583 rfl endpoint_8_49_base endpoint_8_49_p7) (by decide)⟩
private def endpoint_8_50_flag : Flag := ⟨8, 50, 4098⟩
private def endpoint_8_50_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_50_base : receiptBase endpoint_8_50_flag endpoint_8_50_sources = some 223819403041971897 := by decide +kernel
private theorem endpoint_8_50_w0 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 2 223819403041971897 = some 223819403041971897 := by decide +kernel
private theorem endpoint_8_50_w2 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 2 2 223819403041971897 = some 223819403041971897 := by decide +kernel
private theorem endpoint_8_50_p4 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 4 223819403041971897 = some 223819403041971897 :=
  join_receipt_window endpoint_8_50_flag endpoint_8_50_sources 0 2 2 223819403041971897 223819403041971897 223819403041971897 endpoint_8_50_w0 endpoint_8_50_w2
private theorem endpoint_8_50_w4 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 4 2 223819403041971897 = some 223819403041971897 := by decide +kernel
private theorem endpoint_8_50_p6 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 6 223819403041971897 = some 223819403041971897 :=
  join_receipt_window endpoint_8_50_flag endpoint_8_50_sources 0 4 2 223819403041971897 223819403041971897 223819403041971897 endpoint_8_50_p4 endpoint_8_50_w4
private theorem endpoint_8_50_w6 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 6 1 223819403041971897 = some 223819403041971897 := by decide +kernel
private theorem endpoint_8_50_p7 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 7 223819403041971897 = some 223819403041971897 :=
  join_receipt_window endpoint_8_50_flag endpoint_8_50_sources 0 6 1 223819403041971897 223819403041971897 223819403041971897 endpoint_8_50_p6 endpoint_8_50_w6
def endpoint_8_50 : CertifiedEndpoint :=
  ⟨⟨8, 50, 4098⟩, 223819403041971897, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_50_flag endpoint_8_50_sources 7 223819403041971897 223819403041971897 rfl endpoint_8_50_base endpoint_8_50_p7) (by decide)⟩
private def endpoint_8_51_flag : Flag := ⟨8, 51, 4063⟩
private def endpoint_8_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_51_base : receiptBase endpoint_8_51_flag endpoint_8_51_sources = some 227063649912740777 := by decide +kernel
private theorem endpoint_8_51_w0 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 2 227063649912740777 = some 227063649912740777 := by decide +kernel
private theorem endpoint_8_51_w2 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 2 2 227063649912740777 = some 227063649912740777 := by decide +kernel
private theorem endpoint_8_51_p4 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 4 227063649912740777 = some 227063649912740777 :=
  join_receipt_window endpoint_8_51_flag endpoint_8_51_sources 0 2 2 227063649912740777 227063649912740777 227063649912740777 endpoint_8_51_w0 endpoint_8_51_w2
private theorem endpoint_8_51_w4 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 4 2 227063649912740777 = some 227063649912740777 := by decide +kernel
private theorem endpoint_8_51_p6 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 6 227063649912740777 = some 227063649912740777 :=
  join_receipt_window endpoint_8_51_flag endpoint_8_51_sources 0 4 2 227063649912740777 227063649912740777 227063649912740777 endpoint_8_51_p4 endpoint_8_51_w4
private theorem endpoint_8_51_w6 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 6 1 227063649912740777 = some 227063649912740777 := by decide +kernel
private theorem endpoint_8_51_p7 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 7 227063649912740777 = some 227063649912740777 :=
  join_receipt_window endpoint_8_51_flag endpoint_8_51_sources 0 6 1 227063649912740777 227063649912740777 227063649912740777 endpoint_8_51_p6 endpoint_8_51_w6
def endpoint_8_51 : CertifiedEndpoint :=
  ⟨⟨8, 51, 4063⟩, 227063649912740777, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_51_flag endpoint_8_51_sources 7 227063649912740777 227063649912740777 rfl endpoint_8_51_base endpoint_8_51_p7) (by decide)⟩
private def endpoint_8_52_flag : Flag := ⟨8, 52, 4027⟩
private def endpoint_8_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_52_base : receiptBase endpoint_8_52_flag endpoint_8_52_sources = some 228904399166166057 := by decide +kernel
private theorem endpoint_8_52_w0 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 2 228904399166166057 = some 228904399166166057 := by decide +kernel
private theorem endpoint_8_52_w2 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 2 2 228904399166166057 = some 228904399166166057 := by decide +kernel
private theorem endpoint_8_52_p4 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 4 228904399166166057 = some 228904399166166057 :=
  join_receipt_window endpoint_8_52_flag endpoint_8_52_sources 0 2 2 228904399166166057 228904399166166057 228904399166166057 endpoint_8_52_w0 endpoint_8_52_w2
private theorem endpoint_8_52_w4 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 4 2 228904399166166057 = some 228904399166166057 := by decide +kernel
private theorem endpoint_8_52_p6 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 6 228904399166166057 = some 228904399166166057 :=
  join_receipt_window endpoint_8_52_flag endpoint_8_52_sources 0 4 2 228904399166166057 228904399166166057 228904399166166057 endpoint_8_52_p4 endpoint_8_52_w4
private theorem endpoint_8_52_w6 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 6 1 228904399166166057 = some 228904399166166057 := by decide +kernel
private theorem endpoint_8_52_p7 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 7 228904399166166057 = some 228904399166166057 :=
  join_receipt_window endpoint_8_52_flag endpoint_8_52_sources 0 6 1 228904399166166057 228904399166166057 228904399166166057 endpoint_8_52_p6 endpoint_8_52_w6
def endpoint_8_52 : CertifiedEndpoint :=
  ⟨⟨8, 52, 4027⟩, 228904399166166057, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_52_flag endpoint_8_52_sources 7 228904399166166057 228904399166166057 rfl endpoint_8_52_base endpoint_8_52_p7) (by decide)⟩
private def endpoint_8_53_flag : Flag := ⟨8, 53, 3991⟩
private def endpoint_8_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_53_base : receiptBase endpoint_8_53_flag endpoint_8_53_sources = some 230676398259450361 := by decide +kernel
private theorem endpoint_8_53_w0 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 2 230676398259450361 = some 230676398259450361 := by decide +kernel
private theorem endpoint_8_53_w2 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 2 2 230676398259450361 = some 230676398259450361 := by decide +kernel
private theorem endpoint_8_53_p4 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 4 230676398259450361 = some 230676398259450361 :=
  join_receipt_window endpoint_8_53_flag endpoint_8_53_sources 0 2 2 230676398259450361 230676398259450361 230676398259450361 endpoint_8_53_w0 endpoint_8_53_w2
private theorem endpoint_8_53_w4 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 4 2 230676398259450361 = some 230676398259450361 := by decide +kernel
private theorem endpoint_8_53_p6 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 6 230676398259450361 = some 230676398259450361 :=
  join_receipt_window endpoint_8_53_flag endpoint_8_53_sources 0 4 2 230676398259450361 230676398259450361 230676398259450361 endpoint_8_53_p4 endpoint_8_53_w4
private theorem endpoint_8_53_w6 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 6 1 230676398259450361 = some 230676398259450361 := by decide +kernel
private theorem endpoint_8_53_p7 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 7 230676398259450361 = some 230676398259450361 :=
  join_receipt_window endpoint_8_53_flag endpoint_8_53_sources 0 6 1 230676398259450361 230676398259450361 230676398259450361 endpoint_8_53_p6 endpoint_8_53_w6
def endpoint_8_53 : CertifiedEndpoint :=
  ⟨⟨8, 53, 3991⟩, 230676398259450361, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_53_flag endpoint_8_53_sources 7 230676398259450361 230676398259450361 rfl endpoint_8_53_base endpoint_8_53_p7) (by decide)⟩
private def endpoint_8_54_flag : Flag := ⟨8, 54, 3953⟩
private def endpoint_8_54_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_54_base : receiptBase endpoint_8_54_flag endpoint_8_54_sources = some 232263531038434732 := by decide +kernel
private theorem endpoint_8_54_w0 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 2 232263531038434732 = some 232263531038434732 := by decide +kernel
private theorem endpoint_8_54_w2 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 2 2 232263531038434732 = some 232263531038434732 := by decide +kernel
private theorem endpoint_8_54_p4 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 4 232263531038434732 = some 232263531038434732 :=
  join_receipt_window endpoint_8_54_flag endpoint_8_54_sources 0 2 2 232263531038434732 232263531038434732 232263531038434732 endpoint_8_54_w0 endpoint_8_54_w2
private theorem endpoint_8_54_w4 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 4 2 232263531038434732 = some 232263531038434732 := by decide +kernel
private theorem endpoint_8_54_p6 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 6 232263531038434732 = some 232263531038434732 :=
  join_receipt_window endpoint_8_54_flag endpoint_8_54_sources 0 4 2 232263531038434732 232263531038434732 232263531038434732 endpoint_8_54_p4 endpoint_8_54_w4
private theorem endpoint_8_54_w6 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 6 1 232263531038434732 = some 232263531038434732 := by decide +kernel
private theorem endpoint_8_54_p7 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 7 232263531038434732 = some 232263531038434732 :=
  join_receipt_window endpoint_8_54_flag endpoint_8_54_sources 0 6 1 232263531038434732 232263531038434732 232263531038434732 endpoint_8_54_p6 endpoint_8_54_w6
def endpoint_8_54 : CertifiedEndpoint :=
  ⟨⟨8, 54, 3953⟩, 232263531038434732, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_54_flag endpoint_8_54_sources 7 232263531038434732 232263531038434732 rfl endpoint_8_54_base endpoint_8_54_p7) (by decide)⟩
private def endpoint_8_55_flag : Flag := ⟨8, 55, 3915⟩
private def endpoint_8_55_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_55_base : receiptBase endpoint_8_55_flag endpoint_8_55_sources = some 233778146525215607 := by decide +kernel
private theorem endpoint_8_55_w0 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 2 233778146525215607 = some 233778146525215607 := by decide +kernel
private theorem endpoint_8_55_w2 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 2 2 233778146525215607 = some 233778146525215607 := by decide +kernel
private theorem endpoint_8_55_p4 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 4 233778146525215607 = some 233778146525215607 :=
  join_receipt_window endpoint_8_55_flag endpoint_8_55_sources 0 2 2 233778146525215607 233778146525215607 233778146525215607 endpoint_8_55_w0 endpoint_8_55_w2
private theorem endpoint_8_55_w4 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 4 2 233778146525215607 = some 233778146525215607 := by decide +kernel
private theorem endpoint_8_55_p6 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 6 233778146525215607 = some 233778146525215607 :=
  join_receipt_window endpoint_8_55_flag endpoint_8_55_sources 0 4 2 233778146525215607 233778146525215607 233778146525215607 endpoint_8_55_p4 endpoint_8_55_w4
private theorem endpoint_8_55_w6 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 6 1 233778146525215607 = some 233778146525215607 := by decide +kernel
private theorem endpoint_8_55_p7 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 7 233778146525215607 = some 233778146525215607 :=
  join_receipt_window endpoint_8_55_flag endpoint_8_55_sources 0 6 1 233778146525215607 233778146525215607 233778146525215607 endpoint_8_55_p6 endpoint_8_55_w6
def endpoint_8_55 : CertifiedEndpoint :=
  ⟨⟨8, 55, 3915⟩, 233778146525215607, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_55_flag endpoint_8_55_sources 7 233778146525215607 233778146525215607 rfl endpoint_8_55_base endpoint_8_55_p7) (by decide)⟩
private def endpoint_8_56_flag : Flag := ⟨8, 56, 3875⟩
private def endpoint_8_56_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_56_base : receiptBase endpoint_8_56_flag endpoint_8_56_sources = some 235925286721154692 := by decide +kernel
private theorem endpoint_8_56_w0 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 2 235925286721154692 = some 235925286721154692 := by decide +kernel
private theorem endpoint_8_56_w2 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 2 2 235925286721154692 = some 235925286721154692 := by decide +kernel
private theorem endpoint_8_56_p4 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 4 235925286721154692 = some 235925286721154692 :=
  join_receipt_window endpoint_8_56_flag endpoint_8_56_sources 0 2 2 235925286721154692 235925286721154692 235925286721154692 endpoint_8_56_w0 endpoint_8_56_w2
private theorem endpoint_8_56_w4 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 4 2 235925286721154692 = some 235925286721154692 := by decide +kernel
private theorem endpoint_8_56_p6 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 6 235925286721154692 = some 235925286721154692 :=
  join_receipt_window endpoint_8_56_flag endpoint_8_56_sources 0 4 2 235925286721154692 235925286721154692 235925286721154692 endpoint_8_56_p4 endpoint_8_56_w4
private theorem endpoint_8_56_w6 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 6 1 235925286721154692 = some 235925286721154692 := by decide +kernel
private theorem endpoint_8_56_p7 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 7 235925286721154692 = some 235925286721154692 :=
  join_receipt_window endpoint_8_56_flag endpoint_8_56_sources 0 6 1 235925286721154692 235925286721154692 235925286721154692 endpoint_8_56_p6 endpoint_8_56_w6
def endpoint_8_56 : CertifiedEndpoint :=
  ⟨⟨8, 56, 3875⟩, 235925286721154692, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_56_flag endpoint_8_56_sources 7 235925286721154692 235925286721154692 rfl endpoint_8_56_base endpoint_8_56_p7) (by decide)⟩
private def endpoint_8_57_flag : Flag := ⟨8, 57, 3834⟩
private def endpoint_8_57_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_57_base : receiptBase endpoint_8_57_flag endpoint_8_57_sources = some 237101260427901459 := by decide +kernel
private theorem endpoint_8_57_w0 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 2 237101260427901459 = some 237101260427901459 := by decide +kernel
private theorem endpoint_8_57_w2 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 2 2 237101260427901459 = some 237101260427901459 := by decide +kernel
private theorem endpoint_8_57_p4 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 4 237101260427901459 = some 237101260427901459 :=
  join_receipt_window endpoint_8_57_flag endpoint_8_57_sources 0 2 2 237101260427901459 237101260427901459 237101260427901459 endpoint_8_57_w0 endpoint_8_57_w2
private theorem endpoint_8_57_w4 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 4 2 237101260427901459 = some 237101260427901459 := by decide +kernel
private theorem endpoint_8_57_p6 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 6 237101260427901459 = some 237101260427901459 :=
  join_receipt_window endpoint_8_57_flag endpoint_8_57_sources 0 4 2 237101260427901459 237101260427901459 237101260427901459 endpoint_8_57_p4 endpoint_8_57_w4
private theorem endpoint_8_57_w6 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 6 1 237101260427901459 = some 237101260427901459 := by decide +kernel
private theorem endpoint_8_57_p7 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 7 237101260427901459 = some 237101260427901459 :=
  join_receipt_window endpoint_8_57_flag endpoint_8_57_sources 0 6 1 237101260427901459 237101260427901459 237101260427901459 endpoint_8_57_p6 endpoint_8_57_w6
def endpoint_8_57 : CertifiedEndpoint :=
  ⟨⟨8, 57, 3834⟩, 237101260427901459, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_57_flag endpoint_8_57_sources 7 237101260427901459 237101260427901459 rfl endpoint_8_57_base endpoint_8_57_p7) (by decide)⟩
private def endpoint_8_58_flag : Flag := ⟨8, 58, 3793⟩
private def endpoint_8_58_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_58_base : receiptBase endpoint_8_58_flag endpoint_8_58_sources = some 238199066144350951 := by decide +kernel
private theorem endpoint_8_58_w0 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 2 238199066144350951 = some 238199066144350951 := by decide +kernel
private theorem endpoint_8_58_w2 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 2 2 238199066144350951 = some 238199066144350951 := by decide +kernel
private theorem endpoint_8_58_p4 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 4 238199066144350951 = some 238199066144350951 :=
  join_receipt_window endpoint_8_58_flag endpoint_8_58_sources 0 2 2 238199066144350951 238199066144350951 238199066144350951 endpoint_8_58_w0 endpoint_8_58_w2
private theorem endpoint_8_58_w4 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 4 2 238199066144350951 = some 238199066144350951 := by decide +kernel
private theorem endpoint_8_58_p6 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 6 238199066144350951 = some 238199066144350951 :=
  join_receipt_window endpoint_8_58_flag endpoint_8_58_sources 0 4 2 238199066144350951 238199066144350951 238199066144350951 endpoint_8_58_p4 endpoint_8_58_w4
private theorem endpoint_8_58_w6 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 6 1 238199066144350951 = some 238199066144350951 := by decide +kernel
private theorem endpoint_8_58_p7 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 7 238199066144350951 = some 238199066144350951 :=
  join_receipt_window endpoint_8_58_flag endpoint_8_58_sources 0 6 1 238199066144350951 238199066144350951 238199066144350951 endpoint_8_58_p6 endpoint_8_58_w6
def endpoint_8_58 : CertifiedEndpoint :=
  ⟨⟨8, 58, 3793⟩, 238199066144350951, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_58_flag endpoint_8_58_sources 7 238199066144350951 238199066144350951 rfl endpoint_8_58_base endpoint_8_58_p7) (by decide)⟩
private def endpoint_8_59_flag : Flag := ⟨8, 59, 3749⟩
private def endpoint_8_59_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_59_base : receiptBase endpoint_8_59_flag endpoint_8_59_sources = some 239029754848374574 := by decide +kernel
private theorem endpoint_8_59_w0 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 2 239029754848374574 = some 239029754848374574 := by decide +kernel
private theorem endpoint_8_59_w2 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 2 2 239029754848374574 = some 239029754848374574 := by decide +kernel
private theorem endpoint_8_59_p4 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 4 239029754848374574 = some 239029754848374574 :=
  join_receipt_window endpoint_8_59_flag endpoint_8_59_sources 0 2 2 239029754848374574 239029754848374574 239029754848374574 endpoint_8_59_w0 endpoint_8_59_w2
private theorem endpoint_8_59_w4 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 4 2 239029754848374574 = some 239029754848374574 := by decide +kernel
private theorem endpoint_8_59_p6 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 6 239029754848374574 = some 239029754848374574 :=
  join_receipt_window endpoint_8_59_flag endpoint_8_59_sources 0 4 2 239029754848374574 239029754848374574 239029754848374574 endpoint_8_59_p4 endpoint_8_59_w4
private theorem endpoint_8_59_w6 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 6 1 239029754848374574 = some 239029754848374574 := by decide +kernel
private theorem endpoint_8_59_p7 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 7 239029754848374574 = some 239029754848374574 :=
  join_receipt_window endpoint_8_59_flag endpoint_8_59_sources 0 6 1 239029754848374574 239029754848374574 239029754848374574 endpoint_8_59_p6 endpoint_8_59_w6
def endpoint_8_59 : CertifiedEndpoint :=
  ⟨⟨8, 59, 3749⟩, 239029754848374574, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_59_flag endpoint_8_59_sources 7 239029754848374574 239029754848374574 rfl endpoint_8_59_base endpoint_8_59_p7) (by decide)⟩
private def endpoint_8_60_flag : Flag := ⟨8, 60, 3705⟩
private def endpoint_8_60_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_60_base : receiptBase endpoint_8_60_flag endpoint_8_60_sources = some 239776624864007142 := by decide +kernel
private theorem endpoint_8_60_w0 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 2 239776624864007142 = some 239776624864007142 := by decide +kernel
private theorem endpoint_8_60_w2 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 2 2 239776624864007142 = some 239776624864007142 := by decide +kernel
private theorem endpoint_8_60_p4 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 4 239776624864007142 = some 239776624864007142 :=
  join_receipt_window endpoint_8_60_flag endpoint_8_60_sources 0 2 2 239776624864007142 239776624864007142 239776624864007142 endpoint_8_60_w0 endpoint_8_60_w2
private theorem endpoint_8_60_w4 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 4 2 239776624864007142 = some 239776624864007142 := by decide +kernel
private theorem endpoint_8_60_p6 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 6 239776624864007142 = some 239776624864007142 :=
  join_receipt_window endpoint_8_60_flag endpoint_8_60_sources 0 4 2 239776624864007142 239776624864007142 239776624864007142 endpoint_8_60_p4 endpoint_8_60_w4
private theorem endpoint_8_60_w6 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 6 1 239776624864007142 = some 239776624864007142 := by decide +kernel
private theorem endpoint_8_60_p7 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 7 239776624864007142 = some 239776624864007142 :=
  join_receipt_window endpoint_8_60_flag endpoint_8_60_sources 0 6 1 239776624864007142 239776624864007142 239776624864007142 endpoint_8_60_p6 endpoint_8_60_w6
def endpoint_8_60 : CertifiedEndpoint :=
  ⟨⟨8, 60, 3705⟩, 239776624864007142, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_60_flag endpoint_8_60_sources 7 239776624864007142 239776624864007142 rfl endpoint_8_60_base endpoint_8_60_p7) (by decide)⟩
private def endpoint_8_61_flag : Flag := ⟨8, 61, 3658⟩
private def endpoint_8_61_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_61_base : receiptBase endpoint_8_61_flag endpoint_8_61_sources = some 242704270898400109 := by decide +kernel
private theorem endpoint_8_61_w0 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 2 242704270898400109 = some 242704270898400109 := by decide +kernel
private theorem endpoint_8_61_w2 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 2 2 242704270898400109 = some 242704270898400109 := by decide +kernel
private theorem endpoint_8_61_p4 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 4 242704270898400109 = some 242704270898400109 :=
  join_receipt_window endpoint_8_61_flag endpoint_8_61_sources 0 2 2 242704270898400109 242704270898400109 242704270898400109 endpoint_8_61_w0 endpoint_8_61_w2
private theorem endpoint_8_61_w4 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 4 2 242704270898400109 = some 242704270898400109 := by decide +kernel
private theorem endpoint_8_61_p6 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 6 242704270898400109 = some 242704270898400109 :=
  join_receipt_window endpoint_8_61_flag endpoint_8_61_sources 0 4 2 242704270898400109 242704270898400109 242704270898400109 endpoint_8_61_p4 endpoint_8_61_w4
private theorem endpoint_8_61_w6 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 6 1 242704270898400109 = some 242704270898400109 := by decide +kernel
private theorem endpoint_8_61_p7 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 7 242704270898400109 = some 242704270898400109 :=
  join_receipt_window endpoint_8_61_flag endpoint_8_61_sources 0 6 1 242704270898400109 242704270898400109 242704270898400109 endpoint_8_61_p6 endpoint_8_61_w6
def endpoint_8_61 : CertifiedEndpoint :=
  ⟨⟨8, 61, 3658⟩, 242704270898400109, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_61_flag endpoint_8_61_sources 7 242704270898400109 242704270898400109 rfl endpoint_8_61_base endpoint_8_61_p7) (by decide)⟩
private def endpoint_8_62_flag : Flag := ⟨8, 62, 3610⟩
private def endpoint_8_62_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_62_base : receiptBase endpoint_8_62_flag endpoint_8_62_sources = some 242998470927878298 := by decide +kernel
private theorem endpoint_8_62_w0 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 2 242998470927878298 = some 242998470927878298 := by decide +kernel
private theorem endpoint_8_62_w2 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 2 2 242998470927878298 = some 242998470927878298 := by decide +kernel
private theorem endpoint_8_62_p4 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 4 242998470927878298 = some 242998470927878298 :=
  join_receipt_window endpoint_8_62_flag endpoint_8_62_sources 0 2 2 242998470927878298 242998470927878298 242998470927878298 endpoint_8_62_w0 endpoint_8_62_w2
private theorem endpoint_8_62_w4 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 4 2 242998470927878298 = some 242998470927878298 := by decide +kernel
private theorem endpoint_8_62_p6 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 6 242998470927878298 = some 242998470927878298 :=
  join_receipt_window endpoint_8_62_flag endpoint_8_62_sources 0 4 2 242998470927878298 242998470927878298 242998470927878298 endpoint_8_62_p4 endpoint_8_62_w4
private theorem endpoint_8_62_w6 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 6 1 242998470927878298 = some 242998470927878298 := by decide +kernel
private theorem endpoint_8_62_p7 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 7 242998470927878298 = some 242998470927878298 :=
  join_receipt_window endpoint_8_62_flag endpoint_8_62_sources 0 6 1 242998470927878298 242998470927878298 242998470927878298 endpoint_8_62_p6 endpoint_8_62_w6
def endpoint_8_62 : CertifiedEndpoint :=
  ⟨⟨8, 62, 3610⟩, 242998470927878298, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_62_flag endpoint_8_62_sources 7 242998470927878298 242998470927878298 rfl endpoint_8_62_base endpoint_8_62_p7) (by decide)⟩
private def endpoint_8_63_flag : Flag := ⟨8, 63, 3559⟩
private def endpoint_8_63_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_63_base : receiptBase endpoint_8_63_flag endpoint_8_63_sources = some 242997616412512358 := by decide +kernel
private theorem endpoint_8_63_w0 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 2 242997616412512358 = some 242997616412512358 := by decide +kernel
private theorem endpoint_8_63_w2 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 2 2 242997616412512358 = some 242997616412512358 := by decide +kernel
private theorem endpoint_8_63_p4 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 4 242997616412512358 = some 242997616412512358 :=
  join_receipt_window endpoint_8_63_flag endpoint_8_63_sources 0 2 2 242997616412512358 242997616412512358 242997616412512358 endpoint_8_63_w0 endpoint_8_63_w2
private theorem endpoint_8_63_w4 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 4 2 242997616412512358 = some 242997616412512358 := by decide +kernel
private theorem endpoint_8_63_p6 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 6 242997616412512358 = some 242997616412512358 :=
  join_receipt_window endpoint_8_63_flag endpoint_8_63_sources 0 4 2 242997616412512358 242997616412512358 242997616412512358 endpoint_8_63_p4 endpoint_8_63_w4
private theorem endpoint_8_63_w6 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 6 1 242997616412512358 = some 242997616412512358 := by decide +kernel
private theorem endpoint_8_63_p7 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 7 242997616412512358 = some 242997616412512358 :=
  join_receipt_window endpoint_8_63_flag endpoint_8_63_sources 0 6 1 242997616412512358 242997616412512358 242997616412512358 endpoint_8_63_p6 endpoint_8_63_w6
def endpoint_8_63 : CertifiedEndpoint :=
  ⟨⟨8, 63, 3559⟩, 242997616412512358, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_63_flag endpoint_8_63_sources 7 242997616412512358 242997616412512358 rfl endpoint_8_63_base endpoint_8_63_p7) (by decide)⟩
private def endpoint_8_64_flag : Flag := ⟨8, 64, 3506⟩
private def endpoint_8_64_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_64_base : receiptBase endpoint_8_64_flag endpoint_8_64_sources = some 242761710803982258 := by decide +kernel
private theorem endpoint_8_64_w0 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 2 242761710803982258 = some 242761710803982258 := by decide +kernel
private theorem endpoint_8_64_w2 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 2 2 242761710803982258 = some 242761710803982258 := by decide +kernel
private theorem endpoint_8_64_p4 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 4 242761710803982258 = some 242761710803982258 :=
  join_receipt_window endpoint_8_64_flag endpoint_8_64_sources 0 2 2 242761710803982258 242761710803982258 242761710803982258 endpoint_8_64_w0 endpoint_8_64_w2
private theorem endpoint_8_64_w4 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 4 2 242761710803982258 = some 242761710803982258 := by decide +kernel
private theorem endpoint_8_64_p6 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 6 242761710803982258 = some 242761710803982258 :=
  join_receipt_window endpoint_8_64_flag endpoint_8_64_sources 0 4 2 242761710803982258 242761710803982258 242761710803982258 endpoint_8_64_p4 endpoint_8_64_w4
private theorem endpoint_8_64_w6 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 6 1 242761710803982258 = some 242761710803982258 := by decide +kernel
private theorem endpoint_8_64_p7 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 7 242761710803982258 = some 242761710803982258 :=
  join_receipt_window endpoint_8_64_flag endpoint_8_64_sources 0 6 1 242761710803982258 242761710803982258 242761710803982258 endpoint_8_64_p6 endpoint_8_64_w6
def endpoint_8_64 : CertifiedEndpoint :=
  ⟨⟨8, 64, 3506⟩, 242761710803982258, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_64_flag endpoint_8_64_sources 7 242761710803982258 242761710803982258 rfl endpoint_8_64_base endpoint_8_64_p7) (by decide)⟩
private def endpoint_8_65_flag : Flag := ⟨8, 65, 3451⟩
private def endpoint_8_65_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_8_65_base : receiptBase endpoint_8_65_flag endpoint_8_65_sources = some 243855351142973612 := by decide +kernel
private theorem endpoint_8_65_w0 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 2 243855351142973612 = some 243855351142973612 := by decide +kernel
private theorem endpoint_8_65_w2 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 2 2 243855351142973612 = some 243855351142973612 := by decide +kernel
private theorem endpoint_8_65_p4 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 4 243855351142973612 = some 243855351142973612 :=
  join_receipt_window endpoint_8_65_flag endpoint_8_65_sources 0 2 2 243855351142973612 243855351142973612 243855351142973612 endpoint_8_65_w0 endpoint_8_65_w2
private theorem endpoint_8_65_w4 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 4 2 243855351142973612 = some 243855351142973612 := by decide +kernel
private theorem endpoint_8_65_p6 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 6 243855351142973612 = some 243855351142973612 :=
  join_receipt_window endpoint_8_65_flag endpoint_8_65_sources 0 4 2 243855351142973612 243855351142973612 243855351142973612 endpoint_8_65_p4 endpoint_8_65_w4
private theorem endpoint_8_65_w6 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 6 1 243855351142973612 = some 243855351142973612 := by decide +kernel
private theorem endpoint_8_65_p7 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 7 243855351142973612 = some 243855351142973612 :=
  join_receipt_window endpoint_8_65_flag endpoint_8_65_sources 0 6 1 243855351142973612 243855351142973612 243855351142973612 endpoint_8_65_p6 endpoint_8_65_w6
def endpoint_8_65 : CertifiedEndpoint :=
  ⟨⟨8, 65, 3451⟩, 243855351142973612, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_8_65_flag endpoint_8_65_sources 7 243855351142973612 243855351142973612 rfl endpoint_8_65_base endpoint_8_65_p7) (by decide)⟩
private def endpoint_8_66_flag : Flag := ⟨8, 66, 3392⟩
private def endpoint_8_66_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_8_66_base : receiptBase endpoint_8_66_flag endpoint_8_66_sources = some 242988145158639169 := by decide +kernel
private theorem endpoint_8_66_w0 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 2 242988145158639169 = some 242988145158639169 := by decide +kernel
private theorem endpoint_8_66_w2 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 2 2 242988145158639169 = some 242988145158639169 := by decide +kernel
private theorem endpoint_8_66_p4 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 4 242988145158639169 = some 242988145158639169 :=
  join_receipt_window endpoint_8_66_flag endpoint_8_66_sources 0 2 2 242988145158639169 242988145158639169 242988145158639169 endpoint_8_66_w0 endpoint_8_66_w2
private theorem endpoint_8_66_w4 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 4 2 242988145158639169 = some 242988145158639169 := by decide +kernel
private theorem endpoint_8_66_p6 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 6 242988145158639169 = some 242988145158639169 :=
  join_receipt_window endpoint_8_66_flag endpoint_8_66_sources 0 4 2 242988145158639169 242988145158639169 242988145158639169 endpoint_8_66_p4 endpoint_8_66_w4
private theorem endpoint_8_66_w6 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 6 1 242988145158639169 = some 242988145158639169 := by decide +kernel
private theorem endpoint_8_66_p7 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 7 242988145158639169 = some 242988145158639169 :=
  join_receipt_window endpoint_8_66_flag endpoint_8_66_sources 0 6 1 242988145158639169 242988145158639169 242988145158639169 endpoint_8_66_p6 endpoint_8_66_w6
def endpoint_8_66 : CertifiedEndpoint :=
  ⟨⟨8, 66, 3392⟩, 242988145158639169, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_8_66_flag endpoint_8_66_sources 7 242988145158639169 242988145158639169 rfl endpoint_8_66_base endpoint_8_66_p7) (by decide)⟩
private def endpoint_8_67_flag : Flag := ⟨8, 67, 3331⟩
private def endpoint_8_67_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_8_67_base : receiptBase endpoint_8_67_flag endpoint_8_67_sources = some 241862844327649923 := by decide +kernel
private theorem endpoint_8_67_w0 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 2 241862844327649923 = some 241862844327649923 := by decide +kernel
private theorem endpoint_8_67_w2 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 2 2 241862844327649923 = some 241862844327649923 := by decide +kernel
private theorem endpoint_8_67_p4 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 4 241862844327649923 = some 241862844327649923 :=
  join_receipt_window endpoint_8_67_flag endpoint_8_67_sources 0 2 2 241862844327649923 241862844327649923 241862844327649923 endpoint_8_67_w0 endpoint_8_67_w2
private theorem endpoint_8_67_w4 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 4 2 241862844327649923 = some 241862844327649923 := by decide +kernel
private theorem endpoint_8_67_p6 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 6 241862844327649923 = some 241862844327649923 :=
  join_receipt_window endpoint_8_67_flag endpoint_8_67_sources 0 4 2 241862844327649923 241862844327649923 241862844327649923 endpoint_8_67_p4 endpoint_8_67_w4
private theorem endpoint_8_67_w6 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 6 1 241862844327649923 = some 241862844327649923 := by decide +kernel
private theorem endpoint_8_67_p7 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 7 241862844327649923 = some 241862844327649923 :=
  join_receipt_window endpoint_8_67_flag endpoint_8_67_sources 0 6 1 241862844327649923 241862844327649923 241862844327649923 endpoint_8_67_p6 endpoint_8_67_w6
def endpoint_8_67 : CertifiedEndpoint :=
  ⟨⟨8, 67, 3331⟩, 241862844327649923, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_8_67_flag endpoint_8_67_sources 7 241862844327649923 241862844327649923 rfl endpoint_8_67_base endpoint_8_67_p7) (by decide)⟩

def endpointBlock05 : List CertifiedEndpoint := [
  endpoint_7_34, endpoint_7_35, endpoint_7_36, endpoint_7_37, endpoint_7_38, endpoint_7_39, endpoint_7_40,
  endpoint_7_41, endpoint_7_42, endpoint_7_43, endpoint_7_44, endpoint_7_45, endpoint_7_46, endpoint_7_47,
  endpoint_7_48, endpoint_7_49, endpoint_7_50, endpoint_7_51, endpoint_7_52, endpoint_7_53, endpoint_7_54,
  endpoint_7_55, endpoint_7_56, endpoint_7_57, endpoint_7_58, endpoint_7_59, endpoint_7_60, endpoint_7_61,
  endpoint_7_62, endpoint_7_63, endpoint_7_64, endpoint_7_65, endpoint_7_66, endpoint_7_67, endpoint_7_68,
  endpoint_7_69, endpoint_7_70, endpoint_7_71, endpoint_7_72, endpoint_7_73, endpoint_7_74, endpoint_7_75,
  endpoint_7_76, endpoint_7_77, endpoint_7_78, endpoint_7_79, endpoint_7_80, endpoint_7_81, endpoint_7_82,
  endpoint_7_83, endpoint_7_84, endpoint_7_85, endpoint_7_86, endpoint_7_87, endpoint_7_88, endpoint_7_89,
  endpoint_7_90, endpoint_7_91, endpoint_7_92, endpoint_7_93, endpoint_7_94, endpoint_7_95, endpoint_7_96,
  endpoint_7_97, endpoint_8_8, endpoint_8_9, endpoint_8_10, endpoint_8_11, endpoint_8_12, endpoint_8_13,
  endpoint_8_14, endpoint_8_15, endpoint_8_16, endpoint_8_17, endpoint_8_18, endpoint_8_19, endpoint_8_20,
  endpoint_8_21, endpoint_8_22, endpoint_8_23, endpoint_8_24, endpoint_8_25, endpoint_8_26, endpoint_8_27,
  endpoint_8_28, endpoint_8_29, endpoint_8_30, endpoint_8_31, endpoint_8_32, endpoint_8_33, endpoint_8_34,
  endpoint_8_35, endpoint_8_36, endpoint_8_37, endpoint_8_38, endpoint_8_39, endpoint_8_40, endpoint_8_41,
  endpoint_8_42, endpoint_8_43, endpoint_8_44, endpoint_8_45, endpoint_8_46, endpoint_8_47, endpoint_8_48,
  endpoint_8_49, endpoint_8_50, endpoint_8_51, endpoint_8_52, endpoint_8_53, endpoint_8_54, endpoint_8_55,
  endpoint_8_56, endpoint_8_57, endpoint_8_58, endpoint_8_59, endpoint_8_60, endpoint_8_61, endpoint_8_62,
  endpoint_8_63, endpoint_8_64, endpoint_8_65, endpoint_8_66, endpoint_8_67
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
