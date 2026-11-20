import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def endpoint_7_27 : CertifiedEndpoint :=
  ⟨⟨7, 27, 4767⟩, 184043025939353428, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_28 : CertifiedEndpoint :=
  ⟨⟨7, 28, 4743⟩, 191052779528790819, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_29 : CertifiedEndpoint :=
  ⟨⟨7, 29, 4718⟩, 197937932925807537, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_30 : CertifiedEndpoint :=
  ⟨⟨7, 30, 4693⟩, 204737219150741721, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_31 : CertifiedEndpoint :=
  ⟨⟨7, 31, 4668⟩, 211450638203593371, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_32 : CertifiedEndpoint :=
  ⟨⟨7, 32, 4643⟩, 218078190084362487, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_33 : CertifiedEndpoint :=
  ⟨⟨7, 33, 4617⟩, 224571039752465926, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_34 : CertifiedEndpoint :=
  ⟨⟨7, 34, 4591⟩, 230974654908405163, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_35 : CertifiedEndpoint :=
  ⟨⟨7, 35, 4564⟩, 237236833171515387, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_36 : CertifiedEndpoint :=
  ⟨⟨7, 36, 4537⟩, 243406409582379741, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_37 : CertifiedEndpoint :=
  ⟨⟨7, 37, 4510⟩, 249483384140998225, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_38 : CertifiedEndpoint :=
  ⟨⟨7, 38, 4483⟩, 255467756847370839, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_39 : CertifiedEndpoint :=
  ⟨⟨7, 39, 4455⟩, 261300590640669436, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_7_40_flag : Flag := ⟨7, 40, 4426⟩
private def endpoint_7_40_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_40_base : receiptBase endpoint_7_40_flag endpoint_7_40_sources = some 183751431436769938 := by decide +kernel
private theorem endpoint_7_40_w0 : receiptWindow endpoint_7_40_flag endpoint_7_40_sources 0 2 183751431436769938 = some 183751431436769938 := by decide +kernel
private theorem endpoint_7_40_w2 : receiptWindow endpoint_7_40_flag endpoint_7_40_sources 2 2 183751431436769938 = some 183751431436769938 := by decide +kernel
private theorem endpoint_7_40_p4 : receiptWindow endpoint_7_40_flag endpoint_7_40_sources 0 4 183751431436769938 = some 183751431436769938 :=
  join_receipt_window endpoint_7_40_flag endpoint_7_40_sources 0 2 2 183751431436769938 183751431436769938 183751431436769938 endpoint_7_40_w0 endpoint_7_40_w2
private theorem endpoint_7_40_w4 : receiptWindow endpoint_7_40_flag endpoint_7_40_sources 4 2 183751431436769938 = some 183751431436769938 := by decide +kernel
private theorem endpoint_7_40_p6 : receiptWindow endpoint_7_40_flag endpoint_7_40_sources 0 6 183751431436769938 = some 183751431436769938 :=
  join_receipt_window endpoint_7_40_flag endpoint_7_40_sources 0 4 2 183751431436769938 183751431436769938 183751431436769938 endpoint_7_40_p4 endpoint_7_40_w4
def endpoint_7_40 : CertifiedEndpoint :=
  ⟨⟨7, 40, 4426⟩, 183751431436769938, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_40_flag endpoint_7_40_sources 6 183751431436769938 183751431436769938 rfl endpoint_7_40_base endpoint_7_40_p6) (by decide)⟩
private def endpoint_7_41_flag : Flag := ⟨7, 41, 4398⟩
private def endpoint_7_41_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_41_base : receiptBase endpoint_7_41_flag endpoint_7_41_sources = some 186456575197519815 := by decide +kernel
private theorem endpoint_7_41_w0 : receiptWindow endpoint_7_41_flag endpoint_7_41_sources 0 2 186456575197519815 = some 186456575197519815 := by decide +kernel
private theorem endpoint_7_41_w2 : receiptWindow endpoint_7_41_flag endpoint_7_41_sources 2 2 186456575197519815 = some 186456575197519815 := by decide +kernel
private theorem endpoint_7_41_p4 : receiptWindow endpoint_7_41_flag endpoint_7_41_sources 0 4 186456575197519815 = some 186456575197519815 :=
  join_receipt_window endpoint_7_41_flag endpoint_7_41_sources 0 2 2 186456575197519815 186456575197519815 186456575197519815 endpoint_7_41_w0 endpoint_7_41_w2
private theorem endpoint_7_41_w4 : receiptWindow endpoint_7_41_flag endpoint_7_41_sources 4 2 186456575197519815 = some 186456575197519815 := by decide +kernel
private theorem endpoint_7_41_p6 : receiptWindow endpoint_7_41_flag endpoint_7_41_sources 0 6 186456575197519815 = some 186456575197519815 :=
  join_receipt_window endpoint_7_41_flag endpoint_7_41_sources 0 4 2 186456575197519815 186456575197519815 186456575197519815 endpoint_7_41_p4 endpoint_7_41_w4
def endpoint_7_41 : CertifiedEndpoint :=
  ⟨⟨7, 41, 4398⟩, 186456575197519815, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_41_flag endpoint_7_41_sources 6 186456575197519815 186456575197519815 rfl endpoint_7_41_base endpoint_7_41_p6) (by decide)⟩
private def endpoint_7_42_flag : Flag := ⟨7, 42, 4368⟩
private def endpoint_7_42_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_42_base : receiptBase endpoint_7_42_flag endpoint_7_42_sources = some 189027054167464317 := by decide +kernel
private theorem endpoint_7_42_w0 : receiptWindow endpoint_7_42_flag endpoint_7_42_sources 0 2 189027054167464317 = some 189027054167464317 := by decide +kernel
private theorem endpoint_7_42_w2 : receiptWindow endpoint_7_42_flag endpoint_7_42_sources 2 2 189027054167464317 = some 189027054167464317 := by decide +kernel
private theorem endpoint_7_42_p4 : receiptWindow endpoint_7_42_flag endpoint_7_42_sources 0 4 189027054167464317 = some 189027054167464317 :=
  join_receipt_window endpoint_7_42_flag endpoint_7_42_sources 0 2 2 189027054167464317 189027054167464317 189027054167464317 endpoint_7_42_w0 endpoint_7_42_w2
private theorem endpoint_7_42_w4 : receiptWindow endpoint_7_42_flag endpoint_7_42_sources 4 2 189027054167464317 = some 189027054167464317 := by decide +kernel
private theorem endpoint_7_42_p6 : receiptWindow endpoint_7_42_flag endpoint_7_42_sources 0 6 189027054167464317 = some 189027054167464317 :=
  join_receipt_window endpoint_7_42_flag endpoint_7_42_sources 0 4 2 189027054167464317 189027054167464317 189027054167464317 endpoint_7_42_p4 endpoint_7_42_w4
def endpoint_7_42 : CertifiedEndpoint :=
  ⟨⟨7, 42, 4368⟩, 189027054167464317, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_42_flag endpoint_7_42_sources 6 189027054167464317 189027054167464317 rfl endpoint_7_42_base endpoint_7_42_p6) (by decide)⟩
private def endpoint_7_43_flag : Flag := ⟨7, 43, 4338⟩
private def endpoint_7_43_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_43_base : receiptBase endpoint_7_43_flag endpoint_7_43_sources = some 191544825462678025 := by decide +kernel
private theorem endpoint_7_43_w0 : receiptWindow endpoint_7_43_flag endpoint_7_43_sources 0 2 191544825462678025 = some 191544825462678025 := by decide +kernel
private theorem endpoint_7_43_w2 : receiptWindow endpoint_7_43_flag endpoint_7_43_sources 2 2 191544825462678025 = some 191544825462678025 := by decide +kernel
private theorem endpoint_7_43_p4 : receiptWindow endpoint_7_43_flag endpoint_7_43_sources 0 4 191544825462678025 = some 191544825462678025 :=
  join_receipt_window endpoint_7_43_flag endpoint_7_43_sources 0 2 2 191544825462678025 191544825462678025 191544825462678025 endpoint_7_43_w0 endpoint_7_43_w2
private theorem endpoint_7_43_w4 : receiptWindow endpoint_7_43_flag endpoint_7_43_sources 4 2 191544825462678025 = some 191544825462678025 := by decide +kernel
private theorem endpoint_7_43_p6 : receiptWindow endpoint_7_43_flag endpoint_7_43_sources 0 6 191544825462678025 = some 191544825462678025 :=
  join_receipt_window endpoint_7_43_flag endpoint_7_43_sources 0 4 2 191544825462678025 191544825462678025 191544825462678025 endpoint_7_43_p4 endpoint_7_43_w4
def endpoint_7_43 : CertifiedEndpoint :=
  ⟨⟨7, 43, 4338⟩, 191544825462678025, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_43_flag endpoint_7_43_sources 6 191544825462678025 191544825462678025 rfl endpoint_7_43_base endpoint_7_43_p6) (by decide)⟩
private def endpoint_7_44_flag : Flag := ⟨7, 44, 4308⟩
private def endpoint_7_44_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_44_base : receiptBase endpoint_7_44_flag endpoint_7_44_sources = some 194009889083160938 := by decide +kernel
private theorem endpoint_7_44_w0 : receiptWindow endpoint_7_44_flag endpoint_7_44_sources 0 2 194009889083160938 = some 194009889083160938 := by decide +kernel
private theorem endpoint_7_44_w2 : receiptWindow endpoint_7_44_flag endpoint_7_44_sources 2 2 194009889083160938 = some 194009889083160938 := by decide +kernel
private theorem endpoint_7_44_p4 : receiptWindow endpoint_7_44_flag endpoint_7_44_sources 0 4 194009889083160938 = some 194009889083160938 :=
  join_receipt_window endpoint_7_44_flag endpoint_7_44_sources 0 2 2 194009889083160938 194009889083160938 194009889083160938 endpoint_7_44_w0 endpoint_7_44_w2
private theorem endpoint_7_44_w4 : receiptWindow endpoint_7_44_flag endpoint_7_44_sources 4 2 194009889083160938 = some 194009889083160938 := by decide +kernel
private theorem endpoint_7_44_p6 : receiptWindow endpoint_7_44_flag endpoint_7_44_sources 0 6 194009889083160938 = some 194009889083160938 :=
  join_receipt_window endpoint_7_44_flag endpoint_7_44_sources 0 4 2 194009889083160938 194009889083160938 194009889083160938 endpoint_7_44_p4 endpoint_7_44_w4
def endpoint_7_44 : CertifiedEndpoint :=
  ⟨⟨7, 44, 4308⟩, 194009889083160938, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_44_flag endpoint_7_44_sources 6 194009889083160938 194009889083160938 rfl endpoint_7_44_base endpoint_7_44_p6) (by decide)⟩
private def endpoint_7_45_flag : Flag := ⟨7, 45, 4277⟩
private def endpoint_7_45_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_45_base : receiptBase endpoint_7_45_flag endpoint_7_45_sources = some 196376946169668324 := by decide +kernel
private theorem endpoint_7_45_w0 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 0 2 196376946169668324 = some 196376946169668324 := by decide +kernel
private theorem endpoint_7_45_w2 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 2 2 196376946169668324 = some 196376946169668324 := by decide +kernel
private theorem endpoint_7_45_p4 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 0 4 196376946169668324 = some 196376946169668324 :=
  join_receipt_window endpoint_7_45_flag endpoint_7_45_sources 0 2 2 196376946169668324 196376946169668324 196376946169668324 endpoint_7_45_w0 endpoint_7_45_w2
private theorem endpoint_7_45_w4 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 4 2 196376946169668324 = some 196376946169668324 := by decide +kernel
private theorem endpoint_7_45_p6 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 0 6 196376946169668324 = some 196376946169668324 :=
  join_receipt_window endpoint_7_45_flag endpoint_7_45_sources 0 4 2 196376946169668324 196376946169668324 196376946169668324 endpoint_7_45_p4 endpoint_7_45_w4
def endpoint_7_45 : CertifiedEndpoint :=
  ⟨⟨7, 45, 4277⟩, 196376946169668324, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_45_flag endpoint_7_45_sources 6 196376946169668324 196376946169668324 rfl endpoint_7_45_base endpoint_7_45_p6) (by decide)⟩
private def endpoint_7_46_flag : Flag := ⟨7, 46, 4246⟩
private def endpoint_7_46_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_46_base : receiptBase endpoint_7_46_flag endpoint_7_46_sources = some 198689567460961939 := by decide +kernel
private theorem endpoint_7_46_w0 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 0 2 198689567460961939 = some 198689567460961939 := by decide +kernel
private theorem endpoint_7_46_w2 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 2 2 198689567460961939 = some 198689567460961939 := by decide +kernel
private theorem endpoint_7_46_p4 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 0 4 198689567460961939 = some 198689567460961939 :=
  join_receipt_window endpoint_7_46_flag endpoint_7_46_sources 0 2 2 198689567460961939 198689567460961939 198689567460961939 endpoint_7_46_w0 endpoint_7_46_w2
private theorem endpoint_7_46_w4 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 4 2 198689567460961939 = some 198689567460961939 := by decide +kernel
private theorem endpoint_7_46_p6 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 0 6 198689567460961939 = some 198689567460961939 :=
  join_receipt_window endpoint_7_46_flag endpoint_7_46_sources 0 4 2 198689567460961939 198689567460961939 198689567460961939 endpoint_7_46_p4 endpoint_7_46_w4
def endpoint_7_46 : CertifiedEndpoint :=
  ⟨⟨7, 46, 4246⟩, 198689567460961939, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_46_flag endpoint_7_46_sources 6 198689567460961939 198689567460961939 rfl endpoint_7_46_base endpoint_7_46_p6) (by decide)⟩
private def endpoint_7_47_flag : Flag := ⟨7, 47, 4214⟩
private def endpoint_7_47_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_47_base : receiptBase endpoint_7_47_flag endpoint_7_47_sources = some 200900725977314073 := by decide +kernel
private theorem endpoint_7_47_w0 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 0 2 200900725977314073 = some 200900725977314073 := by decide +kernel
private theorem endpoint_7_47_w2 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 2 2 200900725977314073 = some 200900725977314073 := by decide +kernel
private theorem endpoint_7_47_p4 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 0 4 200900725977314073 = some 200900725977314073 :=
  join_receipt_window endpoint_7_47_flag endpoint_7_47_sources 0 2 2 200900725977314073 200900725977314073 200900725977314073 endpoint_7_47_w0 endpoint_7_47_w2
private theorem endpoint_7_47_w4 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 4 2 200900725977314073 = some 200900725977314073 := by decide +kernel
private theorem endpoint_7_47_p6 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 0 6 200900725977314073 = some 200900725977314073 :=
  join_receipt_window endpoint_7_47_flag endpoint_7_47_sources 0 4 2 200900725977314073 200900725977314073 200900725977314073 endpoint_7_47_p4 endpoint_7_47_w4
def endpoint_7_47 : CertifiedEndpoint :=
  ⟨⟨7, 47, 4214⟩, 200900725977314073, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_47_flag endpoint_7_47_sources 6 200900725977314073 200900725977314073 rfl endpoint_7_47_base endpoint_7_47_p6) (by decide)⟩
private def endpoint_7_48_flag : Flag := ⟨7, 48, 4181⟩
private def endpoint_7_48_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_48_base : receiptBase endpoint_7_48_flag endpoint_7_48_sources = some 203007829538000261 := by decide +kernel
private theorem endpoint_7_48_w0 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 0 2 203007829538000261 = some 203007829538000261 := by decide +kernel
private theorem endpoint_7_48_w2 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 2 2 203007829538000261 = some 203007829538000261 := by decide +kernel
private theorem endpoint_7_48_p4 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 0 4 203007829538000261 = some 203007829538000261 :=
  join_receipt_window endpoint_7_48_flag endpoint_7_48_sources 0 2 2 203007829538000261 203007829538000261 203007829538000261 endpoint_7_48_w0 endpoint_7_48_w2
private theorem endpoint_7_48_w4 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 4 2 203007829538000261 = some 203007829538000261 := by decide +kernel
private theorem endpoint_7_48_p6 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 0 6 203007829538000261 = some 203007829538000261 :=
  join_receipt_window endpoint_7_48_flag endpoint_7_48_sources 0 4 2 203007829538000261 203007829538000261 203007829538000261 endpoint_7_48_p4 endpoint_7_48_w4
def endpoint_7_48 : CertifiedEndpoint :=
  ⟨⟨7, 48, 4181⟩, 203007829538000261, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_48_flag endpoint_7_48_sources 6 203007829538000261 203007829538000261 rfl endpoint_7_48_base endpoint_7_48_p6) (by decide)⟩
private def endpoint_7_49_flag : Flag := ⟨7, 49, 4148⟩
private def endpoint_7_49_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_49_base : receiptBase endpoint_7_49_flag endpoint_7_49_sources = some 205057041062506724 := by decide +kernel
private theorem endpoint_7_49_w0 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 0 2 205057041062506724 = some 205057041062506724 := by decide +kernel
private theorem endpoint_7_49_w2 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 2 2 205057041062506724 = some 205057041062506724 := by decide +kernel
private theorem endpoint_7_49_p4 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 0 4 205057041062506724 = some 205057041062506724 :=
  join_receipt_window endpoint_7_49_flag endpoint_7_49_sources 0 2 2 205057041062506724 205057041062506724 205057041062506724 endpoint_7_49_w0 endpoint_7_49_w2
private theorem endpoint_7_49_w4 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 4 2 205057041062506724 = some 205057041062506724 := by decide +kernel
private theorem endpoint_7_49_p6 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 0 6 205057041062506724 = some 205057041062506724 :=
  join_receipt_window endpoint_7_49_flag endpoint_7_49_sources 0 4 2 205057041062506724 205057041062506724 205057041062506724 endpoint_7_49_p4 endpoint_7_49_w4
def endpoint_7_49 : CertifiedEndpoint :=
  ⟨⟨7, 49, 4148⟩, 205057041062506724, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_49_flag endpoint_7_49_sources 6 205057041062506724 205057041062506724 rfl endpoint_7_49_base endpoint_7_49_p6) (by decide)⟩
private def endpoint_7_50_flag : Flag := ⟨7, 50, 4114⟩
private def endpoint_7_50_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_50_base : receiptBase endpoint_7_50_flag endpoint_7_50_sources = some 206998741390381288 := by decide +kernel
private theorem endpoint_7_50_w0 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 0 2 206998741390381288 = some 206998741390381288 := by decide +kernel
private theorem endpoint_7_50_w2 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 2 2 206998741390381288 = some 206998741390381288 := by decide +kernel
private theorem endpoint_7_50_p4 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 0 4 206998741390381288 = some 206998741390381288 :=
  join_receipt_window endpoint_7_50_flag endpoint_7_50_sources 0 2 2 206998741390381288 206998741390381288 206998741390381288 endpoint_7_50_w0 endpoint_7_50_w2
private theorem endpoint_7_50_w4 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 4 2 206998741390381288 = some 206998741390381288 := by decide +kernel
private theorem endpoint_7_50_p6 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 0 6 206998741390381288 = some 206998741390381288 :=
  join_receipt_window endpoint_7_50_flag endpoint_7_50_sources 0 4 2 206998741390381288 206998741390381288 206998741390381288 endpoint_7_50_p4 endpoint_7_50_w4
def endpoint_7_50 : CertifiedEndpoint :=
  ⟨⟨7, 50, 4114⟩, 206998741390381288, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_50_flag endpoint_7_50_sources 6 206998741390381288 206998741390381288 rfl endpoint_7_50_base endpoint_7_50_p6) (by decide)⟩
private def endpoint_7_51_flag : Flag := ⟨7, 51, 4080⟩
private def endpoint_7_51_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_51_base : receiptBase endpoint_7_51_flag endpoint_7_51_sources = some 208880821561593149 := by decide +kernel
private theorem endpoint_7_51_w0 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 0 2 208880821561593149 = some 208880821561593149 := by decide +kernel
private theorem endpoint_7_51_w2 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 2 2 208880821561593149 = some 208880821561593149 := by decide +kernel
private theorem endpoint_7_51_p4 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 0 4 208880821561593149 = some 208880821561593149 :=
  join_receipt_window endpoint_7_51_flag endpoint_7_51_sources 0 2 2 208880821561593149 208880821561593149 208880821561593149 endpoint_7_51_w0 endpoint_7_51_w2
private theorem endpoint_7_51_w4 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 4 2 208880821561593149 = some 208880821561593149 := by decide +kernel
private theorem endpoint_7_51_p6 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 0 6 208880821561593149 = some 208880821561593149 :=
  join_receipt_window endpoint_7_51_flag endpoint_7_51_sources 0 4 2 208880821561593149 208880821561593149 208880821561593149 endpoint_7_51_p4 endpoint_7_51_w4
def endpoint_7_51 : CertifiedEndpoint :=
  ⟨⟨7, 51, 4080⟩, 208880821561593149, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_51_flag endpoint_7_51_sources 6 208880821561593149 208880821561593149 rfl endpoint_7_51_base endpoint_7_51_p6) (by decide)⟩
private def endpoint_7_52_flag : Flag := ⟨7, 52, 4044⟩
private def endpoint_7_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_52_base : receiptBase endpoint_7_52_flag endpoint_7_52_sources = some 211964503452455762 := by decide +kernel
private theorem endpoint_7_52_w0 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 0 2 211964503452455762 = some 211964503452455762 := by decide +kernel
private theorem endpoint_7_52_w2 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 2 2 211964503452455762 = some 211964503452455762 := by decide +kernel
private theorem endpoint_7_52_p4 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 0 4 211964503452455762 = some 211964503452455762 :=
  join_receipt_window endpoint_7_52_flag endpoint_7_52_sources 0 2 2 211964503452455762 211964503452455762 211964503452455762 endpoint_7_52_w0 endpoint_7_52_w2
private theorem endpoint_7_52_w4 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 4 2 211964503452455762 = some 211964503452455762 := by decide +kernel
private theorem endpoint_7_52_p6 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 0 6 211964503452455762 = some 211964503452455762 :=
  join_receipt_window endpoint_7_52_flag endpoint_7_52_sources 0 4 2 211964503452455762 211964503452455762 211964503452455762 endpoint_7_52_p4 endpoint_7_52_w4
def endpoint_7_52 : CertifiedEndpoint :=
  ⟨⟨7, 52, 4044⟩, 211964503452455762, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_52_flag endpoint_7_52_sources 6 211964503452455762 211964503452455762 rfl endpoint_7_52_base endpoint_7_52_p6) (by decide)⟩
private def endpoint_7_53_flag : Flag := ⟨7, 53, 4008⟩
private def endpoint_7_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_53_base : receiptBase endpoint_7_53_flag endpoint_7_53_sources = some 213624983707676913 := by decide +kernel
private theorem endpoint_7_53_w0 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 0 2 213624983707676913 = some 213624983707676913 := by decide +kernel
private theorem endpoint_7_53_w2 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 2 2 213624983707676913 = some 213624983707676913 := by decide +kernel
private theorem endpoint_7_53_p4 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 0 4 213624983707676913 = some 213624983707676913 :=
  join_receipt_window endpoint_7_53_flag endpoint_7_53_sources 0 2 2 213624983707676913 213624983707676913 213624983707676913 endpoint_7_53_w0 endpoint_7_53_w2
private theorem endpoint_7_53_w4 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 4 2 213624983707676913 = some 213624983707676913 := by decide +kernel
private theorem endpoint_7_53_p6 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 0 6 213624983707676913 = some 213624983707676913 :=
  join_receipt_window endpoint_7_53_flag endpoint_7_53_sources 0 4 2 213624983707676913 213624983707676913 213624983707676913 endpoint_7_53_p4 endpoint_7_53_w4
def endpoint_7_53 : CertifiedEndpoint :=
  ⟨⟨7, 53, 4008⟩, 213624983707676913, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_53_flag endpoint_7_53_sources 6 213624983707676913 213624983707676913 rfl endpoint_7_53_base endpoint_7_53_p6) (by decide)⟩
private def endpoint_7_54_flag : Flag := ⟨7, 54, 3970⟩
private def endpoint_7_54_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_54_base : receiptBase endpoint_7_54_flag endpoint_7_54_sources = some 215114542259248733 := by decide +kernel
private theorem endpoint_7_54_w0 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 0 2 215114542259248733 = some 215114542259248733 := by decide +kernel
private theorem endpoint_7_54_w2 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 2 2 215114542259248733 = some 215114542259248733 := by decide +kernel
private theorem endpoint_7_54_p4 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 0 4 215114542259248733 = some 215114542259248733 :=
  join_receipt_window endpoint_7_54_flag endpoint_7_54_sources 0 2 2 215114542259248733 215114542259248733 215114542259248733 endpoint_7_54_w0 endpoint_7_54_w2
private theorem endpoint_7_54_w4 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 4 2 215114542259248733 = some 215114542259248733 := by decide +kernel
private theorem endpoint_7_54_p6 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 0 6 215114542259248733 = some 215114542259248733 :=
  join_receipt_window endpoint_7_54_flag endpoint_7_54_sources 0 4 2 215114542259248733 215114542259248733 215114542259248733 endpoint_7_54_p4 endpoint_7_54_w4
def endpoint_7_54 : CertifiedEndpoint :=
  ⟨⟨7, 54, 3970⟩, 215114542259248733, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_54_flag endpoint_7_54_sources 6 215114542259248733 215114542259248733 rfl endpoint_7_54_base endpoint_7_54_p6) (by decide)⟩
private def endpoint_7_55_flag : Flag := ⟨7, 55, 3932⟩
private def endpoint_7_55_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_55_base : receiptBase endpoint_7_55_flag endpoint_7_55_sources = some 216536874999126837 := by decide +kernel
private theorem endpoint_7_55_w0 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 0 2 216536874999126837 = some 216536874999126837 := by decide +kernel
private theorem endpoint_7_55_w2 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 2 2 216536874999126837 = some 216536874999126837 := by decide +kernel
private theorem endpoint_7_55_p4 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 0 4 216536874999126837 = some 216536874999126837 :=
  join_receipt_window endpoint_7_55_flag endpoint_7_55_sources 0 2 2 216536874999126837 216536874999126837 216536874999126837 endpoint_7_55_w0 endpoint_7_55_w2
private theorem endpoint_7_55_w4 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 4 2 216536874999126837 = some 216536874999126837 := by decide +kernel
private theorem endpoint_7_55_p6 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 0 6 216536874999126837 = some 216536874999126837 :=
  join_receipt_window endpoint_7_55_flag endpoint_7_55_sources 0 4 2 216536874999126837 216536874999126837 216536874999126837 endpoint_7_55_p4 endpoint_7_55_w4
def endpoint_7_55 : CertifiedEndpoint :=
  ⟨⟨7, 55, 3932⟩, 216536874999126837, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_55_flag endpoint_7_55_sources 6 216536874999126837 216536874999126837 rfl endpoint_7_55_base endpoint_7_55_p6) (by decide)⟩
private def endpoint_7_56_flag : Flag := ⟨7, 56, 3893⟩
private def endpoint_7_56_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_56_base : receiptBase endpoint_7_56_flag endpoint_7_56_sources = some 217836641731375302 := by decide +kernel
private theorem endpoint_7_56_w0 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 0 2 217836641731375302 = some 217836641731375302 := by decide +kernel
private theorem endpoint_7_56_w2 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 2 2 217836641731375302 = some 217836641731375302 := by decide +kernel
private theorem endpoint_7_56_p4 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 0 4 217836641731375302 = some 217836641731375302 :=
  join_receipt_window endpoint_7_56_flag endpoint_7_56_sources 0 2 2 217836641731375302 217836641731375302 217836641731375302 endpoint_7_56_w0 endpoint_7_56_w2
private theorem endpoint_7_56_w4 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 4 2 217836641731375302 = some 217836641731375302 := by decide +kernel
private theorem endpoint_7_56_p6 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 0 6 217836641731375302 = some 217836641731375302 :=
  join_receipt_window endpoint_7_56_flag endpoint_7_56_sources 0 4 2 217836641731375302 217836641731375302 217836641731375302 endpoint_7_56_p4 endpoint_7_56_w4
def endpoint_7_56 : CertifiedEndpoint :=
  ⟨⟨7, 56, 3893⟩, 217836641731375302, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_56_flag endpoint_7_56_sources 6 217836641731375302 217836641731375302 rfl endpoint_7_56_base endpoint_7_56_p6) (by decide)⟩
private def endpoint_7_57_flag : Flag := ⟨7, 57, 3852⟩
private def endpoint_7_57_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_57_base : receiptBase endpoint_7_57_flag endpoint_7_57_sources = some 218955010010100090 := by decide +kernel
private theorem endpoint_7_57_w0 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 0 2 218955010010100090 = some 218955010010100090 := by decide +kernel
private theorem endpoint_7_57_w2 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 2 2 218955010010100090 = some 218955010010100090 := by decide +kernel
private theorem endpoint_7_57_p4 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 0 4 218955010010100090 = some 218955010010100090 :=
  join_receipt_window endpoint_7_57_flag endpoint_7_57_sources 0 2 2 218955010010100090 218955010010100090 218955010010100090 endpoint_7_57_w0 endpoint_7_57_w2
private theorem endpoint_7_57_w4 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 4 2 218955010010100090 = some 218955010010100090 := by decide +kernel
private theorem endpoint_7_57_p6 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 0 6 218955010010100090 = some 218955010010100090 :=
  join_receipt_window endpoint_7_57_flag endpoint_7_57_sources 0 4 2 218955010010100090 218955010010100090 218955010010100090 endpoint_7_57_p4 endpoint_7_57_w4
def endpoint_7_57 : CertifiedEndpoint :=
  ⟨⟨7, 57, 3852⟩, 218955010010100090, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_57_flag endpoint_7_57_sources 6 218955010010100090 218955010010100090 rfl endpoint_7_57_base endpoint_7_57_p6) (by decide)⟩
private def endpoint_7_58_flag : Flag := ⟨7, 58, 3811⟩
private def endpoint_7_58_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_58_base : receiptBase endpoint_7_58_flag endpoint_7_58_sources = some 220710247081869442 := by decide +kernel
private theorem endpoint_7_58_w0 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 0 2 220710247081869442 = some 220710247081869442 := by decide +kernel
private theorem endpoint_7_58_w2 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 2 2 220710247081869442 = some 220710247081869442 := by decide +kernel
private theorem endpoint_7_58_p4 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 0 4 220710247081869442 = some 220710247081869442 :=
  join_receipt_window endpoint_7_58_flag endpoint_7_58_sources 0 2 2 220710247081869442 220710247081869442 220710247081869442 endpoint_7_58_w0 endpoint_7_58_w2
private theorem endpoint_7_58_w4 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 4 2 220710247081869442 = some 220710247081869442 := by decide +kernel
private theorem endpoint_7_58_p6 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 0 6 220710247081869442 = some 220710247081869442 :=
  join_receipt_window endpoint_7_58_flag endpoint_7_58_sources 0 4 2 220710247081869442 220710247081869442 220710247081869442 endpoint_7_58_p4 endpoint_7_58_w4
def endpoint_7_58 : CertifiedEndpoint :=
  ⟨⟨7, 58, 3811⟩, 220710247081869442, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_58_flag endpoint_7_58_sources 6 220710247081869442 220710247081869442 rfl endpoint_7_58_base endpoint_7_58_p6) (by decide)⟩
private def endpoint_7_59_flag : Flag := ⟨7, 59, 3767⟩
private def endpoint_7_59_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_59_base : receiptBase endpoint_7_59_flag endpoint_7_59_sources = some 221501302643490115 := by decide +kernel
private theorem endpoint_7_59_w0 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 0 2 221501302643490115 = some 221501302643490115 := by decide +kernel
private theorem endpoint_7_59_w2 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 2 2 221501302643490115 = some 221501302643490115 := by decide +kernel
private theorem endpoint_7_59_p4 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 0 4 221501302643490115 = some 221501302643490115 :=
  join_receipt_window endpoint_7_59_flag endpoint_7_59_sources 0 2 2 221501302643490115 221501302643490115 221501302643490115 endpoint_7_59_w0 endpoint_7_59_w2
private theorem endpoint_7_59_w4 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 4 2 221501302643490115 = some 221501302643490115 := by decide +kernel
private theorem endpoint_7_59_p6 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 0 6 221501302643490115 = some 221501302643490115 :=
  join_receipt_window endpoint_7_59_flag endpoint_7_59_sources 0 4 2 221501302643490115 221501302643490115 221501302643490115 endpoint_7_59_p4 endpoint_7_59_w4
def endpoint_7_59 : CertifiedEndpoint :=
  ⟨⟨7, 59, 3767⟩, 221501302643490115, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_59_flag endpoint_7_59_sources 6 221501302643490115 221501302643490115 rfl endpoint_7_59_base endpoint_7_59_p6) (by decide)⟩
private def endpoint_7_60_flag : Flag := ⟨7, 60, 3723⟩
private def endpoint_7_60_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_60_base : receiptBase endpoint_7_60_flag endpoint_7_60_sources = some 222214655643542728 := by decide +kernel
private theorem endpoint_7_60_w0 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 0 2 222214655643542728 = some 222214655643542728 := by decide +kernel
private theorem endpoint_7_60_w2 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 2 2 222214655643542728 = some 222214655643542728 := by decide +kernel
private theorem endpoint_7_60_p4 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 0 4 222214655643542728 = some 222214655643542728 :=
  join_receipt_window endpoint_7_60_flag endpoint_7_60_sources 0 2 2 222214655643542728 222214655643542728 222214655643542728 endpoint_7_60_w0 endpoint_7_60_w2
private theorem endpoint_7_60_w4 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 4 2 222214655643542728 = some 222214655643542728 := by decide +kernel
private theorem endpoint_7_60_p6 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 0 6 222214655643542728 = some 222214655643542728 :=
  join_receipt_window endpoint_7_60_flag endpoint_7_60_sources 0 4 2 222214655643542728 222214655643542728 222214655643542728 endpoint_7_60_p4 endpoint_7_60_w4
def endpoint_7_60 : CertifiedEndpoint :=
  ⟨⟨7, 60, 3723⟩, 222214655643542728, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_60_flag endpoint_7_60_sources 6 222214655643542728 222214655643542728 rfl endpoint_7_60_base endpoint_7_60_p6) (by decide)⟩
private def endpoint_7_61_flag : Flag := ⟨7, 61, 3676⟩
private def endpoint_7_61_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_61_base : receiptBase endpoint_7_61_flag endpoint_7_61_sources = some 222670622517782763 := by decide +kernel
private theorem endpoint_7_61_w0 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 0 2 222670622517782763 = some 222670622517782763 := by decide +kernel
private theorem endpoint_7_61_w2 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 2 2 222670622517782763 = some 222670622517782763 := by decide +kernel
private theorem endpoint_7_61_p4 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 0 4 222670622517782763 = some 222670622517782763 :=
  join_receipt_window endpoint_7_61_flag endpoint_7_61_sources 0 2 2 222670622517782763 222670622517782763 222670622517782763 endpoint_7_61_w0 endpoint_7_61_w2
private theorem endpoint_7_61_w4 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 4 2 222670622517782763 = some 222670622517782763 := by decide +kernel
private theorem endpoint_7_61_p6 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 0 6 222670622517782763 = some 222670622517782763 :=
  join_receipt_window endpoint_7_61_flag endpoint_7_61_sources 0 4 2 222670622517782763 222670622517782763 222670622517782763 endpoint_7_61_p4 endpoint_7_61_w4
def endpoint_7_61 : CertifiedEndpoint :=
  ⟨⟨7, 61, 3676⟩, 222670622517782763, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_61_flag endpoint_7_61_sources 6 222670622517782763 222670622517782763 rfl endpoint_7_61_base endpoint_7_61_p6) (by decide)⟩
private def endpoint_7_62_flag : Flag := ⟨7, 62, 3628⟩
private def endpoint_7_62_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_62_base : receiptBase endpoint_7_62_flag endpoint_7_62_sources = some 222982880871613199 := by decide +kernel
private theorem endpoint_7_62_w0 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 0 2 222982880871613199 = some 222982880871613199 := by decide +kernel
private theorem endpoint_7_62_w2 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 2 2 222982880871613199 = some 222982880871613199 := by decide +kernel
private theorem endpoint_7_62_p4 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 0 4 222982880871613199 = some 222982880871613199 :=
  join_receipt_window endpoint_7_62_flag endpoint_7_62_sources 0 2 2 222982880871613199 222982880871613199 222982880871613199 endpoint_7_62_w0 endpoint_7_62_w2
private theorem endpoint_7_62_w4 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 4 2 222982880871613199 = some 222982880871613199 := by decide +kernel
private theorem endpoint_7_62_p6 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 0 6 222982880871613199 = some 222982880871613199 :=
  join_receipt_window endpoint_7_62_flag endpoint_7_62_sources 0 4 2 222982880871613199 222982880871613199 222982880871613199 endpoint_7_62_p4 endpoint_7_62_w4
def endpoint_7_62 : CertifiedEndpoint :=
  ⟨⟨7, 62, 3628⟩, 222982880871613199, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_62_flag endpoint_7_62_sources 6 222982880871613199 222982880871613199 rfl endpoint_7_62_base endpoint_7_62_p6) (by decide)⟩
private def endpoint_7_63_flag : Flag := ⟨7, 63, 3577⟩
private def endpoint_7_63_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_63_base : receiptBase endpoint_7_63_flag endpoint_7_63_sources = some 225392894929357708 := by decide +kernel
private theorem endpoint_7_63_w0 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 0 2 225392894929357708 = some 225392894929357708 := by decide +kernel
private theorem endpoint_7_63_w2 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 2 2 225392894929357708 = some 225392894929357708 := by decide +kernel
private theorem endpoint_7_63_p4 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 0 4 225392894929357708 = some 225392894929357708 :=
  join_receipt_window endpoint_7_63_flag endpoint_7_63_sources 0 2 2 225392894929357708 225392894929357708 225392894929357708 endpoint_7_63_w0 endpoint_7_63_w2
private theorem endpoint_7_63_w4 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 4 2 225392894929357708 = some 225392894929357708 := by decide +kernel
private theorem endpoint_7_63_p6 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 0 6 225392894929357708 = some 225392894929357708 :=
  join_receipt_window endpoint_7_63_flag endpoint_7_63_sources 0 4 2 225392894929357708 225392894929357708 225392894929357708 endpoint_7_63_p4 endpoint_7_63_w4
def endpoint_7_63 : CertifiedEndpoint :=
  ⟨⟨7, 63, 3577⟩, 225392894929357708, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_63_flag endpoint_7_63_sources 6 225392894929357708 225392894929357708 rfl endpoint_7_63_base endpoint_7_63_p6) (by decide)⟩
private def endpoint_7_64_flag : Flag := ⟨7, 64, 3524⟩
private def endpoint_7_64_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_64_base : receiptBase endpoint_7_64_flag endpoint_7_64_sources = some 225199326766699310 := by decide +kernel
private theorem endpoint_7_64_w0 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 0 2 225199326766699310 = some 225199326766699310 := by decide +kernel
private theorem endpoint_7_64_w2 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 2 2 225199326766699310 = some 225199326766699310 := by decide +kernel
private theorem endpoint_7_64_p4 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 0 4 225199326766699310 = some 225199326766699310 :=
  join_receipt_window endpoint_7_64_flag endpoint_7_64_sources 0 2 2 225199326766699310 225199326766699310 225199326766699310 endpoint_7_64_w0 endpoint_7_64_w2
private theorem endpoint_7_64_w4 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 4 2 225199326766699310 = some 225199326766699310 := by decide +kernel
private theorem endpoint_7_64_p6 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 0 6 225199326766699310 = some 225199326766699310 :=
  join_receipt_window endpoint_7_64_flag endpoint_7_64_sources 0 4 2 225199326766699310 225199326766699310 225199326766699310 endpoint_7_64_p4 endpoint_7_64_w4
def endpoint_7_64 : CertifiedEndpoint :=
  ⟨⟨7, 64, 3524⟩, 225199326766699310, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_64_flag endpoint_7_64_sources 6 225199326766699310 225199326766699310 rfl endpoint_7_64_base endpoint_7_64_p6) (by decide)⟩
private def endpoint_7_65_flag : Flag := ⟨7, 65, 3468⟩
private def endpoint_7_65_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_65_base : receiptBase endpoint_7_65_flag endpoint_7_65_sources = some 224718710344177435 := by decide +kernel
private theorem endpoint_7_65_w0 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 0 2 224718710344177435 = some 224718710344177435 := by decide +kernel
private theorem endpoint_7_65_w2 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 2 2 224718710344177435 = some 224718710344177435 := by decide +kernel
private theorem endpoint_7_65_p4 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 0 4 224718710344177435 = some 224718710344177435 :=
  join_receipt_window endpoint_7_65_flag endpoint_7_65_sources 0 2 2 224718710344177435 224718710344177435 224718710344177435 endpoint_7_65_w0 endpoint_7_65_w2
private theorem endpoint_7_65_w4 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 4 2 224718710344177435 = some 224718710344177435 := by decide +kernel
private theorem endpoint_7_65_p6 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 0 6 224718710344177435 = some 224718710344177435 :=
  join_receipt_window endpoint_7_65_flag endpoint_7_65_sources 0 4 2 224718710344177435 224718710344177435 224718710344177435 endpoint_7_65_p4 endpoint_7_65_w4
def endpoint_7_65 : CertifiedEndpoint :=
  ⟨⟨7, 65, 3468⟩, 224718710344177435, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_65_flag endpoint_7_65_sources 6 224718710344177435 224718710344177435 rfl endpoint_7_65_base endpoint_7_65_p6) (by decide)⟩
private def endpoint_7_66_flag : Flag := ⟨7, 66, 3410⟩
private def endpoint_7_66_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_66_base : receiptBase endpoint_7_66_flag endpoint_7_66_sources = some 224008211886690218 := by decide +kernel
private theorem endpoint_7_66_w0 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 0 2 224008211886690218 = some 224008211886690218 := by decide +kernel
private theorem endpoint_7_66_w2 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 2 2 224008211886690218 = some 224008211886690218 := by decide +kernel
private theorem endpoint_7_66_p4 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 0 4 224008211886690218 = some 224008211886690218 :=
  join_receipt_window endpoint_7_66_flag endpoint_7_66_sources 0 2 2 224008211886690218 224008211886690218 224008211886690218 endpoint_7_66_w0 endpoint_7_66_w2
private theorem endpoint_7_66_w4 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 4 2 224008211886690218 = some 224008211886690218 := by decide +kernel
private theorem endpoint_7_66_p6 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 0 6 224008211886690218 = some 224008211886690218 :=
  join_receipt_window endpoint_7_66_flag endpoint_7_66_sources 0 4 2 224008211886690218 224008211886690218 224008211886690218 endpoint_7_66_p4 endpoint_7_66_w4
def endpoint_7_66 : CertifiedEndpoint :=
  ⟨⟨7, 66, 3410⟩, 224008211886690218, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_66_flag endpoint_7_66_sources 6 224008211886690218 224008211886690218 rfl endpoint_7_66_base endpoint_7_66_p6) (by decide)⟩
private def endpoint_7_67_flag : Flag := ⟨7, 67, 3348⟩
private def endpoint_7_67_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_7_67_base : receiptBase endpoint_7_67_flag endpoint_7_67_sources = some 224550842976001417 := by decide +kernel
private theorem endpoint_7_67_w0 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 0 2 224550842976001417 = some 224550842976001417 := by decide +kernel
private theorem endpoint_7_67_w2 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 2 2 224550842976001417 = some 224550842976001417 := by decide +kernel
private theorem endpoint_7_67_p4 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 0 4 224550842976001417 = some 224550842976001417 :=
  join_receipt_window endpoint_7_67_flag endpoint_7_67_sources 0 2 2 224550842976001417 224550842976001417 224550842976001417 endpoint_7_67_w0 endpoint_7_67_w2
private theorem endpoint_7_67_w4 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 4 2 224550842976001417 = some 224550842976001417 := by decide +kernel
private theorem endpoint_7_67_p6 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 0 6 224550842976001417 = some 224550842976001417 :=
  join_receipt_window endpoint_7_67_flag endpoint_7_67_sources 0 4 2 224550842976001417 224550842976001417 224550842976001417 endpoint_7_67_p4 endpoint_7_67_w4
def endpoint_7_67 : CertifiedEndpoint :=
  ⟨⟨7, 67, 3348⟩, 224550842976001417, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_7_67_flag endpoint_7_67_sources 6 224550842976001417 224550842976001417 rfl endpoint_7_67_base endpoint_7_67_p6) (by decide)⟩
private def endpoint_7_68_flag : Flag := ⟨7, 68, 3283⟩
private def endpoint_7_68_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_7_68_base : receiptBase endpoint_7_68_flag endpoint_7_68_sources = some 223153737812233031 := by decide +kernel
private theorem endpoint_7_68_w0 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 0 2 223153737812233031 = some 223153737812233031 := by decide +kernel
private theorem endpoint_7_68_w2 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 2 2 223153737812233031 = some 223153737812233031 := by decide +kernel
private theorem endpoint_7_68_p4 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 0 4 223153737812233031 = some 223153737812233031 :=
  join_receipt_window endpoint_7_68_flag endpoint_7_68_sources 0 2 2 223153737812233031 223153737812233031 223153737812233031 endpoint_7_68_w0 endpoint_7_68_w2
private theorem endpoint_7_68_w4 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 4 2 223153737812233031 = some 223153737812233031 := by decide +kernel
private theorem endpoint_7_68_p6 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 0 6 223153737812233031 = some 223153737812233031 :=
  join_receipt_window endpoint_7_68_flag endpoint_7_68_sources 0 4 2 223153737812233031 223153737812233031 223153737812233031 endpoint_7_68_p4 endpoint_7_68_w4
def endpoint_7_68 : CertifiedEndpoint :=
  ⟨⟨7, 68, 3283⟩, 223153737812233031, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_7_68_flag endpoint_7_68_sources 6 223153737812233031 223153737812233031 rfl endpoint_7_68_base endpoint_7_68_p6) (by decide)⟩
private def endpoint_7_69_flag : Flag := ⟨7, 69, 3215⟩
private def endpoint_7_69_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_7_69_base : receiptBase endpoint_7_69_flag endpoint_7_69_sources = some 221434986890090591 := by decide +kernel
private theorem endpoint_7_69_w0 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 0 2 221434986890090591 = some 221434986890090591 := by decide +kernel
private theorem endpoint_7_69_w2 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 2 2 221434986890090591 = some 221434986890090591 := by decide +kernel
private theorem endpoint_7_69_p4 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 0 4 221434986890090591 = some 221434986890090591 :=
  join_receipt_window endpoint_7_69_flag endpoint_7_69_sources 0 2 2 221434986890090591 221434986890090591 221434986890090591 endpoint_7_69_w0 endpoint_7_69_w2
private theorem endpoint_7_69_w4 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 4 2 221434986890090591 = some 221434986890090591 := by decide +kernel
private theorem endpoint_7_69_p6 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 0 6 221434986890090591 = some 221434986890090591 :=
  join_receipt_window endpoint_7_69_flag endpoint_7_69_sources 0 4 2 221434986890090591 221434986890090591 221434986890090591 endpoint_7_69_p4 endpoint_7_69_w4
def endpoint_7_69 : CertifiedEndpoint :=
  ⟨⟨7, 69, 3215⟩, 221434986890090591, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_7_69_flag endpoint_7_69_sources 6 221434986890090591 221434986890090591 rfl endpoint_7_69_base endpoint_7_69_p6) (by decide)⟩
private def endpoint_7_70_flag : Flag := ⟨7, 70, 3144⟩
private def endpoint_7_70_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_7_70_base : receiptBase endpoint_7_70_flag endpoint_7_70_sources = some 221021504122973585 := by decide +kernel
private theorem endpoint_7_70_w0 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 0 2 221021504122973585 = some 221021504122973585 := by decide +kernel
private theorem endpoint_7_70_w2 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 2 2 221021504122973585 = some 221021504122973585 := by decide +kernel
private theorem endpoint_7_70_p4 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 0 4 221021504122973585 = some 221021504122973585 :=
  join_receipt_window endpoint_7_70_flag endpoint_7_70_sources 0 2 2 221021504122973585 221021504122973585 221021504122973585 endpoint_7_70_w0 endpoint_7_70_w2
private theorem endpoint_7_70_w4 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 4 2 221021504122973585 = some 221021504122973585 := by decide +kernel
private theorem endpoint_7_70_p6 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 0 6 221021504122973585 = some 221021504122973585 :=
  join_receipt_window endpoint_7_70_flag endpoint_7_70_sources 0 4 2 221021504122973585 221021504122973585 221021504122973585 endpoint_7_70_p4 endpoint_7_70_w4
def endpoint_7_70 : CertifiedEndpoint :=
  ⟨⟨7, 70, 3144⟩, 221021504122973585, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_7_70_flag endpoint_7_70_sources 6 221021504122973585 221021504122973585 rfl endpoint_7_70_base endpoint_7_70_p6) (by decide)⟩
private def endpoint_7_71_flag : Flag := ⟨7, 71, 3069⟩
private def endpoint_7_71_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_7_71_base : receiptBase endpoint_7_71_flag endpoint_7_71_sources = some 220203820256674740 := by decide +kernel
private theorem endpoint_7_71_w0 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 0 2 220203820256674740 = some 220203820256674740 := by decide +kernel
private theorem endpoint_7_71_w2 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 2 2 220203820256674740 = some 220203820256674740 := by decide +kernel
private theorem endpoint_7_71_p4 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 0 4 220203820256674740 = some 220203820256674740 :=
  join_receipt_window endpoint_7_71_flag endpoint_7_71_sources 0 2 2 220203820256674740 220203820256674740 220203820256674740 endpoint_7_71_w0 endpoint_7_71_w2
private theorem endpoint_7_71_w4 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 4 2 220203820256674740 = some 220203820256674740 := by decide +kernel
private theorem endpoint_7_71_p6 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 0 6 220203820256674740 = some 220203820256674740 :=
  join_receipt_window endpoint_7_71_flag endpoint_7_71_sources 0 4 2 220203820256674740 220203820256674740 220203820256674740 endpoint_7_71_p4 endpoint_7_71_w4
def endpoint_7_71 : CertifiedEndpoint :=
  ⟨⟨7, 71, 3069⟩, 220203820256674740, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_7_71_flag endpoint_7_71_sources 6 220203820256674740 220203820256674740 rfl endpoint_7_71_base endpoint_7_71_p6) (by decide)⟩
private def endpoint_7_72_flag : Flag := ⟨7, 72, 2991⟩
private def endpoint_7_72_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_7_72_base : receiptBase endpoint_7_72_flag endpoint_7_72_sources = some 217360228228491632 := by decide +kernel
private theorem endpoint_7_72_w0 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 0 2 217360228228491632 = some 217360228228491632 := by decide +kernel
private theorem endpoint_7_72_w2 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 2 2 217360228228491632 = some 217360228228491632 := by decide +kernel
private theorem endpoint_7_72_p4 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 0 4 217360228228491632 = some 217360228228491632 :=
  join_receipt_window endpoint_7_72_flag endpoint_7_72_sources 0 2 2 217360228228491632 217360228228491632 217360228228491632 endpoint_7_72_w0 endpoint_7_72_w2
private theorem endpoint_7_72_w4 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 4 2 217360228228491632 = some 217360228228491632 := by decide +kernel
private theorem endpoint_7_72_p6 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 0 6 217360228228491632 = some 217360228228491632 :=
  join_receipt_window endpoint_7_72_flag endpoint_7_72_sources 0 4 2 217360228228491632 217360228228491632 217360228228491632 endpoint_7_72_p4 endpoint_7_72_w4
def endpoint_7_72 : CertifiedEndpoint :=
  ⟨⟨7, 72, 2991⟩, 217360228228491632, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_7_72_flag endpoint_7_72_sources 6 217360228228491632 217360228228491632 rfl endpoint_7_72_base endpoint_7_72_p6) (by decide)⟩
private def endpoint_7_73_flag : Flag := ⟨7, 73, 2911⟩
private def endpoint_7_73_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_7_73_base : receiptBase endpoint_7_73_flag endpoint_7_73_sources = some 217423848399529621 := by decide +kernel
private theorem endpoint_7_73_w0 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 0 2 217423848399529621 = some 217423848399529621 := by decide +kernel
private theorem endpoint_7_73_w2 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 2 2 217423848399529621 = some 217423848399529621 := by decide +kernel
private theorem endpoint_7_73_p4 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 0 4 217423848399529621 = some 217423848399529621 :=
  join_receipt_window endpoint_7_73_flag endpoint_7_73_sources 0 2 2 217423848399529621 217423848399529621 217423848399529621 endpoint_7_73_w0 endpoint_7_73_w2
private theorem endpoint_7_73_w4 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 4 2 217423848399529621 = some 217423848399529621 := by decide +kernel
private theorem endpoint_7_73_p6 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 0 6 217423848399529621 = some 217423848399529621 :=
  join_receipt_window endpoint_7_73_flag endpoint_7_73_sources 0 4 2 217423848399529621 217423848399529621 217423848399529621 endpoint_7_73_p4 endpoint_7_73_w4
def endpoint_7_73 : CertifiedEndpoint :=
  ⟨⟨7, 73, 2911⟩, 217423848399529621, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_7_73_flag endpoint_7_73_sources 6 217423848399529621 217423848399529621 rfl endpoint_7_73_base endpoint_7_73_p6) (by decide)⟩
private def endpoint_7_74_flag : Flag := ⟨7, 74, 2827⟩
private def endpoint_7_74_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_7_74_base : receiptBase endpoint_7_74_flag endpoint_7_74_sources = some 213796562969633364 := by decide +kernel
private theorem endpoint_7_74_w0 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 0 2 213796562969633364 = some 213796562969633364 := by decide +kernel
private theorem endpoint_7_74_w2 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 2 2 213796562969633364 = some 213796562969633364 := by decide +kernel
private theorem endpoint_7_74_p4 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 0 4 213796562969633364 = some 213796562969633364 :=
  join_receipt_window endpoint_7_74_flag endpoint_7_74_sources 0 2 2 213796562969633364 213796562969633364 213796562969633364 endpoint_7_74_w0 endpoint_7_74_w2
private theorem endpoint_7_74_w4 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 4 2 213796562969633364 = some 213796562969633364 := by decide +kernel
private theorem endpoint_7_74_p6 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 0 6 213796562969633364 = some 213796562969633364 :=
  join_receipt_window endpoint_7_74_flag endpoint_7_74_sources 0 4 2 213796562969633364 213796562969633364 213796562969633364 endpoint_7_74_p4 endpoint_7_74_w4
def endpoint_7_74 : CertifiedEndpoint :=
  ⟨⟨7, 74, 2827⟩, 213796562969633364, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_7_74_flag endpoint_7_74_sources 6 213796562969633364 213796562969633364 rfl endpoint_7_74_base endpoint_7_74_p6) (by decide)⟩
private def endpoint_7_75_flag : Flag := ⟨7, 75, 2740⟩
private def endpoint_7_75_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_7_75_base : receiptBase endpoint_7_75_flag endpoint_7_75_sources = some 209784343841368249 := by decide +kernel
private theorem endpoint_7_75_w0 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 0 2 209784343841368249 = some 209784343841368249 := by decide +kernel
private theorem endpoint_7_75_w2 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 2 2 209784343841368249 = some 209784343841368249 := by decide +kernel
private theorem endpoint_7_75_p4 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 0 4 209784343841368249 = some 209784343841368249 :=
  join_receipt_window endpoint_7_75_flag endpoint_7_75_sources 0 2 2 209784343841368249 209784343841368249 209784343841368249 endpoint_7_75_w0 endpoint_7_75_w2
private theorem endpoint_7_75_w4 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 4 2 209784343841368249 = some 209784343841368249 := by decide +kernel
private theorem endpoint_7_75_p6 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 0 6 209784343841368249 = some 209784343841368249 :=
  join_receipt_window endpoint_7_75_flag endpoint_7_75_sources 0 4 2 209784343841368249 209784343841368249 209784343841368249 endpoint_7_75_p4 endpoint_7_75_w4
def endpoint_7_75 : CertifiedEndpoint :=
  ⟨⟨7, 75, 2740⟩, 209784343841368249, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_7_75_flag endpoint_7_75_sources 6 209784343841368249 209784343841368249 rfl endpoint_7_75_base endpoint_7_75_p6) (by decide)⟩
private def endpoint_7_76_flag : Flag := ⟨7, 76, 2649⟩
private def endpoint_7_76_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_7_76_base : receiptBase endpoint_7_76_flag endpoint_7_76_sources = some 209096499582613571 := by decide +kernel
private theorem endpoint_7_76_w0 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 0 2 209096499582613571 = some 209096499582613571 := by decide +kernel
private theorem endpoint_7_76_w2 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 2 2 209096499582613571 = some 209096499582613571 := by decide +kernel
private theorem endpoint_7_76_p4 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 0 4 209096499582613571 = some 209096499582613571 :=
  join_receipt_window endpoint_7_76_flag endpoint_7_76_sources 0 2 2 209096499582613571 209096499582613571 209096499582613571 endpoint_7_76_w0 endpoint_7_76_w2
private theorem endpoint_7_76_w4 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 4 2 209096499582613571 = some 209096499582613571 := by decide +kernel
private theorem endpoint_7_76_p6 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 0 6 209096499582613571 = some 209096499582613571 :=
  join_receipt_window endpoint_7_76_flag endpoint_7_76_sources 0 4 2 209096499582613571 209096499582613571 209096499582613571 endpoint_7_76_p4 endpoint_7_76_w4
def endpoint_7_76 : CertifiedEndpoint :=
  ⟨⟨7, 76, 2649⟩, 209096499582613571, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_7_76_flag endpoint_7_76_sources 6 209096499582613571 209096499582613571 rfl endpoint_7_76_base endpoint_7_76_p6) (by decide)⟩
private def endpoint_7_77_flag : Flag := ⟨7, 77, 2556⟩
private def endpoint_7_77_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_7_77_base : receiptBase endpoint_7_77_flag endpoint_7_77_sources = some 204246928296147799 := by decide +kernel
private theorem endpoint_7_77_w0 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 0 2 204246928296147799 = some 204246928296147799 := by decide +kernel
private theorem endpoint_7_77_w2 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 2 2 204246928296147799 = some 204246928296147799 := by decide +kernel
private theorem endpoint_7_77_p4 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 0 4 204246928296147799 = some 204246928296147799 :=
  join_receipt_window endpoint_7_77_flag endpoint_7_77_sources 0 2 2 204246928296147799 204246928296147799 204246928296147799 endpoint_7_77_w0 endpoint_7_77_w2
private theorem endpoint_7_77_w4 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 4 2 204246928296147799 = some 204246928296147799 := by decide +kernel
private theorem endpoint_7_77_p6 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 0 6 204246928296147799 = some 204246928296147799 :=
  join_receipt_window endpoint_7_77_flag endpoint_7_77_sources 0 4 2 204246928296147799 204246928296147799 204246928296147799 endpoint_7_77_p4 endpoint_7_77_w4
def endpoint_7_77 : CertifiedEndpoint :=
  ⟨⟨7, 77, 2556⟩, 204246928296147799, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_7_77_flag endpoint_7_77_sources 6 204246928296147799 204246928296147799 rfl endpoint_7_77_base endpoint_7_77_p6) (by decide)⟩
private def endpoint_7_78_flag : Flag := ⟨7, 78, 2459⟩
private def endpoint_7_78_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_7_78_base : receiptBase endpoint_7_78_flag endpoint_7_78_sources = some 198904997883465586 := by decide +kernel
private theorem endpoint_7_78_w0 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 0 2 198904997883465586 = some 198904997883465586 := by decide +kernel
private theorem endpoint_7_78_w2 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 2 2 198904997883465586 = some 198904997883465586 := by decide +kernel
private theorem endpoint_7_78_p4 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 0 4 198904997883465586 = some 198904997883465586 :=
  join_receipt_window endpoint_7_78_flag endpoint_7_78_sources 0 2 2 198904997883465586 198904997883465586 198904997883465586 endpoint_7_78_w0 endpoint_7_78_w2
private theorem endpoint_7_78_w4 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 4 2 198904997883465586 = some 198904997883465586 := by decide +kernel
private theorem endpoint_7_78_p6 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 0 6 198904997883465586 = some 198904997883465586 :=
  join_receipt_window endpoint_7_78_flag endpoint_7_78_sources 0 4 2 198904997883465586 198904997883465586 198904997883465586 endpoint_7_78_p4 endpoint_7_78_w4
def endpoint_7_78 : CertifiedEndpoint :=
  ⟨⟨7, 78, 2459⟩, 198904997883465586, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_7_78_flag endpoint_7_78_sources 6 198904997883465586 198904997883465586 rfl endpoint_7_78_base endpoint_7_78_p6) (by decide)⟩
private def endpoint_7_79_flag : Flag := ⟨7, 79, 2359⟩
private def endpoint_7_79_sources : Sources := ⟨contact11, contact11, contact13⟩
private theorem endpoint_7_79_base : receiptBase endpoint_7_79_flag endpoint_7_79_sources = some 193143335895451831 := by decide +kernel
private theorem endpoint_7_79_w0 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 0 2 193143335895451831 = some 193143335895451831 := by decide +kernel
private theorem endpoint_7_79_w2 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 2 2 193143335895451831 = some 193143335895451831 := by decide +kernel
private theorem endpoint_7_79_p4 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 0 4 193143335895451831 = some 193143335895451831 :=
  join_receipt_window endpoint_7_79_flag endpoint_7_79_sources 0 2 2 193143335895451831 193143335895451831 193143335895451831 endpoint_7_79_w0 endpoint_7_79_w2
private theorem endpoint_7_79_w4 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 4 2 193143335895451831 = some 193143335895451831 := by decide +kernel
private theorem endpoint_7_79_p6 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 0 6 193143335895451831 = some 193143335895451831 :=
  join_receipt_window endpoint_7_79_flag endpoint_7_79_sources 0 4 2 193143335895451831 193143335895451831 193143335895451831 endpoint_7_79_p4 endpoint_7_79_w4
def endpoint_7_79 : CertifiedEndpoint :=
  ⟨⟨7, 79, 2359⟩, 193143335895451831, .terminal ⟨contact11, contact11, contact13⟩ (finish_receipt_window endpoint_7_79_flag endpoint_7_79_sources 6 193143335895451831 193143335895451831 rfl endpoint_7_79_base endpoint_7_79_p6) (by decide)⟩
private def endpoint_7_80_flag : Flag := ⟨7, 80, 2256⟩
private def endpoint_7_80_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_7_80_base : receiptBase endpoint_7_80_flag endpoint_7_80_sources = some 189009882051854930 := by decide +kernel
private theorem endpoint_7_80_w0 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 0 2 189009882051854930 = some 189009882051854930 := by decide +kernel
private theorem endpoint_7_80_w2 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 2 2 189009882051854930 = some 189009882051854930 := by decide +kernel
private theorem endpoint_7_80_p4 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 0 4 189009882051854930 = some 189009882051854930 :=
  join_receipt_window endpoint_7_80_flag endpoint_7_80_sources 0 2 2 189009882051854930 189009882051854930 189009882051854930 endpoint_7_80_w0 endpoint_7_80_w2
private theorem endpoint_7_80_w4 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 4 2 189009882051854930 = some 189009882051854930 := by decide +kernel
private theorem endpoint_7_80_p6 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 0 6 189009882051854930 = some 189009882051854930 :=
  join_receipt_window endpoint_7_80_flag endpoint_7_80_sources 0 4 2 189009882051854930 189009882051854930 189009882051854930 endpoint_7_80_p4 endpoint_7_80_w4
def endpoint_7_80 : CertifiedEndpoint :=
  ⟨⟨7, 80, 2256⟩, 189009882051854930, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_7_80_flag endpoint_7_80_sources 6 189009882051854930 189009882051854930 rfl endpoint_7_80_base endpoint_7_80_p6) (by decide)⟩
private def endpoint_7_81_flag : Flag := ⟨7, 81, 2150⟩
private def endpoint_7_81_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_7_81_base : receiptBase endpoint_7_81_flag endpoint_7_81_sources = some 182224558757115070 := by decide +kernel
private theorem endpoint_7_81_w0 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 0 2 182224558757115070 = some 182224558757115070 := by decide +kernel
private theorem endpoint_7_81_w2 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 2 2 182224558757115070 = some 182224558757115070 := by decide +kernel
private theorem endpoint_7_81_p4 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 0 4 182224558757115070 = some 182224558757115070 :=
  join_receipt_window endpoint_7_81_flag endpoint_7_81_sources 0 2 2 182224558757115070 182224558757115070 182224558757115070 endpoint_7_81_w0 endpoint_7_81_w2
private theorem endpoint_7_81_w4 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 4 2 182224558757115070 = some 182224558757115070 := by decide +kernel
private theorem endpoint_7_81_p6 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 0 6 182224558757115070 = some 182224558757115070 :=
  join_receipt_window endpoint_7_81_flag endpoint_7_81_sources 0 4 2 182224558757115070 182224558757115070 182224558757115070 endpoint_7_81_p4 endpoint_7_81_w4
def endpoint_7_81 : CertifiedEndpoint :=
  ⟨⟨7, 81, 2150⟩, 182224558757115070, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_7_81_flag endpoint_7_81_sources 6 182224558757115070 182224558757115070 rfl endpoint_7_81_base endpoint_7_81_p6) (by decide)⟩
def endpoint_7_82 : CertifiedEndpoint :=
  ⟨⟨7, 82, 2041⟩, 262410391984007269, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_83 : CertifiedEndpoint :=
  ⟨⟨7, 83, 1928⟩, 250676764442373399, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_84 : CertifiedEndpoint :=
  ⟨⟨7, 84, 1812⟩, 238156837163473180, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_85 : CertifiedEndpoint :=
  ⟨⟨7, 85, 1693⟩, 224835457116939106, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_86 : CertifiedEndpoint :=
  ⟨⟨7, 86, 1571⟩, 210697471272403671, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_87 : CertifiedEndpoint :=
  ⟨⟨7, 87, 1446⟩, 195727726599499369, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_88 : CertifiedEndpoint :=
  ⟨⟨7, 88, 1317⟩, 179769633175029681, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_89 : CertifiedEndpoint :=
  ⟨⟨7, 89, 1185⟩, 162946107521374446, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_90 : CertifiedEndpoint :=
  ⟨⟨7, 90, 1050⟩, 145241996608166158, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_91 : CertifiedEndpoint :=
  ⟨⟨7, 91, 912⟩, 126642147405037311, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_92 : CertifiedEndpoint :=
  ⟨⟨7, 92, 770⟩, 106983235308628050, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_93 : CertifiedEndpoint :=
  ⟨⟨7, 93, 626⟩, 86544766764514733, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_94 : CertifiedEndpoint :=
  ⟨⟨7, 94, 478⟩, 65013561926304322, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_95 : CertifiedEndpoint :=
  ⟨⟨7, 95, 327⟩, 42522639336621660, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_96 : CertifiedEndpoint :=
  ⟨⟨7, 96, 172⟩, 18901939711943556, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_8 : CertifiedEndpoint :=
  ⟨⟨8, 8, 5100⟩, 48042905671151484, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_9 : CertifiedEndpoint :=
  ⟨⟨8, 9, 5079⟩, 51023509175194398, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_10 : CertifiedEndpoint :=
  ⟨⟨8, 10, 5059⟩, 53988461431156121, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_11 : CertifiedEndpoint :=
  ⟨⟨8, 11, 5038⟩, 63524311480460923, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_12 : CertifiedEndpoint :=
  ⟨⟨8, 12, 5017⟩, 72976682431852027, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_13 : CertifiedEndpoint :=
  ⟨⟨8, 13, 4996⟩, 82345574285329433, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_14 : CertifiedEndpoint :=
  ⟨⟨8, 14, 4974⟩, 91612535372160294, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_15 : CertifiedEndpoint :=
  ⟨⟨8, 15, 4953⟩, 100812527655440218, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_16 : CertifiedEndpoint :=
  ⟨⟨8, 16, 4931⟩, 109906706423333425, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_17 : CertifiedEndpoint :=
  ⟨⟨8, 17, 4909⟩, 118913523344572762, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_18 : CertifiedEndpoint :=
  ⟨⟨8, 18, 4887⟩, 127832978419158229, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_19 : CertifiedEndpoint :=
  ⟨⟨8, 19, 4864⟩, 136636913106506549, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_20 : CertifiedEndpoint :=
  ⟨⟨8, 20, 4842⟩, 145379703113414190, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_21 : CertifiedEndpoint :=
  ⟨⟨8, 21, 4819⟩, 154003089984344512, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_22 : CertifiedEndpoint :=
  ⟨⟨8, 22, 4796⟩, 162535232259880792, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_23 : CertifiedEndpoint :=
  ⟨⟨8, 23, 4772⟩, 170940205901959409, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_24 : CertifiedEndpoint :=
  ⟨⟨8, 24, 4749⟩, 179287917612337519, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_25 : CertifiedEndpoint :=
  ⟨⟨8, 25, 4725⟩, 187504577940517794, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_26 : CertifiedEndpoint :=
  ⟨⟨8, 26, 4701⟩, 195626110924563855, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_27 : CertifiedEndpoint :=
  ⟨⟨8, 27, 4677⟩, 203652516564475702, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_28 : CertifiedEndpoint :=
  ⟨⟨8, 28, 4652⟩, 211538163950339284, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_29 : CertifiedEndpoint :=
  ⟨⟨8, 29, 4627⟩, 219324801243328480, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_30 : CertifiedEndpoint :=
  ⟨⟨8, 30, 4602⟩, 227012428443443290, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_31 : CertifiedEndpoint :=
  ⟨⟨8, 31, 4577⟩, 234601045550683714, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_32 : CertifiedEndpoint :=
  ⟨⟨8, 32, 4551⟩, 242037256157655357, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_33 : CertifiedEndpoint :=
  ⟨⟨8, 33, 4525⟩, 249370573923012442, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_34 : CertifiedEndpoint :=
  ⟨⟨8, 34, 4498⟩, 256543719690620402, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_35 : CertifiedEndpoint :=
  ⟨⟨8, 35, 4471⟩, 263610089867873632, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_8_36_flag : Flag := ⟨8, 36, 4444⟩
private def endpoint_8_36_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_36_base : receiptBase endpoint_8_36_flag endpoint_8_36_sources = some 183526271978631762 := by decide +kernel
private theorem endpoint_8_36_w0 : receiptWindow endpoint_8_36_flag endpoint_8_36_sources 0 2 183526271978631762 = some 183526271978631762 := by decide +kernel
private theorem endpoint_8_36_w2 : receiptWindow endpoint_8_36_flag endpoint_8_36_sources 2 2 183526271978631762 = some 183526271978631762 := by decide +kernel
private theorem endpoint_8_36_p4 : receiptWindow endpoint_8_36_flag endpoint_8_36_sources 0 4 183526271978631762 = some 183526271978631762 :=
  join_receipt_window endpoint_8_36_flag endpoint_8_36_sources 0 2 2 183526271978631762 183526271978631762 183526271978631762 endpoint_8_36_w0 endpoint_8_36_w2
private theorem endpoint_8_36_w4 : receiptWindow endpoint_8_36_flag endpoint_8_36_sources 4 2 183526271978631762 = some 183526271978631762 := by decide +kernel
private theorem endpoint_8_36_p6 : receiptWindow endpoint_8_36_flag endpoint_8_36_sources 0 6 183526271978631762 = some 183526271978631762 :=
  join_receipt_window endpoint_8_36_flag endpoint_8_36_sources 0 4 2 183526271978631762 183526271978631762 183526271978631762 endpoint_8_36_p4 endpoint_8_36_w4
private theorem endpoint_8_36_w6 : receiptWindow endpoint_8_36_flag endpoint_8_36_sources 6 1 183526271978631762 = some 183526271978631762 := by decide +kernel
private theorem endpoint_8_36_p7 : receiptWindow endpoint_8_36_flag endpoint_8_36_sources 0 7 183526271978631762 = some 183526271978631762 :=
  join_receipt_window endpoint_8_36_flag endpoint_8_36_sources 0 6 1 183526271978631762 183526271978631762 183526271978631762 endpoint_8_36_p6 endpoint_8_36_w6
def endpoint_8_36 : CertifiedEndpoint :=
  ⟨⟨8, 36, 4444⟩, 183526271978631762, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_36_flag endpoint_8_36_sources 7 183526271978631762 183526271978631762 rfl endpoint_8_36_base endpoint_8_36_p7) (by decide)⟩
private def endpoint_8_37_flag : Flag := ⟨8, 37, 4416⟩
private def endpoint_8_37_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_37_base : receiptBase endpoint_8_37_flag endpoint_8_37_sources = some 186571083292318446 := by decide +kernel
private theorem endpoint_8_37_w0 : receiptWindow endpoint_8_37_flag endpoint_8_37_sources 0 2 186571083292318446 = some 186571083292318446 := by decide +kernel
private theorem endpoint_8_37_w2 : receiptWindow endpoint_8_37_flag endpoint_8_37_sources 2 2 186571083292318446 = some 186571083292318446 := by decide +kernel
private theorem endpoint_8_37_p4 : receiptWindow endpoint_8_37_flag endpoint_8_37_sources 0 4 186571083292318446 = some 186571083292318446 :=
  join_receipt_window endpoint_8_37_flag endpoint_8_37_sources 0 2 2 186571083292318446 186571083292318446 186571083292318446 endpoint_8_37_w0 endpoint_8_37_w2
private theorem endpoint_8_37_w4 : receiptWindow endpoint_8_37_flag endpoint_8_37_sources 4 2 186571083292318446 = some 186571083292318446 := by decide +kernel
private theorem endpoint_8_37_p6 : receiptWindow endpoint_8_37_flag endpoint_8_37_sources 0 6 186571083292318446 = some 186571083292318446 :=
  join_receipt_window endpoint_8_37_flag endpoint_8_37_sources 0 4 2 186571083292318446 186571083292318446 186571083292318446 endpoint_8_37_p4 endpoint_8_37_w4
private theorem endpoint_8_37_w6 : receiptWindow endpoint_8_37_flag endpoint_8_37_sources 6 1 186571083292318446 = some 186571083292318446 := by decide +kernel
private theorem endpoint_8_37_p7 : receiptWindow endpoint_8_37_flag endpoint_8_37_sources 0 7 186571083292318446 = some 186571083292318446 :=
  join_receipt_window endpoint_8_37_flag endpoint_8_37_sources 0 6 1 186571083292318446 186571083292318446 186571083292318446 endpoint_8_37_p6 endpoint_8_37_w6
def endpoint_8_37 : CertifiedEndpoint :=
  ⟨⟨8, 37, 4416⟩, 186571083292318446, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_37_flag endpoint_8_37_sources 7 186571083292318446 186571083292318446 rfl endpoint_8_37_base endpoint_8_37_p7) (by decide)⟩
private def endpoint_8_38_flag : Flag := ⟨8, 38, 4388⟩
private def endpoint_8_38_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_38_base : receiptBase endpoint_8_38_flag endpoint_8_38_sources = some 189562726102297506 := by decide +kernel
private theorem endpoint_8_38_w0 : receiptWindow endpoint_8_38_flag endpoint_8_38_sources 0 2 189562726102297506 = some 189562726102297506 := by decide +kernel
private theorem endpoint_8_38_w2 : receiptWindow endpoint_8_38_flag endpoint_8_38_sources 2 2 189562726102297506 = some 189562726102297506 := by decide +kernel
private theorem endpoint_8_38_p4 : receiptWindow endpoint_8_38_flag endpoint_8_38_sources 0 4 189562726102297506 = some 189562726102297506 :=
  join_receipt_window endpoint_8_38_flag endpoint_8_38_sources 0 2 2 189562726102297506 189562726102297506 189562726102297506 endpoint_8_38_w0 endpoint_8_38_w2
private theorem endpoint_8_38_w4 : receiptWindow endpoint_8_38_flag endpoint_8_38_sources 4 2 189562726102297506 = some 189562726102297506 := by decide +kernel
private theorem endpoint_8_38_p6 : receiptWindow endpoint_8_38_flag endpoint_8_38_sources 0 6 189562726102297506 = some 189562726102297506 :=
  join_receipt_window endpoint_8_38_flag endpoint_8_38_sources 0 4 2 189562726102297506 189562726102297506 189562726102297506 endpoint_8_38_p4 endpoint_8_38_w4
private theorem endpoint_8_38_w6 : receiptWindow endpoint_8_38_flag endpoint_8_38_sources 6 1 189562726102297506 = some 189562726102297506 := by decide +kernel
private theorem endpoint_8_38_p7 : receiptWindow endpoint_8_38_flag endpoint_8_38_sources 0 7 189562726102297506 = some 189562726102297506 :=
  join_receipt_window endpoint_8_38_flag endpoint_8_38_sources 0 6 1 189562726102297506 189562726102297506 189562726102297506 endpoint_8_38_p6 endpoint_8_38_w6
def endpoint_8_38 : CertifiedEndpoint :=
  ⟨⟨8, 38, 4388⟩, 189562726102297506, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_38_flag endpoint_8_38_sources 7 189562726102297506 189562726102297506 rfl endpoint_8_38_base endpoint_8_38_p7) (by decide)⟩
private def endpoint_8_39_flag : Flag := ⟨8, 39, 4360⟩
private def endpoint_8_39_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_39_base : receiptBase endpoint_8_39_flag endpoint_8_39_sources = some 192501200408568941 := by decide +kernel
private theorem endpoint_8_39_w0 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 2 192501200408568941 = some 192501200408568941 := by decide +kernel
private theorem endpoint_8_39_w2 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 2 2 192501200408568941 = some 192501200408568941 := by decide +kernel
private theorem endpoint_8_39_p4 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 4 192501200408568941 = some 192501200408568941 :=
  join_receipt_window endpoint_8_39_flag endpoint_8_39_sources 0 2 2 192501200408568941 192501200408568941 192501200408568941 endpoint_8_39_w0 endpoint_8_39_w2
private theorem endpoint_8_39_w4 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 4 2 192501200408568941 = some 192501200408568941 := by decide +kernel
private theorem endpoint_8_39_p6 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 6 192501200408568941 = some 192501200408568941 :=
  join_receipt_window endpoint_8_39_flag endpoint_8_39_sources 0 4 2 192501200408568941 192501200408568941 192501200408568941 endpoint_8_39_p4 endpoint_8_39_w4
private theorem endpoint_8_39_w6 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 6 1 192501200408568941 = some 192501200408568941 := by decide +kernel
private theorem endpoint_8_39_p7 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 7 192501200408568941 = some 192501200408568941 :=
  join_receipt_window endpoint_8_39_flag endpoint_8_39_sources 0 6 1 192501200408568941 192501200408568941 192501200408568941 endpoint_8_39_p6 endpoint_8_39_w6
def endpoint_8_39 : CertifiedEndpoint :=
  ⟨⟨8, 39, 4360⟩, 192501200408568941, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_39_flag endpoint_8_39_sources 7 192501200408568941 192501200408568941 rfl endpoint_8_39_base endpoint_8_39_p7) (by decide)⟩
private def endpoint_8_40_flag : Flag := ⟨8, 40, 4331⟩
private def endpoint_8_40_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_40_base : receiptBase endpoint_8_40_flag endpoint_8_40_sources = some 195342032488347567 := by decide +kernel
private theorem endpoint_8_40_w0 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 2 195342032488347567 = some 195342032488347567 := by decide +kernel
private theorem endpoint_8_40_w2 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 2 2 195342032488347567 = some 195342032488347567 := by decide +kernel
private theorem endpoint_8_40_p4 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 4 195342032488347567 = some 195342032488347567 :=
  join_receipt_window endpoint_8_40_flag endpoint_8_40_sources 0 2 2 195342032488347567 195342032488347567 195342032488347567 endpoint_8_40_w0 endpoint_8_40_w2
private theorem endpoint_8_40_w4 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 4 2 195342032488347567 = some 195342032488347567 := by decide +kernel
private theorem endpoint_8_40_p6 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 6 195342032488347567 = some 195342032488347567 :=
  join_receipt_window endpoint_8_40_flag endpoint_8_40_sources 0 4 2 195342032488347567 195342032488347567 195342032488347567 endpoint_8_40_p4 endpoint_8_40_w4
private theorem endpoint_8_40_w6 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 6 1 195342032488347567 = some 195342032488347567 := by decide +kernel
private theorem endpoint_8_40_p7 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 7 195342032488347567 = some 195342032488347567 :=
  join_receipt_window endpoint_8_40_flag endpoint_8_40_sources 0 6 1 195342032488347567 195342032488347567 195342032488347567 endpoint_8_40_p6 endpoint_8_40_w6
def endpoint_8_40 : CertifiedEndpoint :=
  ⟨⟨8, 40, 4331⟩, 195342032488347567, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_40_flag endpoint_8_40_sources 7 195342032488347567 195342032488347567 rfl endpoint_8_40_base endpoint_8_40_p7) (by decide)⟩
private def endpoint_8_41_flag : Flag := ⟨8, 41, 4302⟩
private def endpoint_8_41_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_41_base : receiptBase endpoint_8_41_flag endpoint_8_41_sources = some 198127830502884967 := by decide +kernel
private theorem endpoint_8_41_w0 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 2 198127830502884967 = some 198127830502884967 := by decide +kernel
private theorem endpoint_8_41_w2 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 2 2 198127830502884967 = some 198127830502884967 := by decide +kernel
private theorem endpoint_8_41_p4 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 4 198127830502884967 = some 198127830502884967 :=
  join_receipt_window endpoint_8_41_flag endpoint_8_41_sources 0 2 2 198127830502884967 198127830502884967 198127830502884967 endpoint_8_41_w0 endpoint_8_41_w2
private theorem endpoint_8_41_w4 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 4 2 198127830502884967 = some 198127830502884967 := by decide +kernel
private theorem endpoint_8_41_p6 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 6 198127830502884967 = some 198127830502884967 :=
  join_receipt_window endpoint_8_41_flag endpoint_8_41_sources 0 4 2 198127830502884967 198127830502884967 198127830502884967 endpoint_8_41_p4 endpoint_8_41_w4
private theorem endpoint_8_41_w6 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 6 1 198127830502884967 = some 198127830502884967 := by decide +kernel
private theorem endpoint_8_41_p7 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 7 198127830502884967 = some 198127830502884967 :=
  join_receipt_window endpoint_8_41_flag endpoint_8_41_sources 0 6 1 198127830502884967 198127830502884967 198127830502884967 endpoint_8_41_p6 endpoint_8_41_w6
def endpoint_8_41 : CertifiedEndpoint :=
  ⟨⟨8, 41, 4302⟩, 198127830502884967, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_41_flag endpoint_8_41_sources 7 198127830502884967 198127830502884967 rfl endpoint_8_41_base endpoint_8_41_p7) (by decide)⟩
private def endpoint_8_42_flag : Flag := ⟨8, 42, 4272⟩
private def endpoint_8_42_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_42_base : receiptBase endpoint_8_42_flag endpoint_8_42_sources = some 200812255167862356 := by decide +kernel
private theorem endpoint_8_42_w0 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 2 200812255167862356 = some 200812255167862356 := by decide +kernel
private theorem endpoint_8_42_w2 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 2 2 200812255167862356 = some 200812255167862356 := by decide +kernel
private theorem endpoint_8_42_p4 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 4 200812255167862356 = some 200812255167862356 :=
  join_receipt_window endpoint_8_42_flag endpoint_8_42_sources 0 2 2 200812255167862356 200812255167862356 200812255167862356 endpoint_8_42_w0 endpoint_8_42_w2
private theorem endpoint_8_42_w4 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 4 2 200812255167862356 = some 200812255167862356 := by decide +kernel
private theorem endpoint_8_42_p6 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 6 200812255167862356 = some 200812255167862356 :=
  join_receipt_window endpoint_8_42_flag endpoint_8_42_sources 0 4 2 200812255167862356 200812255167862356 200812255167862356 endpoint_8_42_p4 endpoint_8_42_w4
private theorem endpoint_8_42_w6 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 6 1 200812255167862356 = some 200812255167862356 := by decide +kernel
private theorem endpoint_8_42_p7 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 7 200812255167862356 = some 200812255167862356 :=
  join_receipt_window endpoint_8_42_flag endpoint_8_42_sources 0 6 1 200812255167862356 200812255167862356 200812255167862356 endpoint_8_42_p6 endpoint_8_42_w6
def endpoint_8_42 : CertifiedEndpoint :=
  ⟨⟨8, 42, 4272⟩, 200812255167862356, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_42_flag endpoint_8_42_sources 7 200812255167862356 200812255167862356 rfl endpoint_8_42_base endpoint_8_42_p7) (by decide)⟩
private def endpoint_8_43_flag : Flag := ⟨8, 43, 4242⟩
private def endpoint_8_43_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_43_base : receiptBase endpoint_8_43_flag endpoint_8_43_sources = some 203439780206064918 := by decide +kernel
private theorem endpoint_8_43_w0 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 2 203439780206064918 = some 203439780206064918 := by decide +kernel
private theorem endpoint_8_43_w2 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 2 2 203439780206064918 = some 203439780206064918 := by decide +kernel
private theorem endpoint_8_43_p4 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 4 203439780206064918 = some 203439780206064918 :=
  join_receipt_window endpoint_8_43_flag endpoint_8_43_sources 0 2 2 203439780206064918 203439780206064918 203439780206064918 endpoint_8_43_w0 endpoint_8_43_w2
private theorem endpoint_8_43_w4 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 4 2 203439780206064918 = some 203439780206064918 := by decide +kernel
private theorem endpoint_8_43_p6 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 6 203439780206064918 = some 203439780206064918 :=
  join_receipt_window endpoint_8_43_flag endpoint_8_43_sources 0 4 2 203439780206064918 203439780206064918 203439780206064918 endpoint_8_43_p4 endpoint_8_43_w4
private theorem endpoint_8_43_w6 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 6 1 203439780206064918 = some 203439780206064918 := by decide +kernel
private theorem endpoint_8_43_p7 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 7 203439780206064918 = some 203439780206064918 :=
  join_receipt_window endpoint_8_43_flag endpoint_8_43_sources 0 6 1 203439780206064918 203439780206064918 203439780206064918 endpoint_8_43_p6 endpoint_8_43_w6
def endpoint_8_43 : CertifiedEndpoint :=
  ⟨⟨8, 43, 4242⟩, 203439780206064918, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_43_flag endpoint_8_43_sources 7 203439780206064918 203439780206064918 rfl endpoint_8_43_base endpoint_8_43_p7) (by decide)⟩
private def endpoint_8_44_flag : Flag := ⟨8, 44, 4211⟩
private def endpoint_8_44_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_44_base : receiptBase endpoint_8_44_flag endpoint_8_44_sources = some 205962200771640268 := by decide +kernel
private theorem endpoint_8_44_w0 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 2 205962200771640268 = some 205962200771640268 := by decide +kernel
private theorem endpoint_8_44_w2 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 2 2 205962200771640268 = some 205962200771640268 := by decide +kernel
private theorem endpoint_8_44_p4 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 4 205962200771640268 = some 205962200771640268 :=
  join_receipt_window endpoint_8_44_flag endpoint_8_44_sources 0 2 2 205962200771640268 205962200771640268 205962200771640268 endpoint_8_44_w0 endpoint_8_44_w2
private theorem endpoint_8_44_w4 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 4 2 205962200771640268 = some 205962200771640268 := by decide +kernel
private theorem endpoint_8_44_p6 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 6 205962200771640268 = some 205962200771640268 :=
  join_receipt_window endpoint_8_44_flag endpoint_8_44_sources 0 4 2 205962200771640268 205962200771640268 205962200771640268 endpoint_8_44_p4 endpoint_8_44_w4
private theorem endpoint_8_44_w6 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 6 1 205962200771640268 = some 205962200771640268 := by decide +kernel
private theorem endpoint_8_44_p7 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 7 205962200771640268 = some 205962200771640268 :=
  join_receipt_window endpoint_8_44_flag endpoint_8_44_sources 0 6 1 205962200771640268 205962200771640268 205962200771640268 endpoint_8_44_p6 endpoint_8_44_w6
def endpoint_8_44 : CertifiedEndpoint :=
  ⟨⟨8, 44, 4211⟩, 205962200771640268, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_44_flag endpoint_8_44_sources 7 205962200771640268 205962200771640268 rfl endpoint_8_44_base endpoint_8_44_p7) (by decide)⟩
private def endpoint_8_45_flag : Flag := ⟨8, 45, 4180⟩
private def endpoint_8_45_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_45_base : receiptBase endpoint_8_45_flag endpoint_8_45_sources = some 208425856148907190 := by decide +kernel
private theorem endpoint_8_45_w0 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 2 208425856148907190 = some 208425856148907190 := by decide +kernel
private theorem endpoint_8_45_w2 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 2 2 208425856148907190 = some 208425856148907190 := by decide +kernel
private theorem endpoint_8_45_p4 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 4 208425856148907190 = some 208425856148907190 :=
  join_receipt_window endpoint_8_45_flag endpoint_8_45_sources 0 2 2 208425856148907190 208425856148907190 208425856148907190 endpoint_8_45_w0 endpoint_8_45_w2
private theorem endpoint_8_45_w4 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 4 2 208425856148907190 = some 208425856148907190 := by decide +kernel
private theorem endpoint_8_45_p6 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 6 208425856148907190 = some 208425856148907190 :=
  join_receipt_window endpoint_8_45_flag endpoint_8_45_sources 0 4 2 208425856148907190 208425856148907190 208425856148907190 endpoint_8_45_p4 endpoint_8_45_w4
private theorem endpoint_8_45_w6 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 6 1 208425856148907190 = some 208425856148907190 := by decide +kernel
private theorem endpoint_8_45_p7 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 7 208425856148907190 = some 208425856148907190 :=
  join_receipt_window endpoint_8_45_flag endpoint_8_45_sources 0 6 1 208425856148907190 208425856148907190 208425856148907190 endpoint_8_45_p6 endpoint_8_45_w6
def endpoint_8_45 : CertifiedEndpoint :=
  ⟨⟨8, 45, 4180⟩, 208425856148907190, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_45_flag endpoint_8_45_sources 7 208425856148907190 208425856148907190 rfl endpoint_8_45_base endpoint_8_45_p7) (by decide)⟩
private def endpoint_8_46_flag : Flag := ⟨8, 46, 4148⟩
private def endpoint_8_46_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_46_base : receiptBase endpoint_8_46_flag endpoint_8_46_sources = some 210780675930479698 := by decide +kernel
private theorem endpoint_8_46_w0 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 2 210780675930479698 = some 210780675930479698 := by decide +kernel
private theorem endpoint_8_46_w2 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 2 2 210780675930479698 = some 210780675930479698 := by decide +kernel
private theorem endpoint_8_46_p4 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 4 210780675930479698 = some 210780675930479698 :=
  join_receipt_window endpoint_8_46_flag endpoint_8_46_sources 0 2 2 210780675930479698 210780675930479698 210780675930479698 endpoint_8_46_w0 endpoint_8_46_w2
private theorem endpoint_8_46_w4 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 4 2 210780675930479698 = some 210780675930479698 := by decide +kernel
private theorem endpoint_8_46_p6 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 6 210780675930479698 = some 210780675930479698 :=
  join_receipt_window endpoint_8_46_flag endpoint_8_46_sources 0 4 2 210780675930479698 210780675930479698 210780675930479698 endpoint_8_46_p4 endpoint_8_46_w4
private theorem endpoint_8_46_w6 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 6 1 210780675930479698 = some 210780675930479698 := by decide +kernel
private theorem endpoint_8_46_p7 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 7 210780675930479698 = some 210780675930479698 :=
  join_receipt_window endpoint_8_46_flag endpoint_8_46_sources 0 6 1 210780675930479698 210780675930479698 210780675930479698 endpoint_8_46_p6 endpoint_8_46_w6
def endpoint_8_46 : CertifiedEndpoint :=
  ⟨⟨8, 46, 4148⟩, 210780675930479698, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_46_flag endpoint_8_46_sources 7 210780675930479698 210780675930479698 rfl endpoint_8_46_base endpoint_8_46_p7) (by decide)⟩
private def endpoint_8_47_flag : Flag := ⟨8, 47, 4115⟩
private def endpoint_8_47_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_47_base : receiptBase endpoint_8_47_flag endpoint_8_47_sources = some 213023861774057391 := by decide +kernel
private theorem endpoint_8_47_w0 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 2 213023861774057391 = some 213023861774057391 := by decide +kernel
private theorem endpoint_8_47_w2 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 2 2 213023861774057391 = some 213023861774057391 := by decide +kernel
private theorem endpoint_8_47_p4 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 4 213023861774057391 = some 213023861774057391 :=
  join_receipt_window endpoint_8_47_flag endpoint_8_47_sources 0 2 2 213023861774057391 213023861774057391 213023861774057391 endpoint_8_47_w0 endpoint_8_47_w2
private theorem endpoint_8_47_w4 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 4 2 213023861774057391 = some 213023861774057391 := by decide +kernel
private theorem endpoint_8_47_p6 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 6 213023861774057391 = some 213023861774057391 :=
  join_receipt_window endpoint_8_47_flag endpoint_8_47_sources 0 4 2 213023861774057391 213023861774057391 213023861774057391 endpoint_8_47_p4 endpoint_8_47_w4
private theorem endpoint_8_47_w6 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 6 1 213023861774057391 = some 213023861774057391 := by decide +kernel
private theorem endpoint_8_47_p7 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 7 213023861774057391 = some 213023861774057391 :=
  join_receipt_window endpoint_8_47_flag endpoint_8_47_sources 0 6 1 213023861774057391 213023861774057391 213023861774057391 endpoint_8_47_p6 endpoint_8_47_w6
def endpoint_8_47 : CertifiedEndpoint :=
  ⟨⟨8, 47, 4115⟩, 213023861774057391, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_47_flag endpoint_8_47_sources 7 213023861774057391 213023861774057391 rfl endpoint_8_47_base endpoint_8_47_p7) (by decide)⟩
private def endpoint_8_48_flag : Flag := ⟨8, 48, 4082⟩
private def endpoint_8_48_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_48_base : receiptBase endpoint_8_48_flag endpoint_8_48_sources = some 215204551306259454 := by decide +kernel
private theorem endpoint_8_48_w0 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 2 215204551306259454 = some 215204551306259454 := by decide +kernel
private theorem endpoint_8_48_w2 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 2 2 215204551306259454 = some 215204551306259454 := by decide +kernel
private theorem endpoint_8_48_p4 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 4 215204551306259454 = some 215204551306259454 :=
  join_receipt_window endpoint_8_48_flag endpoint_8_48_sources 0 2 2 215204551306259454 215204551306259454 215204551306259454 endpoint_8_48_w0 endpoint_8_48_w2
private theorem endpoint_8_48_w4 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 4 2 215204551306259454 = some 215204551306259454 := by decide +kernel
private theorem endpoint_8_48_p6 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 6 215204551306259454 = some 215204551306259454 :=
  join_receipt_window endpoint_8_48_flag endpoint_8_48_sources 0 4 2 215204551306259454 215204551306259454 215204551306259454 endpoint_8_48_p4 endpoint_8_48_w4
private theorem endpoint_8_48_w6 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 6 1 215204551306259454 = some 215204551306259454 := by decide +kernel
private theorem endpoint_8_48_p7 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 7 215204551306259454 = some 215204551306259454 :=
  join_receipt_window endpoint_8_48_flag endpoint_8_48_sources 0 6 1 215204551306259454 215204551306259454 215204551306259454 endpoint_8_48_p6 endpoint_8_48_w6
def endpoint_8_48 : CertifiedEndpoint :=
  ⟨⟨8, 48, 4082⟩, 215204551306259454, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_48_flag endpoint_8_48_sources 7 215204551306259454 215204551306259454 rfl endpoint_8_48_base endpoint_8_48_p7) (by decide)⟩
private def endpoint_8_49_flag : Flag := ⟨8, 49, 4048⟩
private def endpoint_8_49_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_49_base : receiptBase endpoint_8_49_flag endpoint_8_49_sources = some 217269875777399499 := by decide +kernel
private theorem endpoint_8_49_w0 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 2 217269875777399499 = some 217269875777399499 := by decide +kernel
private theorem endpoint_8_49_w2 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 2 2 217269875777399499 = some 217269875777399499 := by decide +kernel
private theorem endpoint_8_49_p4 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 4 217269875777399499 = some 217269875777399499 :=
  join_receipt_window endpoint_8_49_flag endpoint_8_49_sources 0 2 2 217269875777399499 217269875777399499 217269875777399499 endpoint_8_49_w0 endpoint_8_49_w2
private theorem endpoint_8_49_w4 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 4 2 217269875777399499 = some 217269875777399499 := by decide +kernel
private theorem endpoint_8_49_p6 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 6 217269875777399499 = some 217269875777399499 :=
  join_receipt_window endpoint_8_49_flag endpoint_8_49_sources 0 4 2 217269875777399499 217269875777399499 217269875777399499 endpoint_8_49_p4 endpoint_8_49_w4
private theorem endpoint_8_49_w6 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 6 1 217269875777399499 = some 217269875777399499 := by decide +kernel
private theorem endpoint_8_49_p7 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 7 217269875777399499 = some 217269875777399499 :=
  join_receipt_window endpoint_8_49_flag endpoint_8_49_sources 0 6 1 217269875777399499 217269875777399499 217269875777399499 endpoint_8_49_p6 endpoint_8_49_w6
def endpoint_8_49 : CertifiedEndpoint :=
  ⟨⟨8, 49, 4048⟩, 217269875777399499, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_49_flag endpoint_8_49_sources 7 217269875777399499 217269875777399499 rfl endpoint_8_49_base endpoint_8_49_p7) (by decide)⟩
private def endpoint_8_50_flag : Flag := ⟨8, 50, 4013⟩
private def endpoint_8_50_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_50_base : receiptBase endpoint_8_50_flag endpoint_8_50_sources = some 219217036845177126 := by decide +kernel
private theorem endpoint_8_50_w0 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 2 219217036845177126 = some 219217036845177126 := by decide +kernel
private theorem endpoint_8_50_w2 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 2 2 219217036845177126 = some 219217036845177126 := by decide +kernel
private theorem endpoint_8_50_p4 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 4 219217036845177126 = some 219217036845177126 :=
  join_receipt_window endpoint_8_50_flag endpoint_8_50_sources 0 2 2 219217036845177126 219217036845177126 219217036845177126 endpoint_8_50_w0 endpoint_8_50_w2
private theorem endpoint_8_50_w4 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 4 2 219217036845177126 = some 219217036845177126 := by decide +kernel
private theorem endpoint_8_50_p6 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 6 219217036845177126 = some 219217036845177126 :=
  join_receipt_window endpoint_8_50_flag endpoint_8_50_sources 0 4 2 219217036845177126 219217036845177126 219217036845177126 endpoint_8_50_p4 endpoint_8_50_w4
private theorem endpoint_8_50_w6 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 6 1 219217036845177126 = some 219217036845177126 := by decide +kernel
private theorem endpoint_8_50_p7 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 7 219217036845177126 = some 219217036845177126 :=
  join_receipt_window endpoint_8_50_flag endpoint_8_50_sources 0 6 1 219217036845177126 219217036845177126 219217036845177126 endpoint_8_50_p6 endpoint_8_50_w6
def endpoint_8_50 : CertifiedEndpoint :=
  ⟨⟨8, 50, 4013⟩, 219217036845177126, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_50_flag endpoint_8_50_sources 7 219217036845177126 219217036845177126 rfl endpoint_8_50_base endpoint_8_50_p7) (by decide)⟩
private def endpoint_8_51_flag : Flag := ⟨8, 51, 3978⟩
private def endpoint_8_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_51_base : receiptBase endpoint_8_51_flag endpoint_8_51_sources = some 222349448194229857 := by decide +kernel
private theorem endpoint_8_51_w0 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 2 222349448194229857 = some 222349448194229857 := by decide +kernel
private theorem endpoint_8_51_w2 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 2 2 222349448194229857 = some 222349448194229857 := by decide +kernel
private theorem endpoint_8_51_p4 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 4 222349448194229857 = some 222349448194229857 :=
  join_receipt_window endpoint_8_51_flag endpoint_8_51_sources 0 2 2 222349448194229857 222349448194229857 222349448194229857 endpoint_8_51_w0 endpoint_8_51_w2
private theorem endpoint_8_51_w4 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 4 2 222349448194229857 = some 222349448194229857 := by decide +kernel
private theorem endpoint_8_51_p6 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 6 222349448194229857 = some 222349448194229857 :=
  join_receipt_window endpoint_8_51_flag endpoint_8_51_sources 0 4 2 222349448194229857 222349448194229857 222349448194229857 endpoint_8_51_p4 endpoint_8_51_w4
private theorem endpoint_8_51_w6 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 6 1 222349448194229857 = some 222349448194229857 := by decide +kernel
private theorem endpoint_8_51_p7 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 7 222349448194229857 = some 222349448194229857 :=
  join_receipt_window endpoint_8_51_flag endpoint_8_51_sources 0 6 1 222349448194229857 222349448194229857 222349448194229857 endpoint_8_51_p6 endpoint_8_51_w6
def endpoint_8_51 : CertifiedEndpoint :=
  ⟨⟨8, 51, 3978⟩, 222349448194229857, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_51_flag endpoint_8_51_sources 7 222349448194229857 222349448194229857 rfl endpoint_8_51_base endpoint_8_51_p7) (by decide)⟩
private def endpoint_8_52_flag : Flag := ⟨8, 52, 3941⟩
private def endpoint_8_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_52_base : receiptBase endpoint_8_52_flag endpoint_8_52_sources = some 224053547472629313 := by decide +kernel
private theorem endpoint_8_52_w0 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 2 224053547472629313 = some 224053547472629313 := by decide +kernel
private theorem endpoint_8_52_w2 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 2 2 224053547472629313 = some 224053547472629313 := by decide +kernel
private theorem endpoint_8_52_p4 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 4 224053547472629313 = some 224053547472629313 :=
  join_receipt_window endpoint_8_52_flag endpoint_8_52_sources 0 2 2 224053547472629313 224053547472629313 224053547472629313 endpoint_8_52_w0 endpoint_8_52_w2
private theorem endpoint_8_52_w4 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 4 2 224053547472629313 = some 224053547472629313 := by decide +kernel
private theorem endpoint_8_52_p6 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 6 224053547472629313 = some 224053547472629313 :=
  join_receipt_window endpoint_8_52_flag endpoint_8_52_sources 0 4 2 224053547472629313 224053547472629313 224053547472629313 endpoint_8_52_p4 endpoint_8_52_w4
private theorem endpoint_8_52_w6 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 6 1 224053547472629313 = some 224053547472629313 := by decide +kernel
private theorem endpoint_8_52_p7 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 7 224053547472629313 = some 224053547472629313 :=
  join_receipt_window endpoint_8_52_flag endpoint_8_52_sources 0 6 1 224053547472629313 224053547472629313 224053547472629313 endpoint_8_52_p6 endpoint_8_52_w6
def endpoint_8_52 : CertifiedEndpoint :=
  ⟨⟨8, 52, 3941⟩, 224053547472629313, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_52_flag endpoint_8_52_sources 7 224053547472629313 224053547472629313 rfl endpoint_8_52_base endpoint_8_52_p7) (by decide)⟩
private def endpoint_8_53_flag : Flag := ⟨8, 53, 3904⟩
private def endpoint_8_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_53_base : receiptBase endpoint_8_53_flag endpoint_8_53_sources = some 225687013024915711 := by decide +kernel
private theorem endpoint_8_53_w0 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 2 225687013024915711 = some 225687013024915711 := by decide +kernel
private theorem endpoint_8_53_w2 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 2 2 225687013024915711 = some 225687013024915711 := by decide +kernel
private theorem endpoint_8_53_p4 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 4 225687013024915711 = some 225687013024915711 :=
  join_receipt_window endpoint_8_53_flag endpoint_8_53_sources 0 2 2 225687013024915711 225687013024915711 225687013024915711 endpoint_8_53_w0 endpoint_8_53_w2
private theorem endpoint_8_53_w4 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 4 2 225687013024915711 = some 225687013024915711 := by decide +kernel
private theorem endpoint_8_53_p6 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 6 225687013024915711 = some 225687013024915711 :=
  join_receipt_window endpoint_8_53_flag endpoint_8_53_sources 0 4 2 225687013024915711 225687013024915711 225687013024915711 endpoint_8_53_p4 endpoint_8_53_w4
private theorem endpoint_8_53_w6 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 6 1 225687013024915711 = some 225687013024915711 := by decide +kernel
private theorem endpoint_8_53_p7 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 7 225687013024915711 = some 225687013024915711 :=
  join_receipt_window endpoint_8_53_flag endpoint_8_53_sources 0 6 1 225687013024915711 225687013024915711 225687013024915711 endpoint_8_53_p6 endpoint_8_53_w6
def endpoint_8_53 : CertifiedEndpoint :=
  ⟨⟨8, 53, 3904⟩, 225687013024915711, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_53_flag endpoint_8_53_sources 7 225687013024915711 225687013024915711 rfl endpoint_8_53_base endpoint_8_53_p7) (by decide)⟩
private def endpoint_8_54_flag : Flag := ⟨8, 54, 3866⟩
private def endpoint_8_54_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_54_base : receiptBase endpoint_8_54_flag endpoint_8_54_sources = some 227191786774065387 := by decide +kernel
private theorem endpoint_8_54_w0 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 2 227191786774065387 = some 227191786774065387 := by decide +kernel
private theorem endpoint_8_54_w2 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 2 2 227191786774065387 = some 227191786774065387 := by decide +kernel
private theorem endpoint_8_54_p4 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 4 227191786774065387 = some 227191786774065387 :=
  join_receipt_window endpoint_8_54_flag endpoint_8_54_sources 0 2 2 227191786774065387 227191786774065387 227191786774065387 endpoint_8_54_w0 endpoint_8_54_w2
private theorem endpoint_8_54_w4 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 4 2 227191786774065387 = some 227191786774065387 := by decide +kernel
private theorem endpoint_8_54_p6 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 6 227191786774065387 = some 227191786774065387 :=
  join_receipt_window endpoint_8_54_flag endpoint_8_54_sources 0 4 2 227191786774065387 227191786774065387 227191786774065387 endpoint_8_54_p4 endpoint_8_54_w4
private theorem endpoint_8_54_w6 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 6 1 227191786774065387 = some 227191786774065387 := by decide +kernel
private theorem endpoint_8_54_p7 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 7 227191786774065387 = some 227191786774065387 :=
  join_receipt_window endpoint_8_54_flag endpoint_8_54_sources 0 6 1 227191786774065387 227191786774065387 227191786774065387 endpoint_8_54_p6 endpoint_8_54_w6
def endpoint_8_54 : CertifiedEndpoint :=
  ⟨⟨8, 54, 3866⟩, 227191786774065387, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_54_flag endpoint_8_54_sources 7 227191786774065387 227191786774065387 rfl endpoint_8_54_base endpoint_8_54_p7) (by decide)⟩
private def endpoint_8_55_flag : Flag := ⟨8, 55, 3827⟩
private def endpoint_8_55_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_55_base : receiptBase endpoint_8_55_flag endpoint_8_55_sources = some 228565043371033821 := by decide +kernel
private theorem endpoint_8_55_w0 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 2 228565043371033821 = some 228565043371033821 := by decide +kernel
private theorem endpoint_8_55_w2 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 2 2 228565043371033821 = some 228565043371033821 := by decide +kernel
private theorem endpoint_8_55_p4 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 4 228565043371033821 = some 228565043371033821 :=
  join_receipt_window endpoint_8_55_flag endpoint_8_55_sources 0 2 2 228565043371033821 228565043371033821 228565043371033821 endpoint_8_55_w0 endpoint_8_55_w2
private theorem endpoint_8_55_w4 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 4 2 228565043371033821 = some 228565043371033821 := by decide +kernel
private theorem endpoint_8_55_p6 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 6 228565043371033821 = some 228565043371033821 :=
  join_receipt_window endpoint_8_55_flag endpoint_8_55_sources 0 4 2 228565043371033821 228565043371033821 228565043371033821 endpoint_8_55_p4 endpoint_8_55_w4
private theorem endpoint_8_55_w6 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 6 1 228565043371033821 = some 228565043371033821 := by decide +kernel
private theorem endpoint_8_55_p7 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 7 228565043371033821 = some 228565043371033821 :=
  join_receipt_window endpoint_8_55_flag endpoint_8_55_sources 0 6 1 228565043371033821 228565043371033821 228565043371033821 endpoint_8_55_p6 endpoint_8_55_w6
def endpoint_8_55 : CertifiedEndpoint :=
  ⟨⟨8, 55, 3827⟩, 228565043371033821, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_55_flag endpoint_8_55_sources 7 228565043371033821 228565043371033821 rfl endpoint_8_55_base endpoint_8_55_p7) (by decide)⟩
private def endpoint_8_56_flag : Flag := ⟨8, 56, 3786⟩
private def endpoint_8_56_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_56_base : receiptBase endpoint_8_56_flag endpoint_8_56_sources = some 230549716345725847 := by decide +kernel
private theorem endpoint_8_56_w0 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 2 230549716345725847 = some 230549716345725847 := by decide +kernel
private theorem endpoint_8_56_w2 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 2 2 230549716345725847 = some 230549716345725847 := by decide +kernel
private theorem endpoint_8_56_p4 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 4 230549716345725847 = some 230549716345725847 :=
  join_receipt_window endpoint_8_56_flag endpoint_8_56_sources 0 2 2 230549716345725847 230549716345725847 230549716345725847 endpoint_8_56_w0 endpoint_8_56_w2
private theorem endpoint_8_56_w4 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 4 2 230549716345725847 = some 230549716345725847 := by decide +kernel
private theorem endpoint_8_56_p6 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 6 230549716345725847 = some 230549716345725847 :=
  join_receipt_window endpoint_8_56_flag endpoint_8_56_sources 0 4 2 230549716345725847 230549716345725847 230549716345725847 endpoint_8_56_p4 endpoint_8_56_w4
private theorem endpoint_8_56_w6 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 6 1 230549716345725847 = some 230549716345725847 := by decide +kernel
private theorem endpoint_8_56_p7 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 7 230549716345725847 = some 230549716345725847 :=
  join_receipt_window endpoint_8_56_flag endpoint_8_56_sources 0 6 1 230549716345725847 230549716345725847 230549716345725847 endpoint_8_56_p6 endpoint_8_56_w6
def endpoint_8_56 : CertifiedEndpoint :=
  ⟨⟨8, 56, 3786⟩, 230549716345725847, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_56_flag endpoint_8_56_sources 7 230549716345725847 230549716345725847 rfl endpoint_8_56_base endpoint_8_56_p7) (by decide)⟩
private def endpoint_8_57_flag : Flag := ⟨8, 57, 3744⟩
private def endpoint_8_57_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_57_base : receiptBase endpoint_8_57_flag endpoint_8_57_sources = some 231580348027084457 := by decide +kernel
private theorem endpoint_8_57_w0 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 2 231580348027084457 = some 231580348027084457 := by decide +kernel
private theorem endpoint_8_57_w2 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 2 2 231580348027084457 = some 231580348027084457 := by decide +kernel
private theorem endpoint_8_57_p4 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 4 231580348027084457 = some 231580348027084457 :=
  join_receipt_window endpoint_8_57_flag endpoint_8_57_sources 0 2 2 231580348027084457 231580348027084457 231580348027084457 endpoint_8_57_w0 endpoint_8_57_w2
private theorem endpoint_8_57_w4 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 4 2 231580348027084457 = some 231580348027084457 := by decide +kernel
private theorem endpoint_8_57_p6 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 6 231580348027084457 = some 231580348027084457 :=
  join_receipt_window endpoint_8_57_flag endpoint_8_57_sources 0 4 2 231580348027084457 231580348027084457 231580348027084457 endpoint_8_57_p4 endpoint_8_57_w4
private theorem endpoint_8_57_w6 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 6 1 231580348027084457 = some 231580348027084457 := by decide +kernel
private theorem endpoint_8_57_p7 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 7 231580348027084457 = some 231580348027084457 :=
  join_receipt_window endpoint_8_57_flag endpoint_8_57_sources 0 6 1 231580348027084457 231580348027084457 231580348027084457 endpoint_8_57_p6 endpoint_8_57_w6
def endpoint_8_57 : CertifiedEndpoint :=
  ⟨⟨8, 57, 3744⟩, 231580348027084457, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_57_flag endpoint_8_57_sources 7 231580348027084457 231580348027084457 rfl endpoint_8_57_base endpoint_8_57_p7) (by decide)⟩

def endpointBlock05 : List CertifiedEndpoint := [
  endpoint_7_27, endpoint_7_28, endpoint_7_29, endpoint_7_30, endpoint_7_31, endpoint_7_32, endpoint_7_33,
  endpoint_7_34, endpoint_7_35, endpoint_7_36, endpoint_7_37, endpoint_7_38, endpoint_7_39, endpoint_7_40,
  endpoint_7_41, endpoint_7_42, endpoint_7_43, endpoint_7_44, endpoint_7_45, endpoint_7_46, endpoint_7_47,
  endpoint_7_48, endpoint_7_49, endpoint_7_50, endpoint_7_51, endpoint_7_52, endpoint_7_53, endpoint_7_54,
  endpoint_7_55, endpoint_7_56, endpoint_7_57, endpoint_7_58, endpoint_7_59, endpoint_7_60, endpoint_7_61,
  endpoint_7_62, endpoint_7_63, endpoint_7_64, endpoint_7_65, endpoint_7_66, endpoint_7_67, endpoint_7_68,
  endpoint_7_69, endpoint_7_70, endpoint_7_71, endpoint_7_72, endpoint_7_73, endpoint_7_74, endpoint_7_75,
  endpoint_7_76, endpoint_7_77, endpoint_7_78, endpoint_7_79, endpoint_7_80, endpoint_7_81, endpoint_7_82,
  endpoint_7_83, endpoint_7_84, endpoint_7_85, endpoint_7_86, endpoint_7_87, endpoint_7_88, endpoint_7_89,
  endpoint_7_90, endpoint_7_91, endpoint_7_92, endpoint_7_93, endpoint_7_94, endpoint_7_95, endpoint_7_96,
  endpoint_8_8, endpoint_8_9, endpoint_8_10, endpoint_8_11, endpoint_8_12, endpoint_8_13, endpoint_8_14,
  endpoint_8_15, endpoint_8_16, endpoint_8_17, endpoint_8_18, endpoint_8_19, endpoint_8_20, endpoint_8_21,
  endpoint_8_22, endpoint_8_23, endpoint_8_24, endpoint_8_25, endpoint_8_26, endpoint_8_27, endpoint_8_28,
  endpoint_8_29, endpoint_8_30, endpoint_8_31, endpoint_8_32, endpoint_8_33, endpoint_8_34, endpoint_8_35,
  endpoint_8_36, endpoint_8_37, endpoint_8_38, endpoint_8_39, endpoint_8_40, endpoint_8_41, endpoint_8_42,
  endpoint_8_43, endpoint_8_44, endpoint_8_45, endpoint_8_46, endpoint_8_47, endpoint_8_48, endpoint_8_49,
  endpoint_8_50, endpoint_8_51, endpoint_8_52, endpoint_8_53, endpoint_8_54, endpoint_8_55, endpoint_8_56,
  endpoint_8_57
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
