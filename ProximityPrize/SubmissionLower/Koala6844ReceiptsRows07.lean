import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def endpoint_10_25 : CertifiedEndpoint :=
  ⟨⟨10, 25, 4091⟩, 195302535336122276, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_26 : CertifiedEndpoint :=
  ⟨⟨10, 26, 4069⟩, 204182388000190959, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_27 : CertifiedEndpoint :=
  ⟨⟨10, 27, 4048⟩, 213004514880940953, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_28 : CertifiedEndpoint :=
  ⟨⟨10, 28, 4026⟩, 221665713855465126, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_29 : CertifiedEndpoint :=
  ⟨⟨10, 29, 4004⟩, 230216357593702749, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_30 : CertifiedEndpoint :=
  ⟨⟨10, 30, 3982⟩, 238656446095653822, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_31 : CertifiedEndpoint :=
  ⟨⟨10, 31, 3959⟩, 246923322776236124, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_32 : CertifiedEndpoint :=
  ⟨⟨10, 32, 3936⟩, 255074730654474696, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_10_33_flag : Flag := ⟨10, 33, 3913⟩
private def endpoint_10_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_33_base : receiptBase endpoint_10_33_flag endpoint_10_33_sources = some 174023547348222479 := by decide +kernel
private theorem endpoint_10_33_w0 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 2 174023547348222479 = some 174023547348222479 := by decide +kernel
private theorem endpoint_10_33_w2 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 2 2 174023547348222479 = some 174023547348222479 := by decide +kernel
private theorem endpoint_10_33_p4 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 4 174023547348222479 = some 174023547348222479 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 2 2 174023547348222479 174023547348222479 174023547348222479 endpoint_10_33_w0 endpoint_10_33_w2
private theorem endpoint_10_33_w4 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 4 2 174023547348222479 = some 174023547348222479 := by decide +kernel
private theorem endpoint_10_33_p6 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 6 174023547348222479 = some 174023547348222479 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 4 2 174023547348222479 174023547348222479 174023547348222479 endpoint_10_33_p4 endpoint_10_33_w4
private theorem endpoint_10_33_w6 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 6 2 174023547348222479 = some 174023547348222479 := by decide +kernel
private theorem endpoint_10_33_p8 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 8 174023547348222479 = some 174023547348222479 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 6 2 174023547348222479 174023547348222479 174023547348222479 endpoint_10_33_p6 endpoint_10_33_w6
private theorem endpoint_10_33_w8 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 8 1 174023547348222479 = some 174023547348222479 := by decide +kernel
private theorem endpoint_10_33_p9 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 9 174023547348222479 = some 174023547348222479 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 8 1 174023547348222479 174023547348222479 174023547348222479 endpoint_10_33_p8 endpoint_10_33_w8
def endpoint_10_33 : CertifiedEndpoint :=
  ⟨⟨10, 33, 3913⟩, 174023547348222479, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_33_flag endpoint_10_33_sources 9 174023547348222479 174023547348222479 rfl endpoint_10_33_base endpoint_10_33_p9) (by decide)⟩
private def endpoint_10_34_flag : Flag := ⟨10, 34, 3889⟩
private def endpoint_10_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_34_base : receiptBase endpoint_10_34_flag endpoint_10_34_sources = some 177262403504024850 := by decide +kernel
private theorem endpoint_10_34_w0 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 2 177262403504024850 = some 177262403504024850 := by decide +kernel
private theorem endpoint_10_34_w2 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 2 2 177262403504024850 = some 177262403504024850 := by decide +kernel
private theorem endpoint_10_34_p4 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 4 177262403504024850 = some 177262403504024850 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 2 2 177262403504024850 177262403504024850 177262403504024850 endpoint_10_34_w0 endpoint_10_34_w2
private theorem endpoint_10_34_w4 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 4 2 177262403504024850 = some 177262403504024850 := by decide +kernel
private theorem endpoint_10_34_p6 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 6 177262403504024850 = some 177262403504024850 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 4 2 177262403504024850 177262403504024850 177262403504024850 endpoint_10_34_p4 endpoint_10_34_w4
private theorem endpoint_10_34_w6 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 6 2 177262403504024850 = some 177262403504024850 := by decide +kernel
private theorem endpoint_10_34_p8 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 8 177262403504024850 = some 177262403504024850 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 6 2 177262403504024850 177262403504024850 177262403504024850 endpoint_10_34_p6 endpoint_10_34_w6
private theorem endpoint_10_34_w8 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 8 1 177262403504024850 = some 177262403504024850 := by decide +kernel
private theorem endpoint_10_34_p9 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 9 177262403504024850 = some 177262403504024850 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 8 1 177262403504024850 177262403504024850 177262403504024850 endpoint_10_34_p8 endpoint_10_34_w8
def endpoint_10_34 : CertifiedEndpoint :=
  ⟨⟨10, 34, 3889⟩, 177262403504024850, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_34_flag endpoint_10_34_sources 9 177262403504024850 177262403504024850 rfl endpoint_10_34_base endpoint_10_34_p9) (by decide)⟩
private def endpoint_10_35_flag : Flag := ⟨10, 35, 3866⟩
private def endpoint_10_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_35_base : receiptBase endpoint_10_35_flag endpoint_10_35_sources = some 180494168801138338 := by decide +kernel
private theorem endpoint_10_35_w0 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 2 180494168801138338 = some 180494168801138338 := by decide +kernel
private theorem endpoint_10_35_w2 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 2 2 180494168801138338 = some 180494168801138338 := by decide +kernel
private theorem endpoint_10_35_p4 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 4 180494168801138338 = some 180494168801138338 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 2 2 180494168801138338 180494168801138338 180494168801138338 endpoint_10_35_w0 endpoint_10_35_w2
private theorem endpoint_10_35_w4 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 4 2 180494168801138338 = some 180494168801138338 := by decide +kernel
private theorem endpoint_10_35_p6 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 6 180494168801138338 = some 180494168801138338 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 4 2 180494168801138338 180494168801138338 180494168801138338 endpoint_10_35_p4 endpoint_10_35_w4
private theorem endpoint_10_35_w6 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 6 2 180494168801138338 = some 180494168801138338 := by decide +kernel
private theorem endpoint_10_35_p8 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 8 180494168801138338 = some 180494168801138338 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 6 2 180494168801138338 180494168801138338 180494168801138338 endpoint_10_35_p6 endpoint_10_35_w6
private theorem endpoint_10_35_w8 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 8 1 180494168801138338 = some 180494168801138338 := by decide +kernel
private theorem endpoint_10_35_p9 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 9 180494168801138338 = some 180494168801138338 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 8 1 180494168801138338 180494168801138338 180494168801138338 endpoint_10_35_p8 endpoint_10_35_w8
def endpoint_10_35 : CertifiedEndpoint :=
  ⟨⟨10, 35, 3866⟩, 180494168801138338, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_35_flag endpoint_10_35_sources 9 180494168801138338 180494168801138338 rfl endpoint_10_35_base endpoint_10_35_p9) (by decide)⟩
private def endpoint_10_36_flag : Flag := ⟨10, 36, 3842⟩
private def endpoint_10_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_36_base : receiptBase endpoint_10_36_flag endpoint_10_36_sources = some 183627894835517887 := by decide +kernel
private theorem endpoint_10_36_w0 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 2 183627894835517887 = some 183627894835517887 := by decide +kernel
private theorem endpoint_10_36_w2 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 2 2 183627894835517887 = some 183627894835517887 := by decide +kernel
private theorem endpoint_10_36_p4 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 4 183627894835517887 = some 183627894835517887 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 2 2 183627894835517887 183627894835517887 183627894835517887 endpoint_10_36_w0 endpoint_10_36_w2
private theorem endpoint_10_36_w4 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 4 2 183627894835517887 = some 183627894835517887 := by decide +kernel
private theorem endpoint_10_36_p6 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 6 183627894835517887 = some 183627894835517887 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 4 2 183627894835517887 183627894835517887 183627894835517887 endpoint_10_36_p4 endpoint_10_36_w4
private theorem endpoint_10_36_w6 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 6 2 183627894835517887 = some 183627894835517887 := by decide +kernel
private theorem endpoint_10_36_p8 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 8 183627894835517887 = some 183627894835517887 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 6 2 183627894835517887 183627894835517887 183627894835517887 endpoint_10_36_p6 endpoint_10_36_w6
private theorem endpoint_10_36_w8 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 8 1 183627894835517887 = some 183627894835517887 := by decide +kernel
private theorem endpoint_10_36_p9 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 9 183627894835517887 = some 183627894835517887 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 8 1 183627894835517887 183627894835517887 183627894835517887 endpoint_10_36_p8 endpoint_10_36_w8
def endpoint_10_36 : CertifiedEndpoint :=
  ⟨⟨10, 36, 3842⟩, 183627894835517887, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_36_flag endpoint_10_36_sources 9 183627894835517887 183627894835517887 rfl endpoint_10_36_base endpoint_10_36_p9) (by decide)⟩
private def endpoint_10_37_flag : Flag := ⟨10, 37, 3817⟩
private def endpoint_10_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_37_base : receiptBase endpoint_10_37_flag endpoint_10_37_sources = some 186660330438435265 := by decide +kernel
private theorem endpoint_10_37_w0 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 2 186660330438435265 = some 186660330438435265 := by decide +kernel
private theorem endpoint_10_37_w2 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 2 2 186660330438435265 = some 186660330438435265 := by decide +kernel
private theorem endpoint_10_37_p4 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 4 186660330438435265 = some 186660330438435265 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 2 2 186660330438435265 186660330438435265 186660330438435265 endpoint_10_37_w0 endpoint_10_37_w2
private theorem endpoint_10_37_w4 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 4 2 186660330438435265 = some 186660330438435265 := by decide +kernel
private theorem endpoint_10_37_p6 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 6 186660330438435265 = some 186660330438435265 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 4 2 186660330438435265 186660330438435265 186660330438435265 endpoint_10_37_p4 endpoint_10_37_w4
private theorem endpoint_10_37_w6 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 6 2 186660330438435265 = some 186660330438435265 := by decide +kernel
private theorem endpoint_10_37_p8 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 8 186660330438435265 = some 186660330438435265 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 6 2 186660330438435265 186660330438435265 186660330438435265 endpoint_10_37_p6 endpoint_10_37_w6
private theorem endpoint_10_37_w8 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 8 1 186660330438435265 = some 186660330438435265 := by decide +kernel
private theorem endpoint_10_37_p9 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 9 186660330438435265 = some 186660330438435265 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 8 1 186660330438435265 186660330438435265 186660330438435265 endpoint_10_37_p8 endpoint_10_37_w8
def endpoint_10_37 : CertifiedEndpoint :=
  ⟨⟨10, 37, 3817⟩, 186660330438435265, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_37_flag endpoint_10_37_sources 9 186660330438435265 186660330438435265 rfl endpoint_10_37_base endpoint_10_37_p9) (by decide)⟩
private def endpoint_10_38_flag : Flag := ⟨10, 38, 3792⟩
private def endpoint_10_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_38_base : receiptBase endpoint_10_38_flag endpoint_10_38_sources = some 189637491673367707 := by decide +kernel
private theorem endpoint_10_38_w0 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 2 189637491673367707 = some 189637491673367707 := by decide +kernel
private theorem endpoint_10_38_w2 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 2 2 189637491673367707 = some 189637491673367707 := by decide +kernel
private theorem endpoint_10_38_p4 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 4 189637491673367707 = some 189637491673367707 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 2 2 189637491673367707 189637491673367707 189637491673367707 endpoint_10_38_w0 endpoint_10_38_w2
private theorem endpoint_10_38_w4 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 4 2 189637491673367707 = some 189637491673367707 := by decide +kernel
private theorem endpoint_10_38_p6 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 6 189637491673367707 = some 189637491673367707 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 4 2 189637491673367707 189637491673367707 189637491673367707 endpoint_10_38_p4 endpoint_10_38_w4
private theorem endpoint_10_38_w6 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 6 2 189637491673367707 = some 189637491673367707 := by decide +kernel
private theorem endpoint_10_38_p8 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 8 189637491673367707 = some 189637491673367707 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 6 2 189637491673367707 189637491673367707 189637491673367707 endpoint_10_38_p6 endpoint_10_38_w6
private theorem endpoint_10_38_w8 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 8 1 189637491673367707 = some 189637491673367707 := by decide +kernel
private theorem endpoint_10_38_p9 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 9 189637491673367707 = some 189637491673367707 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 8 1 189637491673367707 189637491673367707 189637491673367707 endpoint_10_38_p8 endpoint_10_38_w8
def endpoint_10_38 : CertifiedEndpoint :=
  ⟨⟨10, 38, 3792⟩, 189637491673367707, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_38_flag endpoint_10_38_sources 9 189637491673367707 189637491673367707 rfl endpoint_10_38_base endpoint_10_38_p9) (by decide)⟩
private def endpoint_10_39_flag : Flag := ⟨10, 39, 3767⟩
private def endpoint_10_39_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_39_base : receiptBase endpoint_10_39_flag endpoint_10_39_sources = some 192559378540315212 := by decide +kernel
private theorem endpoint_10_39_w0 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 2 192559378540315212 = some 192559378540315212 := by decide +kernel
private theorem endpoint_10_39_w2 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 2 2 192559378540315212 = some 192559378540315212 := by decide +kernel
private theorem endpoint_10_39_p4 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 4 192559378540315212 = some 192559378540315212 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 2 2 192559378540315212 192559378540315212 192559378540315212 endpoint_10_39_w0 endpoint_10_39_w2
private theorem endpoint_10_39_w4 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 4 2 192559378540315212 = some 192559378540315212 := by decide +kernel
private theorem endpoint_10_39_p6 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 6 192559378540315212 = some 192559378540315212 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 4 2 192559378540315212 192559378540315212 192559378540315212 endpoint_10_39_p4 endpoint_10_39_w4
private theorem endpoint_10_39_w6 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 6 2 192559378540315212 = some 192559378540315212 := by decide +kernel
private theorem endpoint_10_39_p8 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 8 192559378540315212 = some 192559378540315212 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 6 2 192559378540315212 192559378540315212 192559378540315212 endpoint_10_39_p6 endpoint_10_39_w6
private theorem endpoint_10_39_w8 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 8 1 192559378540315212 = some 192559378540315212 := by decide +kernel
private theorem endpoint_10_39_p9 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 9 192559378540315212 = some 192559378540315212 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 8 1 192559378540315212 192559378540315212 192559378540315212 endpoint_10_39_p8 endpoint_10_39_w8
def endpoint_10_39 : CertifiedEndpoint :=
  ⟨⟨10, 39, 3767⟩, 192559378540315212, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_39_flag endpoint_10_39_sources 9 192559378540315212 192559378540315212 rfl endpoint_10_39_base endpoint_10_39_p9) (by decide)⟩
private def endpoint_10_40_flag : Flag := ⟨10, 40, 3742⟩
private def endpoint_10_40_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_40_base : receiptBase endpoint_10_40_flag endpoint_10_40_sources = some 195425991039277779 := by decide +kernel
private theorem endpoint_10_40_w0 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 2 195425991039277779 = some 195425991039277779 := by decide +kernel
private theorem endpoint_10_40_w2 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 2 2 195425991039277779 = some 195425991039277779 := by decide +kernel
private theorem endpoint_10_40_p4 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 4 195425991039277779 = some 195425991039277779 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 2 2 195425991039277779 195425991039277779 195425991039277779 endpoint_10_40_w0 endpoint_10_40_w2
private theorem endpoint_10_40_w4 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 4 2 195425991039277779 = some 195425991039277779 := by decide +kernel
private theorem endpoint_10_40_p6 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 6 195425991039277779 = some 195425991039277779 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 4 2 195425991039277779 195425991039277779 195425991039277779 endpoint_10_40_p4 endpoint_10_40_w4
private theorem endpoint_10_40_w6 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 6 2 195425991039277779 = some 195425991039277779 := by decide +kernel
private theorem endpoint_10_40_p8 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 8 195425991039277779 = some 195425991039277779 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 6 2 195425991039277779 195425991039277779 195425991039277779 endpoint_10_40_p6 endpoint_10_40_w6
private theorem endpoint_10_40_w8 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 8 1 195425991039277779 = some 195425991039277779 := by decide +kernel
private theorem endpoint_10_40_p9 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 9 195425991039277779 = some 195425991039277779 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 8 1 195425991039277779 195425991039277779 195425991039277779 endpoint_10_40_p8 endpoint_10_40_w8
def endpoint_10_40 : CertifiedEndpoint :=
  ⟨⟨10, 40, 3742⟩, 195425991039277779, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_40_flag endpoint_10_40_sources 9 195425991039277779 195425991039277779 rfl endpoint_10_40_base endpoint_10_40_p9) (by decide)⟩
private def endpoint_10_41_flag : Flag := ⟨10, 41, 3716⟩
private def endpoint_10_41_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_41_base : receiptBase endpoint_10_41_flag endpoint_10_41_sources = some 198184810769321716 := by decide +kernel
private theorem endpoint_10_41_w0 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 2 198184810769321716 = some 198184810769321716 := by decide +kernel
private theorem endpoint_10_41_w2 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 2 2 198184810769321716 = some 198184810769321716 := by decide +kernel
private theorem endpoint_10_41_p4 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 4 198184810769321716 = some 198184810769321716 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 2 2 198184810769321716 198184810769321716 198184810769321716 endpoint_10_41_w0 endpoint_10_41_w2
private theorem endpoint_10_41_w4 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 4 2 198184810769321716 = some 198184810769321716 := by decide +kernel
private theorem endpoint_10_41_p6 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 6 198184810769321716 = some 198184810769321716 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 4 2 198184810769321716 198184810769321716 198184810769321716 endpoint_10_41_p4 endpoint_10_41_w4
private theorem endpoint_10_41_w6 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 6 2 198184810769321716 = some 198184810769321716 := by decide +kernel
private theorem endpoint_10_41_p8 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 8 198184810769321716 = some 198184810769321716 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 6 2 198184810769321716 198184810769321716 198184810769321716 endpoint_10_41_p6 endpoint_10_41_w6
private theorem endpoint_10_41_w8 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 8 1 198184810769321716 = some 198184810769321716 := by decide +kernel
private theorem endpoint_10_41_p9 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 9 198184810769321716 = some 198184810769321716 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 8 1 198184810769321716 198184810769321716 198184810769321716 endpoint_10_41_p8 endpoint_10_41_w8
def endpoint_10_41 : CertifiedEndpoint :=
  ⟨⟨10, 41, 3716⟩, 198184810769321716, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_41_flag endpoint_10_41_sources 9 198184810769321716 198184810769321716 rfl endpoint_10_41_base endpoint_10_41_p9) (by decide)⟩
private def endpoint_10_42_flag : Flag := ⟨10, 42, 3689⟩
private def endpoint_10_42_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_42_base : receiptBase endpoint_10_42_flag endpoint_10_42_sources = some 200832586561718790 := by decide +kernel
private theorem endpoint_10_42_w0 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 2 200832586561718790 = some 200832586561718790 := by decide +kernel
private theorem endpoint_10_42_w2 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 2 2 200832586561718790 = some 200832586561718790 := by decide +kernel
private theorem endpoint_10_42_p4 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 4 200832586561718790 = some 200832586561718790 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 2 2 200832586561718790 200832586561718790 200832586561718790 endpoint_10_42_w0 endpoint_10_42_w2
private theorem endpoint_10_42_w4 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 4 2 200832586561718790 = some 200832586561718790 := by decide +kernel
private theorem endpoint_10_42_p6 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 6 200832586561718790 = some 200832586561718790 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 4 2 200832586561718790 200832586561718790 200832586561718790 endpoint_10_42_p4 endpoint_10_42_w4
private theorem endpoint_10_42_w6 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 6 2 200832586561718790 = some 200832586561718790 := by decide +kernel
private theorem endpoint_10_42_p8 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 8 200832586561718790 = some 200832586561718790 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 6 2 200832586561718790 200832586561718790 200832586561718790 endpoint_10_42_p6 endpoint_10_42_w6
private theorem endpoint_10_42_w8 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 8 1 200832586561718790 = some 200832586561718790 := by decide +kernel
private theorem endpoint_10_42_p9 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 9 200832586561718790 = some 200832586561718790 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 8 1 200832586561718790 200832586561718790 200832586561718790 endpoint_10_42_p8 endpoint_10_42_w8
def endpoint_10_42 : CertifiedEndpoint :=
  ⟨⟨10, 42, 3689⟩, 200832586561718790, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_42_flag endpoint_10_42_sources 9 200832586561718790 200832586561718790 rfl endpoint_10_42_base endpoint_10_42_p9) (by decide)⟩
private def endpoint_10_43_flag : Flag := ⟨10, 43, 3662⟩
private def endpoint_10_43_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_43_base : receiptBase endpoint_10_43_flag endpoint_10_43_sources = some 203924895646164162 := by decide +kernel
private theorem endpoint_10_43_w0 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 2 203924895646164162 = some 203924895646164162 := by decide +kernel
private theorem endpoint_10_43_w2 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 2 2 203924895646164162 = some 203924895646164162 := by decide +kernel
private theorem endpoint_10_43_p4 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 4 203924895646164162 = some 203924895646164162 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 2 2 203924895646164162 203924895646164162 203924895646164162 endpoint_10_43_w0 endpoint_10_43_w2
private theorem endpoint_10_43_w4 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 4 2 203924895646164162 = some 203924895646164162 := by decide +kernel
private theorem endpoint_10_43_p6 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 6 203924895646164162 = some 203924895646164162 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 4 2 203924895646164162 203924895646164162 203924895646164162 endpoint_10_43_p4 endpoint_10_43_w4
private theorem endpoint_10_43_w6 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 6 2 203924895646164162 = some 203924895646164162 := by decide +kernel
private theorem endpoint_10_43_p8 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 8 203924895646164162 = some 203924895646164162 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 6 2 203924895646164162 203924895646164162 203924895646164162 endpoint_10_43_p6 endpoint_10_43_w6
private theorem endpoint_10_43_w8 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 8 1 203924895646164162 = some 203924895646164162 := by decide +kernel
private theorem endpoint_10_43_p9 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 9 203924895646164162 = some 203924895646164162 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 8 1 203924895646164162 203924895646164162 203924895646164162 endpoint_10_43_p8 endpoint_10_43_w8
def endpoint_10_43 : CertifiedEndpoint :=
  ⟨⟨10, 43, 3662⟩, 203924895646164162, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_43_flag endpoint_10_43_sources 9 203924895646164162 203924895646164162 rfl endpoint_10_43_base endpoint_10_43_p9) (by decide)⟩
private def endpoint_10_44_flag : Flag := ⟨10, 44, 3635⟩
private def endpoint_10_44_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_44_base : receiptBase endpoint_10_44_flag endpoint_10_44_sources = some 206424052289687521 := by decide +kernel
private theorem endpoint_10_44_w0 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 2 206424052289687521 = some 206424052289687521 := by decide +kernel
private theorem endpoint_10_44_w2 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 2 2 206424052289687521 = some 206424052289687521 := by decide +kernel
private theorem endpoint_10_44_p4 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 4 206424052289687521 = some 206424052289687521 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 2 2 206424052289687521 206424052289687521 206424052289687521 endpoint_10_44_w0 endpoint_10_44_w2
private theorem endpoint_10_44_w4 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 4 2 206424052289687521 = some 206424052289687521 := by decide +kernel
private theorem endpoint_10_44_p6 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 6 206424052289687521 = some 206424052289687521 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 4 2 206424052289687521 206424052289687521 206424052289687521 endpoint_10_44_p4 endpoint_10_44_w4
private theorem endpoint_10_44_w6 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 6 2 206424052289687521 = some 206424052289687521 := by decide +kernel
private theorem endpoint_10_44_p8 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 8 206424052289687521 = some 206424052289687521 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 6 2 206424052289687521 206424052289687521 206424052289687521 endpoint_10_44_p6 endpoint_10_44_w6
private theorem endpoint_10_44_w8 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 8 1 206424052289687521 = some 206424052289687521 := by decide +kernel
private theorem endpoint_10_44_p9 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 9 206424052289687521 = some 206424052289687521 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 8 1 206424052289687521 206424052289687521 206424052289687521 endpoint_10_44_p8 endpoint_10_44_w8
def endpoint_10_44 : CertifiedEndpoint :=
  ⟨⟨10, 44, 3635⟩, 206424052289687521, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_44_flag endpoint_10_44_sources 9 206424052289687521 206424052289687521 rfl endpoint_10_44_base endpoint_10_44_p9) (by decide)⟩
private def endpoint_10_45_flag : Flag := ⟨10, 45, 3607⟩
private def endpoint_10_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_45_base : receiptBase endpoint_10_45_flag endpoint_10_45_sources = some 208806784698809648 := by decide +kernel
private theorem endpoint_10_45_w0 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 2 208806784698809648 = some 208806784698809648 := by decide +kernel
private theorem endpoint_10_45_w2 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 2 2 208806784698809648 = some 208806784698809648 := by decide +kernel
private theorem endpoint_10_45_p4 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 4 208806784698809648 = some 208806784698809648 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 2 2 208806784698809648 208806784698809648 208806784698809648 endpoint_10_45_w0 endpoint_10_45_w2
private theorem endpoint_10_45_w4 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 4 2 208806784698809648 = some 208806784698809648 := by decide +kernel
private theorem endpoint_10_45_p6 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 6 208806784698809648 = some 208806784698809648 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 4 2 208806784698809648 208806784698809648 208806784698809648 endpoint_10_45_p4 endpoint_10_45_w4
private theorem endpoint_10_45_w6 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 6 2 208806784698809648 = some 208806784698809648 := by decide +kernel
private theorem endpoint_10_45_p8 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 8 208806784698809648 = some 208806784698809648 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 6 2 208806784698809648 208806784698809648 208806784698809648 endpoint_10_45_p6 endpoint_10_45_w6
private theorem endpoint_10_45_w8 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 8 1 208806784698809648 = some 208806784698809648 := by decide +kernel
private theorem endpoint_10_45_p9 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 9 208806784698809648 = some 208806784698809648 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 8 1 208806784698809648 208806784698809648 208806784698809648 endpoint_10_45_p8 endpoint_10_45_w8
def endpoint_10_45 : CertifiedEndpoint :=
  ⟨⟨10, 45, 3607⟩, 208806784698809648, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_45_flag endpoint_10_45_sources 9 208806784698809648 208806784698809648 rfl endpoint_10_45_base endpoint_10_45_p9) (by decide)⟩
private def endpoint_10_46_flag : Flag := ⟨10, 46, 3579⟩
private def endpoint_10_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_46_base : receiptBase endpoint_10_46_flag endpoint_10_46_sources = some 211128001336290235 := by decide +kernel
private theorem endpoint_10_46_w0 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 2 211128001336290235 = some 211128001336290235 := by decide +kernel
private theorem endpoint_10_46_w2 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 2 2 211128001336290235 = some 211128001336290235 := by decide +kernel
private theorem endpoint_10_46_p4 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 4 211128001336290235 = some 211128001336290235 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 2 2 211128001336290235 211128001336290235 211128001336290235 endpoint_10_46_w0 endpoint_10_46_w2
private theorem endpoint_10_46_w4 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 4 2 211128001336290235 = some 211128001336290235 := by decide +kernel
private theorem endpoint_10_46_p6 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 6 211128001336290235 = some 211128001336290235 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 4 2 211128001336290235 211128001336290235 211128001336290235 endpoint_10_46_p4 endpoint_10_46_w4
private theorem endpoint_10_46_w6 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 6 2 211128001336290235 = some 211128001336290235 := by decide +kernel
private theorem endpoint_10_46_p8 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 8 211128001336290235 = some 211128001336290235 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 6 2 211128001336290235 211128001336290235 211128001336290235 endpoint_10_46_p6 endpoint_10_46_w6
private theorem endpoint_10_46_w8 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 8 1 211128001336290235 = some 211128001336290235 := by decide +kernel
private theorem endpoint_10_46_p9 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 9 211128001336290235 = some 211128001336290235 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 8 1 211128001336290235 211128001336290235 211128001336290235 endpoint_10_46_p8 endpoint_10_46_w8
def endpoint_10_46 : CertifiedEndpoint :=
  ⟨⟨10, 46, 3579⟩, 211128001336290235, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_46_flag endpoint_10_46_sources 9 211128001336290235 211128001336290235 rfl endpoint_10_46_base endpoint_10_46_p9) (by decide)⟩
private def endpoint_10_47_flag : Flag := ⟨10, 47, 3550⟩
private def endpoint_10_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_47_base : receiptBase endpoint_10_47_flag endpoint_10_47_sources = some 213328476843114044 := by decide +kernel
private theorem endpoint_10_47_w0 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 2 213328476843114044 = some 213328476843114044 := by decide +kernel
private theorem endpoint_10_47_w2 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 2 2 213328476843114044 = some 213328476843114044 := by decide +kernel
private theorem endpoint_10_47_p4 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 4 213328476843114044 = some 213328476843114044 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 2 2 213328476843114044 213328476843114044 213328476843114044 endpoint_10_47_w0 endpoint_10_47_w2
private theorem endpoint_10_47_w4 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 4 2 213328476843114044 = some 213328476843114044 := by decide +kernel
private theorem endpoint_10_47_p6 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 6 213328476843114044 = some 213328476843114044 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 4 2 213328476843114044 213328476843114044 213328476843114044 endpoint_10_47_p4 endpoint_10_47_w4
private theorem endpoint_10_47_w6 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 6 2 213328476843114044 = some 213328476843114044 := by decide +kernel
private theorem endpoint_10_47_p8 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 8 213328476843114044 = some 213328476843114044 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 6 2 213328476843114044 213328476843114044 213328476843114044 endpoint_10_47_p6 endpoint_10_47_w6
private theorem endpoint_10_47_w8 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 8 1 213328476843114044 = some 213328476843114044 := by decide +kernel
private theorem endpoint_10_47_p9 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 9 213328476843114044 = some 213328476843114044 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 8 1 213328476843114044 213328476843114044 213328476843114044 endpoint_10_47_p8 endpoint_10_47_w8
def endpoint_10_47 : CertifiedEndpoint :=
  ⟨⟨10, 47, 3550⟩, 213328476843114044, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_47_flag endpoint_10_47_sources 9 213328476843114044 213328476843114044 rfl endpoint_10_47_base endpoint_10_47_p9) (by decide)⟩
private def endpoint_10_48_flag : Flag := ⟨10, 48, 3521⟩
private def endpoint_10_48_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_48_base : receiptBase endpoint_10_48_flag endpoint_10_48_sources = some 215465278130168539 := by decide +kernel
private theorem endpoint_10_48_w0 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 2 215465278130168539 = some 215465278130168539 := by decide +kernel
private theorem endpoint_10_48_w2 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 2 2 215465278130168539 = some 215465278130168539 := by decide +kernel
private theorem endpoint_10_48_p4 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 4 215465278130168539 = some 215465278130168539 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 2 2 215465278130168539 215465278130168539 215465278130168539 endpoint_10_48_w0 endpoint_10_48_w2
private theorem endpoint_10_48_w4 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 4 2 215465278130168539 = some 215465278130168539 := by decide +kernel
private theorem endpoint_10_48_p6 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 6 215465278130168539 = some 215465278130168539 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 4 2 215465278130168539 215465278130168539 215465278130168539 endpoint_10_48_p4 endpoint_10_48_w4
private theorem endpoint_10_48_w6 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 6 2 215465278130168539 = some 215465278130168539 := by decide +kernel
private theorem endpoint_10_48_p8 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 8 215465278130168539 = some 215465278130168539 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 6 2 215465278130168539 215465278130168539 215465278130168539 endpoint_10_48_p6 endpoint_10_48_w6
private theorem endpoint_10_48_w8 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 8 1 215465278130168539 = some 215465278130168539 := by decide +kernel
private theorem endpoint_10_48_p9 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 9 215465278130168539 = some 215465278130168539 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 8 1 215465278130168539 215465278130168539 215465278130168539 endpoint_10_48_p8 endpoint_10_48_w8
def endpoint_10_48 : CertifiedEndpoint :=
  ⟨⟨10, 48, 3521⟩, 215465278130168539, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_48_flag endpoint_10_48_sources 9 215465278130168539 215465278130168539 rfl endpoint_10_48_base endpoint_10_48_p9) (by decide)⟩
private def endpoint_10_49_flag : Flag := ⟨10, 49, 3490⟩
private def endpoint_10_49_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_49_base : receiptBase endpoint_10_49_flag endpoint_10_49_sources = some 217415637583167697 := by decide +kernel
private theorem endpoint_10_49_w0 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 2 217415637583167697 = some 217415637583167697 := by decide +kernel
private theorem endpoint_10_49_w2 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 2 2 217415637583167697 = some 217415637583167697 := by decide +kernel
private theorem endpoint_10_49_p4 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 4 217415637583167697 = some 217415637583167697 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 2 2 217415637583167697 217415637583167697 217415637583167697 endpoint_10_49_w0 endpoint_10_49_w2
private theorem endpoint_10_49_w4 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 4 2 217415637583167697 = some 217415637583167697 := by decide +kernel
private theorem endpoint_10_49_p6 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 6 217415637583167697 = some 217415637583167697 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 4 2 217415637583167697 217415637583167697 217415637583167697 endpoint_10_49_p4 endpoint_10_49_w4
private theorem endpoint_10_49_w6 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 6 2 217415637583167697 = some 217415637583167697 := by decide +kernel
private theorem endpoint_10_49_p8 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 8 217415637583167697 = some 217415637583167697 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 6 2 217415637583167697 217415637583167697 217415637583167697 endpoint_10_49_p6 endpoint_10_49_w6
private theorem endpoint_10_49_w8 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 8 1 217415637583167697 = some 217415637583167697 := by decide +kernel
private theorem endpoint_10_49_p9 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 9 217415637583167697 = some 217415637583167697 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 8 1 217415637583167697 217415637583167697 217415637583167697 endpoint_10_49_p8 endpoint_10_49_w8
def endpoint_10_49 : CertifiedEndpoint :=
  ⟨⟨10, 49, 3490⟩, 217415637583167697, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_49_flag endpoint_10_49_sources 9 217415637583167697 217415637583167697 rfl endpoint_10_49_base endpoint_10_49_p9) (by decide)⟩
private def endpoint_10_50_flag : Flag := ⟨10, 50, 3460⟩
private def endpoint_10_50_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_50_base : receiptBase endpoint_10_50_flag endpoint_10_50_sources = some 219360468951348894 := by decide +kernel
private theorem endpoint_10_50_w0 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 2 219360468951348894 = some 219360468951348894 := by decide +kernel
private theorem endpoint_10_50_w2 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 2 2 219360468951348894 = some 219360468951348894 := by decide +kernel
private theorem endpoint_10_50_p4 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 4 219360468951348894 = some 219360468951348894 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 2 2 219360468951348894 219360468951348894 219360468951348894 endpoint_10_50_w0 endpoint_10_50_w2
private theorem endpoint_10_50_w4 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 4 2 219360468951348894 = some 219360468951348894 := by decide +kernel
private theorem endpoint_10_50_p6 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 6 219360468951348894 = some 219360468951348894 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 4 2 219360468951348894 219360468951348894 219360468951348894 endpoint_10_50_p4 endpoint_10_50_w4
private theorem endpoint_10_50_w6 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 6 2 219360468951348894 = some 219360468951348894 := by decide +kernel
private theorem endpoint_10_50_p8 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 8 219360468951348894 = some 219360468951348894 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 6 2 219360468951348894 219360468951348894 219360468951348894 endpoint_10_50_p6 endpoint_10_50_w6
private theorem endpoint_10_50_w8 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 8 1 219360468951348894 = some 219360468951348894 := by decide +kernel
private theorem endpoint_10_50_p9 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 9 219360468951348894 = some 219360468951348894 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 8 1 219360468951348894 219360468951348894 219360468951348894 endpoint_10_50_p8 endpoint_10_50_w8
def endpoint_10_50 : CertifiedEndpoint :=
  ⟨⟨10, 50, 3460⟩, 219360468951348894, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_50_flag endpoint_10_50_sources 9 219360468951348894 219360468951348894 rfl endpoint_10_50_base endpoint_10_50_p9) (by decide)⟩
private def endpoint_10_51_flag : Flag := ⟨10, 51, 3428⟩
private def endpoint_10_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_51_base : receiptBase endpoint_10_51_flag endpoint_10_51_sources = some 221112383141091434 := by decide +kernel
private theorem endpoint_10_51_w0 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 2 221112383141091434 = some 221112383141091434 := by decide +kernel
private theorem endpoint_10_51_w2 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 2 2 221112383141091434 = some 221112383141091434 := by decide +kernel
private theorem endpoint_10_51_p4 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 4 221112383141091434 = some 221112383141091434 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 2 2 221112383141091434 221112383141091434 221112383141091434 endpoint_10_51_w0 endpoint_10_51_w2
private theorem endpoint_10_51_w4 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 4 2 221112383141091434 = some 221112383141091434 := by decide +kernel
private theorem endpoint_10_51_p6 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 6 221112383141091434 = some 221112383141091434 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 4 2 221112383141091434 221112383141091434 221112383141091434 endpoint_10_51_p4 endpoint_10_51_w4
private theorem endpoint_10_51_w6 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 6 2 221112383141091434 = some 221112383141091434 := by decide +kernel
private theorem endpoint_10_51_p8 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 8 221112383141091434 = some 221112383141091434 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 6 2 221112383141091434 221112383141091434 221112383141091434 endpoint_10_51_p6 endpoint_10_51_w6
private theorem endpoint_10_51_w8 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 8 1 221112383141091434 = some 221112383141091434 := by decide +kernel
private theorem endpoint_10_51_p9 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 9 221112383141091434 = some 221112383141091434 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 8 1 221112383141091434 221112383141091434 221112383141091434 endpoint_10_51_p8 endpoint_10_51_w8
def endpoint_10_51 : CertifiedEndpoint :=
  ⟨⟨10, 51, 3428⟩, 221112383141091434, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_51_flag endpoint_10_51_sources 9 221112383141091434 221112383141091434 rfl endpoint_10_51_base endpoint_10_51_p9) (by decide)⟩
private def endpoint_10_52_flag : Flag := ⟨10, 52, 3396⟩
private def endpoint_10_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_52_base : receiptBase endpoint_10_52_flag endpoint_10_52_sources = some 222794147766681341 := by decide +kernel
private theorem endpoint_10_52_w0 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 2 222794147766681341 = some 222794147766681341 := by decide +kernel
private theorem endpoint_10_52_w2 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 2 2 222794147766681341 = some 222794147766681341 := by decide +kernel
private theorem endpoint_10_52_p4 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 4 222794147766681341 = some 222794147766681341 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 2 2 222794147766681341 222794147766681341 222794147766681341 endpoint_10_52_w0 endpoint_10_52_w2
private theorem endpoint_10_52_w4 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 4 2 222794147766681341 = some 222794147766681341 := by decide +kernel
private theorem endpoint_10_52_p6 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 6 222794147766681341 = some 222794147766681341 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 4 2 222794147766681341 222794147766681341 222794147766681341 endpoint_10_52_p4 endpoint_10_52_w4
private theorem endpoint_10_52_w6 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 6 2 222794147766681341 = some 222794147766681341 := by decide +kernel
private theorem endpoint_10_52_p8 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 8 222794147766681341 = some 222794147766681341 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 6 2 222794147766681341 222794147766681341 222794147766681341 endpoint_10_52_p6 endpoint_10_52_w6
private theorem endpoint_10_52_w8 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 8 1 222794147766681341 = some 222794147766681341 := by decide +kernel
private theorem endpoint_10_52_p9 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 9 222794147766681341 = some 222794147766681341 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 8 1 222794147766681341 222794147766681341 222794147766681341 endpoint_10_52_p8 endpoint_10_52_w8
def endpoint_10_52 : CertifiedEndpoint :=
  ⟨⟨10, 52, 3396⟩, 222794147766681341, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_52_flag endpoint_10_52_sources 9 222794147766681341 222794147766681341 rfl endpoint_10_52_base endpoint_10_52_p9) (by decide)⟩
private def endpoint_10_53_flag : Flag := ⟨10, 53, 3363⟩
private def endpoint_10_53_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_10_53_base : receiptBase endpoint_10_53_flag endpoint_10_53_sources = some 224980563201488650 := by decide +kernel
private theorem endpoint_10_53_w0 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 2 224980563201488650 = some 224980563201488650 := by decide +kernel
private theorem endpoint_10_53_w2 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 2 2 224980563201488650 = some 224980563201488650 := by decide +kernel
private theorem endpoint_10_53_p4 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 4 224980563201488650 = some 224980563201488650 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 2 2 224980563201488650 224980563201488650 224980563201488650 endpoint_10_53_w0 endpoint_10_53_w2
private theorem endpoint_10_53_w4 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 4 2 224980563201488650 = some 224980563201488650 := by decide +kernel
private theorem endpoint_10_53_p6 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 6 224980563201488650 = some 224980563201488650 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 4 2 224980563201488650 224980563201488650 224980563201488650 endpoint_10_53_p4 endpoint_10_53_w4
private theorem endpoint_10_53_w6 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 6 2 224980563201488650 = some 224980563201488650 := by decide +kernel
private theorem endpoint_10_53_p8 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 8 224980563201488650 = some 224980563201488650 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 6 2 224980563201488650 224980563201488650 224980563201488650 endpoint_10_53_p6 endpoint_10_53_w6
private theorem endpoint_10_53_w8 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 8 1 224980563201488650 = some 224980563201488650 := by decide +kernel
private theorem endpoint_10_53_p9 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 9 224980563201488650 = some 224980563201488650 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 8 1 224980563201488650 224980563201488650 224980563201488650 endpoint_10_53_p8 endpoint_10_53_w8
def endpoint_10_53 : CertifiedEndpoint :=
  ⟨⟨10, 53, 3363⟩, 224980563201488650, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_10_53_flag endpoint_10_53_sources 9 224980563201488650 224980563201488650 rfl endpoint_10_53_base endpoint_10_53_p9) (by decide)⟩
private def endpoint_10_54_flag : Flag := ⟨10, 54, 3329⟩
private def endpoint_10_54_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_10_54_base : receiptBase endpoint_10_54_flag endpoint_10_54_sources = some 226395354533276696 := by decide +kernel
private theorem endpoint_10_54_w0 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 2 226395354533276696 = some 226395354533276696 := by decide +kernel
private theorem endpoint_10_54_w2 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 2 2 226395354533276696 = some 226395354533276696 := by decide +kernel
private theorem endpoint_10_54_p4 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 4 226395354533276696 = some 226395354533276696 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 2 2 226395354533276696 226395354533276696 226395354533276696 endpoint_10_54_w0 endpoint_10_54_w2
private theorem endpoint_10_54_w4 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 4 2 226395354533276696 = some 226395354533276696 := by decide +kernel
private theorem endpoint_10_54_p6 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 6 226395354533276696 = some 226395354533276696 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 4 2 226395354533276696 226395354533276696 226395354533276696 endpoint_10_54_p4 endpoint_10_54_w4
private theorem endpoint_10_54_w6 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 6 2 226395354533276696 = some 226395354533276696 := by decide +kernel
private theorem endpoint_10_54_p8 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 8 226395354533276696 = some 226395354533276696 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 6 2 226395354533276696 226395354533276696 226395354533276696 endpoint_10_54_p6 endpoint_10_54_w6
private theorem endpoint_10_54_w8 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 8 1 226395354533276696 = some 226395354533276696 := by decide +kernel
private theorem endpoint_10_54_p9 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 9 226395354533276696 = some 226395354533276696 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 8 1 226395354533276696 226395354533276696 226395354533276696 endpoint_10_54_p8 endpoint_10_54_w8
def endpoint_10_54 : CertifiedEndpoint :=
  ⟨⟨10, 54, 3329⟩, 226395354533276696, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_10_54_flag endpoint_10_54_sources 9 226395354533276696 226395354533276696 rfl endpoint_10_54_base endpoint_10_54_p9) (by decide)⟩
private def endpoint_10_55_flag : Flag := ⟨10, 55, 3295⟩
private def endpoint_10_55_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_10_55_base : receiptBase endpoint_10_55_flag endpoint_10_55_sources = some 227735364379900349 := by decide +kernel
private theorem endpoint_10_55_w0 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 2 227735364379900349 = some 227735364379900349 := by decide +kernel
private theorem endpoint_10_55_w2 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 2 2 227735364379900349 = some 227735364379900349 := by decide +kernel
private theorem endpoint_10_55_p4 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 4 227735364379900349 = some 227735364379900349 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 2 2 227735364379900349 227735364379900349 227735364379900349 endpoint_10_55_w0 endpoint_10_55_w2
private theorem endpoint_10_55_w4 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 4 2 227735364379900349 = some 227735364379900349 := by decide +kernel
private theorem endpoint_10_55_p6 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 6 227735364379900349 = some 227735364379900349 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 4 2 227735364379900349 227735364379900349 227735364379900349 endpoint_10_55_p4 endpoint_10_55_w4
private theorem endpoint_10_55_w6 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 6 2 227735364379900349 = some 227735364379900349 := by decide +kernel
private theorem endpoint_10_55_p8 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 8 227735364379900349 = some 227735364379900349 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 6 2 227735364379900349 227735364379900349 227735364379900349 endpoint_10_55_p6 endpoint_10_55_w6
private theorem endpoint_10_55_w8 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 8 1 227735364379900349 = some 227735364379900349 := by decide +kernel
private theorem endpoint_10_55_p9 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 9 227735364379900349 = some 227735364379900349 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 8 1 227735364379900349 227735364379900349 227735364379900349 endpoint_10_55_p8 endpoint_10_55_w8
def endpoint_10_55 : CertifiedEndpoint :=
  ⟨⟨10, 55, 3295⟩, 227735364379900349, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_10_55_flag endpoint_10_55_sources 9 227735364379900349 227735364379900349 rfl endpoint_10_55_base endpoint_10_55_p9) (by decide)⟩
private def endpoint_10_56_flag : Flag := ⟨10, 56, 3259⟩
private def endpoint_10_56_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_10_56_base : receiptBase endpoint_10_56_flag endpoint_10_56_sources = some 229064094076558031 := by decide +kernel
private theorem endpoint_10_56_w0 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 2 229064094076558031 = some 229064094076558031 := by decide +kernel
private theorem endpoint_10_56_w2 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 2 2 229064094076558031 = some 229064094076558031 := by decide +kernel
private theorem endpoint_10_56_p4 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 4 229064094076558031 = some 229064094076558031 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 2 2 229064094076558031 229064094076558031 229064094076558031 endpoint_10_56_w0 endpoint_10_56_w2
private theorem endpoint_10_56_w4 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 4 2 229064094076558031 = some 229064094076558031 := by decide +kernel
private theorem endpoint_10_56_p6 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 6 229064094076558031 = some 229064094076558031 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 4 2 229064094076558031 229064094076558031 229064094076558031 endpoint_10_56_p4 endpoint_10_56_w4
private theorem endpoint_10_56_w6 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 6 2 229064094076558031 = some 229064094076558031 := by decide +kernel
private theorem endpoint_10_56_p8 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 8 229064094076558031 = some 229064094076558031 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 6 2 229064094076558031 229064094076558031 229064094076558031 endpoint_10_56_p6 endpoint_10_56_w6
private theorem endpoint_10_56_w8 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 8 1 229064094076558031 = some 229064094076558031 := by decide +kernel
private theorem endpoint_10_56_p9 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 9 229064094076558031 = some 229064094076558031 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 8 1 229064094076558031 229064094076558031 229064094076558031 endpoint_10_56_p8 endpoint_10_56_w8
def endpoint_10_56 : CertifiedEndpoint :=
  ⟨⟨10, 56, 3259⟩, 229064094076558031, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_10_56_flag endpoint_10_56_sources 9 229064094076558031 229064094076558031 rfl endpoint_10_56_base endpoint_10_56_p9) (by decide)⟩
private def endpoint_10_57_flag : Flag := ⟨10, 57, 3222⟩
private def endpoint_10_57_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_57_base : receiptBase endpoint_10_57_flag endpoint_10_57_sources = some 232193197639314076 := by decide +kernel
private theorem endpoint_10_57_w0 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 2 232193197639314076 = some 232193197639314076 := by decide +kernel
private theorem endpoint_10_57_w2 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 2 2 232193197639314076 = some 232193197639314076 := by decide +kernel
private theorem endpoint_10_57_p4 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 4 232193197639314076 = some 232193197639314076 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 2 2 232193197639314076 232193197639314076 232193197639314076 endpoint_10_57_w0 endpoint_10_57_w2
private theorem endpoint_10_57_w4 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 4 2 232193197639314076 = some 232193197639314076 := by decide +kernel
private theorem endpoint_10_57_p6 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 6 232193197639314076 = some 232193197639314076 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 4 2 232193197639314076 232193197639314076 232193197639314076 endpoint_10_57_p4 endpoint_10_57_w4
private theorem endpoint_10_57_w6 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 6 2 232193197639314076 = some 232193197639314076 := by decide +kernel
private theorem endpoint_10_57_p8 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 8 232193197639314076 = some 232193197639314076 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 6 2 232193197639314076 232193197639314076 232193197639314076 endpoint_10_57_p6 endpoint_10_57_w6
private theorem endpoint_10_57_w8 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 8 1 232193197639314076 = some 232193197639314076 := by decide +kernel
private theorem endpoint_10_57_p9 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 9 232193197639314076 = some 232193197639314076 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 8 1 232193197639314076 232193197639314076 232193197639314076 endpoint_10_57_p8 endpoint_10_57_w8
def endpoint_10_57 : CertifiedEndpoint :=
  ⟨⟨10, 57, 3222⟩, 232193197639314076, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_57_flag endpoint_10_57_sources 9 232193197639314076 232193197639314076 rfl endpoint_10_57_base endpoint_10_57_p9) (by decide)⟩
private def endpoint_10_58_flag : Flag := ⟨10, 58, 3184⟩
private def endpoint_10_58_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_58_base : receiptBase endpoint_10_58_flag endpoint_10_58_sources = some 232983247286676486 := by decide +kernel
private theorem endpoint_10_58_w0 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 2 232983247286676486 = some 232983247286676486 := by decide +kernel
private theorem endpoint_10_58_w2 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 2 2 232983247286676486 = some 232983247286676486 := by decide +kernel
private theorem endpoint_10_58_p4 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 4 232983247286676486 = some 232983247286676486 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 2 2 232983247286676486 232983247286676486 232983247286676486 endpoint_10_58_w0 endpoint_10_58_w2
private theorem endpoint_10_58_w4 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 4 2 232983247286676486 = some 232983247286676486 := by decide +kernel
private theorem endpoint_10_58_p6 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 6 232983247286676486 = some 232983247286676486 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 4 2 232983247286676486 232983247286676486 232983247286676486 endpoint_10_58_p4 endpoint_10_58_w4
private theorem endpoint_10_58_w6 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 6 2 232983247286676486 = some 232983247286676486 := by decide +kernel
private theorem endpoint_10_58_p8 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 8 232983247286676486 = some 232983247286676486 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 6 2 232983247286676486 232983247286676486 232983247286676486 endpoint_10_58_p6 endpoint_10_58_w6
private theorem endpoint_10_58_w8 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 8 1 232983247286676486 = some 232983247286676486 := by decide +kernel
private theorem endpoint_10_58_p9 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 9 232983247286676486 = some 232983247286676486 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 8 1 232983247286676486 232983247286676486 232983247286676486 endpoint_10_58_p8 endpoint_10_58_w8
def endpoint_10_58 : CertifiedEndpoint :=
  ⟨⟨10, 58, 3184⟩, 232983247286676486, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_58_flag endpoint_10_58_sources 9 232983247286676486 232983247286676486 rfl endpoint_10_58_base endpoint_10_58_p9) (by decide)⟩
private def endpoint_10_59_flag : Flag := ⟨10, 59, 3145⟩
private def endpoint_10_59_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_59_base : receiptBase endpoint_10_59_flag endpoint_10_59_sources = some 233616151181454064 := by decide +kernel
private theorem endpoint_10_59_w0 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 2 233616151181454064 = some 233616151181454064 := by decide +kernel
private theorem endpoint_10_59_w2 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 2 2 233616151181454064 = some 233616151181454064 := by decide +kernel
private theorem endpoint_10_59_p4 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 4 233616151181454064 = some 233616151181454064 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 2 2 233616151181454064 233616151181454064 233616151181454064 endpoint_10_59_w0 endpoint_10_59_w2
private theorem endpoint_10_59_w4 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 4 2 233616151181454064 = some 233616151181454064 := by decide +kernel
private theorem endpoint_10_59_p6 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 6 233616151181454064 = some 233616151181454064 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 4 2 233616151181454064 233616151181454064 233616151181454064 endpoint_10_59_p4 endpoint_10_59_w4
private theorem endpoint_10_59_w6 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 6 2 233616151181454064 = some 233616151181454064 := by decide +kernel
private theorem endpoint_10_59_p8 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 8 233616151181454064 = some 233616151181454064 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 6 2 233616151181454064 233616151181454064 233616151181454064 endpoint_10_59_p6 endpoint_10_59_w6
private theorem endpoint_10_59_w8 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 8 1 233616151181454064 = some 233616151181454064 := by decide +kernel
private theorem endpoint_10_59_p9 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 9 233616151181454064 = some 233616151181454064 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 8 1 233616151181454064 233616151181454064 233616151181454064 endpoint_10_59_p8 endpoint_10_59_w8
def endpoint_10_59 : CertifiedEndpoint :=
  ⟨⟨10, 59, 3145⟩, 233616151181454064, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_59_flag endpoint_10_59_sources 9 233616151181454064 233616151181454064 rfl endpoint_10_59_base endpoint_10_59_p9) (by decide)⟩
private def endpoint_10_60_flag : Flag := ⟨10, 60, 3105⟩
private def endpoint_10_60_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_60_base : receiptBase endpoint_10_60_flag endpoint_10_60_sources = some 234088644665217450 := by decide +kernel
private theorem endpoint_10_60_w0 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 2 234088644665217450 = some 234088644665217450 := by decide +kernel
private theorem endpoint_10_60_w2 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 2 2 234088644665217450 = some 234088644665217450 := by decide +kernel
private theorem endpoint_10_60_p4 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 4 234088644665217450 = some 234088644665217450 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 2 2 234088644665217450 234088644665217450 234088644665217450 endpoint_10_60_w0 endpoint_10_60_w2
private theorem endpoint_10_60_w4 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 4 2 234088644665217450 = some 234088644665217450 := by decide +kernel
private theorem endpoint_10_60_p6 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 6 234088644665217450 = some 234088644665217450 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 4 2 234088644665217450 234088644665217450 234088644665217450 endpoint_10_60_p4 endpoint_10_60_w4
private theorem endpoint_10_60_w6 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 6 2 234088644665217450 = some 234088644665217450 := by decide +kernel
private theorem endpoint_10_60_p8 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 8 234088644665217450 = some 234088644665217450 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 6 2 234088644665217450 234088644665217450 234088644665217450 endpoint_10_60_p6 endpoint_10_60_w6
private theorem endpoint_10_60_w8 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 8 1 234088644665217450 = some 234088644665217450 := by decide +kernel
private theorem endpoint_10_60_p9 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 9 234088644665217450 = some 234088644665217450 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 8 1 234088644665217450 234088644665217450 234088644665217450 endpoint_10_60_p8 endpoint_10_60_w8
def endpoint_10_60 : CertifiedEndpoint :=
  ⟨⟨10, 60, 3105⟩, 234088644665217450, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_60_flag endpoint_10_60_sources 9 234088644665217450 234088644665217450 rfl endpoint_10_60_base endpoint_10_60_p9) (by decide)⟩
private def endpoint_10_61_flag : Flag := ⟨10, 61, 3062⟩
private def endpoint_10_61_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_61_base : receiptBase endpoint_10_61_flag endpoint_10_61_sources = some 234246404495835696 := by decide +kernel
private theorem endpoint_10_61_w0 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 2 234246404495835696 = some 234246404495835696 := by decide +kernel
private theorem endpoint_10_61_w2 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 2 2 234246404495835696 = some 234246404495835696 := by decide +kernel
private theorem endpoint_10_61_p4 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 4 234246404495835696 = some 234246404495835696 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 2 2 234246404495835696 234246404495835696 234246404495835696 endpoint_10_61_w0 endpoint_10_61_w2
private theorem endpoint_10_61_w4 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 4 2 234246404495835696 = some 234246404495835696 := by decide +kernel
private theorem endpoint_10_61_p6 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 6 234246404495835696 = some 234246404495835696 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 4 2 234246404495835696 234246404495835696 234246404495835696 endpoint_10_61_p4 endpoint_10_61_w4
private theorem endpoint_10_61_w6 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 6 2 234246404495835696 = some 234246404495835696 := by decide +kernel
private theorem endpoint_10_61_p8 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 8 234246404495835696 = some 234246404495835696 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 6 2 234246404495835696 234246404495835696 234246404495835696 endpoint_10_61_p6 endpoint_10_61_w6
private theorem endpoint_10_61_w8 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 8 1 234246404495835696 = some 234246404495835696 := by decide +kernel
private theorem endpoint_10_61_p9 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 9 234246404495835696 = some 234246404495835696 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 8 1 234246404495835696 234246404495835696 234246404495835696 endpoint_10_61_p8 endpoint_10_61_w8
def endpoint_10_61 : CertifiedEndpoint :=
  ⟨⟨10, 61, 3062⟩, 234246404495835696, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_61_flag endpoint_10_61_sources 9 234246404495835696 234246404495835696 rfl endpoint_10_61_base endpoint_10_61_p9) (by decide)⟩
private def endpoint_10_62_flag : Flag := ⟨10, 62, 3018⟩
private def endpoint_10_62_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_10_62_base : receiptBase endpoint_10_62_flag endpoint_10_62_sources = some 235429470564826732 := by decide +kernel
private theorem endpoint_10_62_w0 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 2 235429470564826732 = some 235429470564826732 := by decide +kernel
private theorem endpoint_10_62_w2 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 2 2 235429470564826732 = some 235429470564826732 := by decide +kernel
private theorem endpoint_10_62_p4 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 4 235429470564826732 = some 235429470564826732 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 2 2 235429470564826732 235429470564826732 235429470564826732 endpoint_10_62_w0 endpoint_10_62_w2
private theorem endpoint_10_62_w4 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 4 2 235429470564826732 = some 235429470564826732 := by decide +kernel
private theorem endpoint_10_62_p6 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 6 235429470564826732 = some 235429470564826732 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 4 2 235429470564826732 235429470564826732 235429470564826732 endpoint_10_62_p4 endpoint_10_62_w4
private theorem endpoint_10_62_w6 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 6 2 235429470564826732 = some 235429470564826732 := by decide +kernel
private theorem endpoint_10_62_p8 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 8 235429470564826732 = some 235429470564826732 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 6 2 235429470564826732 235429470564826732 235429470564826732 endpoint_10_62_p6 endpoint_10_62_w6
private theorem endpoint_10_62_w8 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 8 1 235429470564826732 = some 235429470564826732 := by decide +kernel
private theorem endpoint_10_62_p9 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 9 235429470564826732 = some 235429470564826732 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 8 1 235429470564826732 235429470564826732 235429470564826732 endpoint_10_62_p8 endpoint_10_62_w8
def endpoint_10_62 : CertifiedEndpoint :=
  ⟨⟨10, 62, 3018⟩, 235429470564826732, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_10_62_flag endpoint_10_62_sources 9 235429470564826732 235429470564826732 rfl endpoint_10_62_base endpoint_10_62_p9) (by decide)⟩
private def endpoint_10_63_flag : Flag := ⟨10, 63, 2972⟩
private def endpoint_10_63_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_10_63_base : receiptBase endpoint_10_63_flag endpoint_10_63_sources = some 235164792341057820 := by decide +kernel
private theorem endpoint_10_63_w0 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 2 235164792341057820 = some 235164792341057820 := by decide +kernel
private theorem endpoint_10_63_w2 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 2 2 235164792341057820 = some 235164792341057820 := by decide +kernel
private theorem endpoint_10_63_p4 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 4 235164792341057820 = some 235164792341057820 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 2 2 235164792341057820 235164792341057820 235164792341057820 endpoint_10_63_w0 endpoint_10_63_w2
private theorem endpoint_10_63_w4 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 4 2 235164792341057820 = some 235164792341057820 := by decide +kernel
private theorem endpoint_10_63_p6 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 6 235164792341057820 = some 235164792341057820 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 4 2 235164792341057820 235164792341057820 235164792341057820 endpoint_10_63_p4 endpoint_10_63_w4
private theorem endpoint_10_63_w6 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 6 2 235164792341057820 = some 235164792341057820 := by decide +kernel
private theorem endpoint_10_63_p8 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 8 235164792341057820 = some 235164792341057820 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 6 2 235164792341057820 235164792341057820 235164792341057820 endpoint_10_63_p6 endpoint_10_63_w6
private theorem endpoint_10_63_w8 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 8 1 235164792341057820 = some 235164792341057820 := by decide +kernel
private theorem endpoint_10_63_p9 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 9 235164792341057820 = some 235164792341057820 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 8 1 235164792341057820 235164792341057820 235164792341057820 endpoint_10_63_p8 endpoint_10_63_w8
def endpoint_10_63 : CertifiedEndpoint :=
  ⟨⟨10, 63, 2972⟩, 235164792341057820, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_10_63_flag endpoint_10_63_sources 9 235164792341057820 235164792341057820 rfl endpoint_10_63_base endpoint_10_63_p9) (by decide)⟩
private def endpoint_10_64_flag : Flag := ⟨10, 64, 2924⟩
private def endpoint_10_64_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_10_64_base : receiptBase endpoint_10_64_flag endpoint_10_64_sources = some 235891702485830215 := by decide +kernel
private theorem endpoint_10_64_w0 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 2 235891702485830215 = some 235891702485830215 := by decide +kernel
private theorem endpoint_10_64_w2 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 2 2 235891702485830215 = some 235891702485830215 := by decide +kernel
private theorem endpoint_10_64_p4 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 4 235891702485830215 = some 235891702485830215 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 2 2 235891702485830215 235891702485830215 235891702485830215 endpoint_10_64_w0 endpoint_10_64_w2
private theorem endpoint_10_64_w4 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 4 2 235891702485830215 = some 235891702485830215 := by decide +kernel
private theorem endpoint_10_64_p6 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 6 235891702485830215 = some 235891702485830215 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 4 2 235891702485830215 235891702485830215 235891702485830215 endpoint_10_64_p4 endpoint_10_64_w4
private theorem endpoint_10_64_w6 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 6 2 235891702485830215 = some 235891702485830215 := by decide +kernel
private theorem endpoint_10_64_p8 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 8 235891702485830215 = some 235891702485830215 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 6 2 235891702485830215 235891702485830215 235891702485830215 endpoint_10_64_p6 endpoint_10_64_w6
private theorem endpoint_10_64_w8 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 8 1 235891702485830215 = some 235891702485830215 := by decide +kernel
private theorem endpoint_10_64_p9 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 9 235891702485830215 = some 235891702485830215 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 8 1 235891702485830215 235891702485830215 235891702485830215 endpoint_10_64_p8 endpoint_10_64_w8
def endpoint_10_64 : CertifiedEndpoint :=
  ⟨⟨10, 64, 2924⟩, 235891702485830215, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_10_64_flag endpoint_10_64_sources 9 235891702485830215 235891702485830215 rfl endpoint_10_64_base endpoint_10_64_p9) (by decide)⟩
private def endpoint_10_65_flag : Flag := ⟨10, 65, 2874⟩
private def endpoint_10_65_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_10_65_base : receiptBase endpoint_10_65_flag endpoint_10_65_sources = some 235097744692885110 := by decide +kernel
private theorem endpoint_10_65_w0 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 2 235097744692885110 = some 235097744692885110 := by decide +kernel
private theorem endpoint_10_65_w2 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 2 2 235097744692885110 = some 235097744692885110 := by decide +kernel
private theorem endpoint_10_65_p4 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 4 235097744692885110 = some 235097744692885110 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 2 2 235097744692885110 235097744692885110 235097744692885110 endpoint_10_65_w0 endpoint_10_65_w2
private theorem endpoint_10_65_w4 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 4 2 235097744692885110 = some 235097744692885110 := by decide +kernel
private theorem endpoint_10_65_p6 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 6 235097744692885110 = some 235097744692885110 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 4 2 235097744692885110 235097744692885110 235097744692885110 endpoint_10_65_p4 endpoint_10_65_w4
private theorem endpoint_10_65_w6 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 6 2 235097744692885110 = some 235097744692885110 := by decide +kernel
private theorem endpoint_10_65_p8 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 8 235097744692885110 = some 235097744692885110 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 6 2 235097744692885110 235097744692885110 235097744692885110 endpoint_10_65_p6 endpoint_10_65_w6
private theorem endpoint_10_65_w8 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 8 1 235097744692885110 = some 235097744692885110 := by decide +kernel
private theorem endpoint_10_65_p9 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 9 235097744692885110 = some 235097744692885110 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 8 1 235097744692885110 235097744692885110 235097744692885110 endpoint_10_65_p8 endpoint_10_65_w8
def endpoint_10_65 : CertifiedEndpoint :=
  ⟨⟨10, 65, 2874⟩, 235097744692885110, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_10_65_flag endpoint_10_65_sources 9 235097744692885110 235097744692885110 rfl endpoint_10_65_base endpoint_10_65_p9) (by decide)⟩
private def endpoint_10_66_flag : Flag := ⟨10, 66, 2821⟩
private def endpoint_10_66_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_10_66_base : receiptBase endpoint_10_66_flag endpoint_10_66_sources = some 235242660503203469 := by decide +kernel
private theorem endpoint_10_66_w0 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 2 235242660503203469 = some 235242660503203469 := by decide +kernel
private theorem endpoint_10_66_w2 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 2 2 235242660503203469 = some 235242660503203469 := by decide +kernel
private theorem endpoint_10_66_p4 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 4 235242660503203469 = some 235242660503203469 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 2 2 235242660503203469 235242660503203469 235242660503203469 endpoint_10_66_w0 endpoint_10_66_w2
private theorem endpoint_10_66_w4 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 4 2 235242660503203469 = some 235242660503203469 := by decide +kernel
private theorem endpoint_10_66_p6 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 6 235242660503203469 = some 235242660503203469 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 4 2 235242660503203469 235242660503203469 235242660503203469 endpoint_10_66_p4 endpoint_10_66_w4
private theorem endpoint_10_66_w6 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 6 2 235242660503203469 = some 235242660503203469 := by decide +kernel
private theorem endpoint_10_66_p8 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 8 235242660503203469 = some 235242660503203469 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 6 2 235242660503203469 235242660503203469 235242660503203469 endpoint_10_66_p6 endpoint_10_66_w6
private theorem endpoint_10_66_w8 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 8 1 235242660503203469 = some 235242660503203469 := by decide +kernel
private theorem endpoint_10_66_p9 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 9 235242660503203469 = some 235242660503203469 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 8 1 235242660503203469 235242660503203469 235242660503203469 endpoint_10_66_p8 endpoint_10_66_w8
def endpoint_10_66 : CertifiedEndpoint :=
  ⟨⟨10, 66, 2821⟩, 235242660503203469, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_10_66_flag endpoint_10_66_sources 9 235242660503203469 235242660503203469 rfl endpoint_10_66_base endpoint_10_66_p9) (by decide)⟩
private def endpoint_10_67_flag : Flag := ⟨10, 67, 2765⟩
private def endpoint_10_67_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_10_67_base : receiptBase endpoint_10_67_flag endpoint_10_67_sources = some 235044417471627623 := by decide +kernel
private theorem endpoint_10_67_w0 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 2 235044417471627623 = some 235044417471627623 := by decide +kernel
private theorem endpoint_10_67_w2 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 2 2 235044417471627623 = some 235044417471627623 := by decide +kernel
private theorem endpoint_10_67_p4 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 4 235044417471627623 = some 235044417471627623 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 2 2 235044417471627623 235044417471627623 235044417471627623 endpoint_10_67_w0 endpoint_10_67_w2
private theorem endpoint_10_67_w4 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 4 2 235044417471627623 = some 235044417471627623 := by decide +kernel
private theorem endpoint_10_67_p6 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 6 235044417471627623 = some 235044417471627623 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 4 2 235044417471627623 235044417471627623 235044417471627623 endpoint_10_67_p4 endpoint_10_67_w4
private theorem endpoint_10_67_w6 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 6 2 235044417471627623 = some 235044417471627623 := by decide +kernel
private theorem endpoint_10_67_p8 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 8 235044417471627623 = some 235044417471627623 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 6 2 235044417471627623 235044417471627623 235044417471627623 endpoint_10_67_p6 endpoint_10_67_w6
private theorem endpoint_10_67_w8 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 8 1 235044417471627623 = some 235044417471627623 := by decide +kernel
private theorem endpoint_10_67_p9 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 9 235044417471627623 = some 235044417471627623 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 8 1 235044417471627623 235044417471627623 235044417471627623 endpoint_10_67_p8 endpoint_10_67_w8
def endpoint_10_67 : CertifiedEndpoint :=
  ⟨⟨10, 67, 2765⟩, 235044417471627623, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_10_67_flag endpoint_10_67_sources 9 235044417471627623 235044417471627623 rfl endpoint_10_67_base endpoint_10_67_p9) (by decide)⟩
private def endpoint_10_68_flag : Flag := ⟨10, 68, 2707⟩
private def endpoint_10_68_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_68_base : receiptBase endpoint_10_68_flag endpoint_10_68_sources = some 234425518133667325 := by decide +kernel
private theorem endpoint_10_68_w0 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 2 234425518133667325 = some 234425518133667325 := by decide +kernel
private theorem endpoint_10_68_w2 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 2 2 234425518133667325 = some 234425518133667325 := by decide +kernel
private theorem endpoint_10_68_p4 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 4 234425518133667325 = some 234425518133667325 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 2 2 234425518133667325 234425518133667325 234425518133667325 endpoint_10_68_w0 endpoint_10_68_w2
private theorem endpoint_10_68_w4 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 4 2 234425518133667325 = some 234425518133667325 := by decide +kernel
private theorem endpoint_10_68_p6 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 6 234425518133667325 = some 234425518133667325 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 4 2 234425518133667325 234425518133667325 234425518133667325 endpoint_10_68_p4 endpoint_10_68_w4
private theorem endpoint_10_68_w6 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 6 2 234425518133667325 = some 234425518133667325 := by decide +kernel
private theorem endpoint_10_68_p8 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 8 234425518133667325 = some 234425518133667325 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 6 2 234425518133667325 234425518133667325 234425518133667325 endpoint_10_68_p6 endpoint_10_68_w6
private theorem endpoint_10_68_w8 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 8 1 234425518133667325 = some 234425518133667325 := by decide +kernel
private theorem endpoint_10_68_p9 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 9 234425518133667325 = some 234425518133667325 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 8 1 234425518133667325 234425518133667325 234425518133667325 endpoint_10_68_p8 endpoint_10_68_w8
def endpoint_10_68 : CertifiedEndpoint :=
  ⟨⟨10, 68, 2707⟩, 234425518133667325, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_68_flag endpoint_10_68_sources 9 234425518133667325 234425518133667325 rfl endpoint_10_68_base endpoint_10_68_p9) (by decide)⟩
private def endpoint_10_69_flag : Flag := ⟨10, 69, 2646⟩
private def endpoint_10_69_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_69_base : receiptBase endpoint_10_69_flag endpoint_10_69_sources = some 232196370504017301 := by decide +kernel
private theorem endpoint_10_69_w0 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 2 232196370504017301 = some 232196370504017301 := by decide +kernel
private theorem endpoint_10_69_w2 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 2 2 232196370504017301 = some 232196370504017301 := by decide +kernel
private theorem endpoint_10_69_p4 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 4 232196370504017301 = some 232196370504017301 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 2 2 232196370504017301 232196370504017301 232196370504017301 endpoint_10_69_w0 endpoint_10_69_w2
private theorem endpoint_10_69_w4 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 4 2 232196370504017301 = some 232196370504017301 := by decide +kernel
private theorem endpoint_10_69_p6 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 6 232196370504017301 = some 232196370504017301 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 4 2 232196370504017301 232196370504017301 232196370504017301 endpoint_10_69_p4 endpoint_10_69_w4
private theorem endpoint_10_69_w6 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 6 2 232196370504017301 = some 232196370504017301 := by decide +kernel
private theorem endpoint_10_69_p8 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 8 232196370504017301 = some 232196370504017301 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 6 2 232196370504017301 232196370504017301 232196370504017301 endpoint_10_69_p6 endpoint_10_69_w6
private theorem endpoint_10_69_w8 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 8 1 232196370504017301 = some 232196370504017301 := by decide +kernel
private theorem endpoint_10_69_p9 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 9 232196370504017301 = some 232196370504017301 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 8 1 232196370504017301 232196370504017301 232196370504017301 endpoint_10_69_p8 endpoint_10_69_w8
def endpoint_10_69 : CertifiedEndpoint :=
  ⟨⟨10, 69, 2646⟩, 232196370504017301, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_69_flag endpoint_10_69_sources 9 232196370504017301 232196370504017301 rfl endpoint_10_69_base endpoint_10_69_p9) (by decide)⟩
private def endpoint_10_70_flag : Flag := ⟨10, 70, 2583⟩
private def endpoint_10_70_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_70_base : receiptBase endpoint_10_70_flag endpoint_10_70_sources = some 229651822949374706 := by decide +kernel
private theorem endpoint_10_70_w0 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 2 229651822949374706 = some 229651822949374706 := by decide +kernel
private theorem endpoint_10_70_w2 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 2 2 229651822949374706 = some 229651822949374706 := by decide +kernel
private theorem endpoint_10_70_p4 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 4 229651822949374706 = some 229651822949374706 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 2 2 229651822949374706 229651822949374706 229651822949374706 endpoint_10_70_w0 endpoint_10_70_w2
private theorem endpoint_10_70_w4 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 4 2 229651822949374706 = some 229651822949374706 := by decide +kernel
private theorem endpoint_10_70_p6 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 6 229651822949374706 = some 229651822949374706 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 4 2 229651822949374706 229651822949374706 229651822949374706 endpoint_10_70_p4 endpoint_10_70_w4
private theorem endpoint_10_70_w6 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 6 2 229651822949374706 = some 229651822949374706 := by decide +kernel
private theorem endpoint_10_70_p8 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 8 229651822949374706 = some 229651822949374706 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 6 2 229651822949374706 229651822949374706 229651822949374706 endpoint_10_70_p6 endpoint_10_70_w6
private theorem endpoint_10_70_w8 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 8 1 229651822949374706 = some 229651822949374706 := by decide +kernel
private theorem endpoint_10_70_p9 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 9 229651822949374706 = some 229651822949374706 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 8 1 229651822949374706 229651822949374706 229651822949374706 endpoint_10_70_p8 endpoint_10_70_w8
def endpoint_10_70 : CertifiedEndpoint :=
  ⟨⟨10, 70, 2583⟩, 229651822949374706, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_70_flag endpoint_10_70_sources 9 229651822949374706 229651822949374706 rfl endpoint_10_70_base endpoint_10_70_p9) (by decide)⟩
private def endpoint_10_71_flag : Flag := ⟨10, 71, 2517⟩
private def endpoint_10_71_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_71_base : receiptBase endpoint_10_71_flag endpoint_10_71_sources = some 226695936001798454 := by decide +kernel
private theorem endpoint_10_71_w0 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 2 226695936001798454 = some 226695936001798454 := by decide +kernel
private theorem endpoint_10_71_w2 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 2 2 226695936001798454 = some 226695936001798454 := by decide +kernel
private theorem endpoint_10_71_p4 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 4 226695936001798454 = some 226695936001798454 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 2 2 226695936001798454 226695936001798454 226695936001798454 endpoint_10_71_w0 endpoint_10_71_w2
private theorem endpoint_10_71_w4 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 4 2 226695936001798454 = some 226695936001798454 := by decide +kernel
private theorem endpoint_10_71_p6 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 6 226695936001798454 = some 226695936001798454 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 4 2 226695936001798454 226695936001798454 226695936001798454 endpoint_10_71_p4 endpoint_10_71_w4
private theorem endpoint_10_71_w6 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 6 2 226695936001798454 = some 226695936001798454 := by decide +kernel
private theorem endpoint_10_71_p8 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 8 226695936001798454 = some 226695936001798454 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 6 2 226695936001798454 226695936001798454 226695936001798454 endpoint_10_71_p6 endpoint_10_71_w6
private theorem endpoint_10_71_w8 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 8 1 226695936001798454 = some 226695936001798454 := by decide +kernel
private theorem endpoint_10_71_p9 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 9 226695936001798454 = some 226695936001798454 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 8 1 226695936001798454 226695936001798454 226695936001798454 endpoint_10_71_p8 endpoint_10_71_w8
def endpoint_10_71 : CertifiedEndpoint :=
  ⟨⟨10, 71, 2517⟩, 226695936001798454, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_71_flag endpoint_10_71_sources 9 226695936001798454 226695936001798454 rfl endpoint_10_71_base endpoint_10_71_p9) (by decide)⟩
private def endpoint_10_72_flag : Flag := ⟨10, 72, 2449⟩
private def endpoint_10_72_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_10_72_base : receiptBase endpoint_10_72_flag endpoint_10_72_sources = some 228206415699127500 := by decide +kernel
private theorem endpoint_10_72_w0 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 2 228206415699127500 = some 228206415699127500 := by decide +kernel
private theorem endpoint_10_72_w2 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 2 2 228206415699127500 = some 228206415699127500 := by decide +kernel
private theorem endpoint_10_72_p4 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 4 228206415699127500 = some 228206415699127500 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 2 2 228206415699127500 228206415699127500 228206415699127500 endpoint_10_72_w0 endpoint_10_72_w2
private theorem endpoint_10_72_w4 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 4 2 228206415699127500 = some 228206415699127500 := by decide +kernel
private theorem endpoint_10_72_p6 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 6 228206415699127500 = some 228206415699127500 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 4 2 228206415699127500 228206415699127500 228206415699127500 endpoint_10_72_p4 endpoint_10_72_w4
private theorem endpoint_10_72_w6 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 6 2 228206415699127500 = some 228206415699127500 := by decide +kernel
private theorem endpoint_10_72_p8 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 8 228206415699127500 = some 228206415699127500 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 6 2 228206415699127500 228206415699127500 228206415699127500 endpoint_10_72_p6 endpoint_10_72_w6
private theorem endpoint_10_72_w8 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 8 1 228206415699127500 = some 228206415699127500 := by decide +kernel
private theorem endpoint_10_72_p9 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 9 228206415699127500 = some 228206415699127500 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 8 1 228206415699127500 228206415699127500 228206415699127500 endpoint_10_72_p8 endpoint_10_72_w8
def endpoint_10_72 : CertifiedEndpoint :=
  ⟨⟨10, 72, 2449⟩, 228206415699127500, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_10_72_flag endpoint_10_72_sources 9 228206415699127500 228206415699127500 rfl endpoint_10_72_base endpoint_10_72_p9) (by decide)⟩
private def endpoint_10_73_flag : Flag := ⟨10, 73, 2378⟩
private def endpoint_10_73_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_10_73_base : receiptBase endpoint_10_73_flag endpoint_10_73_sources = some 224456061861689605 := by decide +kernel
private theorem endpoint_10_73_w0 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 2 224456061861689605 = some 224456061861689605 := by decide +kernel
private theorem endpoint_10_73_w2 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 2 2 224456061861689605 = some 224456061861689605 := by decide +kernel
private theorem endpoint_10_73_p4 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 4 224456061861689605 = some 224456061861689605 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 2 2 224456061861689605 224456061861689605 224456061861689605 endpoint_10_73_w0 endpoint_10_73_w2
private theorem endpoint_10_73_w4 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 4 2 224456061861689605 = some 224456061861689605 := by decide +kernel
private theorem endpoint_10_73_p6 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 6 224456061861689605 = some 224456061861689605 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 4 2 224456061861689605 224456061861689605 224456061861689605 endpoint_10_73_p4 endpoint_10_73_w4
private theorem endpoint_10_73_w6 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 6 2 224456061861689605 = some 224456061861689605 := by decide +kernel
private theorem endpoint_10_73_p8 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 8 224456061861689605 = some 224456061861689605 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 6 2 224456061861689605 224456061861689605 224456061861689605 endpoint_10_73_p6 endpoint_10_73_w6
private theorem endpoint_10_73_w8 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 8 1 224456061861689605 = some 224456061861689605 := by decide +kernel
private theorem endpoint_10_73_p9 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 9 224456061861689605 = some 224456061861689605 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 8 1 224456061861689605 224456061861689605 224456061861689605 endpoint_10_73_p8 endpoint_10_73_w8
def endpoint_10_73 : CertifiedEndpoint :=
  ⟨⟨10, 73, 2378⟩, 224456061861689605, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_10_73_flag endpoint_10_73_sources 9 224456061861689605 224456061861689605 rfl endpoint_10_73_base endpoint_10_73_p9) (by decide)⟩
private def endpoint_10_74_flag : Flag := ⟨10, 74, 2304⟩
private def endpoint_10_74_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_10_74_base : receiptBase endpoint_10_74_flag endpoint_10_74_sources = some 220262574159194469 := by decide +kernel
private theorem endpoint_10_74_w0 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 2 220262574159194469 = some 220262574159194469 := by decide +kernel
private theorem endpoint_10_74_w2 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 2 2 220262574159194469 = some 220262574159194469 := by decide +kernel
private theorem endpoint_10_74_p4 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 4 220262574159194469 = some 220262574159194469 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 2 2 220262574159194469 220262574159194469 220262574159194469 endpoint_10_74_w0 endpoint_10_74_w2
private theorem endpoint_10_74_w4 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 4 2 220262574159194469 = some 220262574159194469 := by decide +kernel
private theorem endpoint_10_74_p6 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 6 220262574159194469 = some 220262574159194469 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 4 2 220262574159194469 220262574159194469 220262574159194469 endpoint_10_74_p4 endpoint_10_74_w4
private theorem endpoint_10_74_w6 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 6 2 220262574159194469 = some 220262574159194469 := by decide +kernel
private theorem endpoint_10_74_p8 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 8 220262574159194469 = some 220262574159194469 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 6 2 220262574159194469 220262574159194469 220262574159194469 endpoint_10_74_p6 endpoint_10_74_w6
private theorem endpoint_10_74_w8 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 8 1 220262574159194469 = some 220262574159194469 := by decide +kernel
private theorem endpoint_10_74_p9 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 9 220262574159194469 = some 220262574159194469 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 8 1 220262574159194469 220262574159194469 220262574159194469 endpoint_10_74_p8 endpoint_10_74_w8
def endpoint_10_74 : CertifiedEndpoint :=
  ⟨⟨10, 74, 2304⟩, 220262574159194469, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_10_74_flag endpoint_10_74_sources 9 220262574159194469 220262574159194469 rfl endpoint_10_74_base endpoint_10_74_p9) (by decide)⟩
private def endpoint_10_75_flag : Flag := ⟨10, 75, 2228⟩
private def endpoint_10_75_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_10_75_base : receiptBase endpoint_10_75_flag endpoint_10_75_sources = some 217434062559883102 := by decide +kernel
private theorem endpoint_10_75_w0 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 2 217434062559883102 = some 217434062559883102 := by decide +kernel
private theorem endpoint_10_75_w2 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 2 2 217434062559883102 = some 217434062559883102 := by decide +kernel
private theorem endpoint_10_75_p4 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 4 217434062559883102 = some 217434062559883102 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 2 2 217434062559883102 217434062559883102 217434062559883102 endpoint_10_75_w0 endpoint_10_75_w2
private theorem endpoint_10_75_w4 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 4 2 217434062559883102 = some 217434062559883102 := by decide +kernel
private theorem endpoint_10_75_p6 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 6 217434062559883102 = some 217434062559883102 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 4 2 217434062559883102 217434062559883102 217434062559883102 endpoint_10_75_p4 endpoint_10_75_w4
private theorem endpoint_10_75_w6 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 6 2 217434062559883102 = some 217434062559883102 := by decide +kernel
private theorem endpoint_10_75_p8 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 8 217434062559883102 = some 217434062559883102 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 6 2 217434062559883102 217434062559883102 217434062559883102 endpoint_10_75_p6 endpoint_10_75_w6
private theorem endpoint_10_75_w8 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 8 1 217434062559883102 = some 217434062559883102 := by decide +kernel
private theorem endpoint_10_75_p9 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 9 217434062559883102 = some 217434062559883102 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 8 1 217434062559883102 217434062559883102 217434062559883102 endpoint_10_75_p8 endpoint_10_75_w8
def endpoint_10_75 : CertifiedEndpoint :=
  ⟨⟨10, 75, 2228⟩, 217434062559883102, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_10_75_flag endpoint_10_75_sources 9 217434062559883102 217434062559883102 rfl endpoint_10_75_base endpoint_10_75_p9) (by decide)⟩
private def endpoint_10_76_flag : Flag := ⟨10, 76, 2149⟩
private def endpoint_10_76_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_10_76_base : receiptBase endpoint_10_76_flag endpoint_10_76_sources = some 212299878994686706 := by decide +kernel
private theorem endpoint_10_76_w0 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 2 212299878994686706 = some 212299878994686706 := by decide +kernel
private theorem endpoint_10_76_w2 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 2 2 212299878994686706 = some 212299878994686706 := by decide +kernel
private theorem endpoint_10_76_p4 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 4 212299878994686706 = some 212299878994686706 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 2 2 212299878994686706 212299878994686706 212299878994686706 endpoint_10_76_w0 endpoint_10_76_w2
private theorem endpoint_10_76_w4 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 4 2 212299878994686706 = some 212299878994686706 := by decide +kernel
private theorem endpoint_10_76_p6 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 6 212299878994686706 = some 212299878994686706 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 4 2 212299878994686706 212299878994686706 212299878994686706 endpoint_10_76_p4 endpoint_10_76_w4
private theorem endpoint_10_76_w6 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 6 2 212299878994686706 = some 212299878994686706 := by decide +kernel
private theorem endpoint_10_76_p8 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 8 212299878994686706 = some 212299878994686706 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 6 2 212299878994686706 212299878994686706 212299878994686706 endpoint_10_76_p6 endpoint_10_76_w6
private theorem endpoint_10_76_w8 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 8 1 212299878994686706 = some 212299878994686706 := by decide +kernel
private theorem endpoint_10_76_p9 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 9 212299878994686706 = some 212299878994686706 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 8 1 212299878994686706 212299878994686706 212299878994686706 endpoint_10_76_p8 endpoint_10_76_w8
def endpoint_10_76 : CertifiedEndpoint :=
  ⟨⟨10, 76, 2149⟩, 212299878994686706, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_10_76_flag endpoint_10_76_sources 9 212299878994686706 212299878994686706 rfl endpoint_10_76_base endpoint_10_76_p9) (by decide)⟩
private def endpoint_10_77_flag : Flag := ⟨10, 77, 2067⟩
private def endpoint_10_77_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_10_77_base : receiptBase endpoint_10_77_flag endpoint_10_77_sources = some 208549281991463733 := by decide +kernel
private theorem endpoint_10_77_w0 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 2 208549281991463733 = some 208549281991463733 := by decide +kernel
private theorem endpoint_10_77_w2 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 2 2 208549281991463733 = some 208549281991463733 := by decide +kernel
private theorem endpoint_10_77_p4 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 4 208549281991463733 = some 208549281991463733 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 2 2 208549281991463733 208549281991463733 208549281991463733 endpoint_10_77_w0 endpoint_10_77_w2
private theorem endpoint_10_77_w4 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 4 2 208549281991463733 = some 208549281991463733 := by decide +kernel
private theorem endpoint_10_77_p6 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 6 208549281991463733 = some 208549281991463733 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 4 2 208549281991463733 208549281991463733 208549281991463733 endpoint_10_77_p4 endpoint_10_77_w4
private theorem endpoint_10_77_w6 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 6 2 208549281991463733 = some 208549281991463733 := by decide +kernel
private theorem endpoint_10_77_p8 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 8 208549281991463733 = some 208549281991463733 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 6 2 208549281991463733 208549281991463733 208549281991463733 endpoint_10_77_p6 endpoint_10_77_w6
private theorem endpoint_10_77_w8 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 8 1 208549281991463733 = some 208549281991463733 := by decide +kernel
private theorem endpoint_10_77_p9 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 9 208549281991463733 = some 208549281991463733 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 8 1 208549281991463733 208549281991463733 208549281991463733 endpoint_10_77_p8 endpoint_10_77_w8
def endpoint_10_77 : CertifiedEndpoint :=
  ⟨⟨10, 77, 2067⟩, 208549281991463733, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_10_77_flag endpoint_10_77_sources 9 208549281991463733 208549281991463733 rfl endpoint_10_77_base endpoint_10_77_p9) (by decide)⟩
private def endpoint_10_78_flag : Flag := ⟨10, 78, 1983⟩
private def endpoint_10_78_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_10_78_base : receiptBase endpoint_10_78_flag endpoint_10_78_sources = some 204395982091851622 := by decide +kernel
private theorem endpoint_10_78_w0 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 2 204395982091851622 = some 204395982091851622 := by decide +kernel
private theorem endpoint_10_78_w2 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 2 2 204395982091851622 = some 204395982091851622 := by decide +kernel
private theorem endpoint_10_78_p4 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 4 204395982091851622 = some 204395982091851622 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 2 2 204395982091851622 204395982091851622 204395982091851622 endpoint_10_78_w0 endpoint_10_78_w2
private theorem endpoint_10_78_w4 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 4 2 204395982091851622 = some 204395982091851622 := by decide +kernel
private theorem endpoint_10_78_p6 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 6 204395982091851622 = some 204395982091851622 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 4 2 204395982091851622 204395982091851622 204395982091851622 endpoint_10_78_p4 endpoint_10_78_w4
private theorem endpoint_10_78_w6 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 6 2 204395982091851622 = some 204395982091851622 := by decide +kernel
private theorem endpoint_10_78_p8 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 8 204395982091851622 = some 204395982091851622 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 6 2 204395982091851622 204395982091851622 204395982091851622 endpoint_10_78_p6 endpoint_10_78_w6
private theorem endpoint_10_78_w8 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 8 1 204395982091851622 = some 204395982091851622 := by decide +kernel
private theorem endpoint_10_78_p9 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 9 204395982091851622 = some 204395982091851622 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 8 1 204395982091851622 204395982091851622 204395982091851622 endpoint_10_78_p8 endpoint_10_78_w8
def endpoint_10_78 : CertifiedEndpoint :=
  ⟨⟨10, 78, 1983⟩, 204395982091851622, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_10_78_flag endpoint_10_78_sources 9 204395982091851622 204395982091851622 rfl endpoint_10_78_base endpoint_10_78_p9) (by decide)⟩
private def endpoint_10_79_flag : Flag := ⟨10, 79, 1896⟩
private def endpoint_10_79_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_10_79_base : receiptBase endpoint_10_79_flag endpoint_10_79_sources = some 197734081776211553 := by decide +kernel
private theorem endpoint_10_79_w0 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 2 197734081776211553 = some 197734081776211553 := by decide +kernel
private theorem endpoint_10_79_w2 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 2 2 197734081776211553 = some 197734081776211553 := by decide +kernel
private theorem endpoint_10_79_p4 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 4 197734081776211553 = some 197734081776211553 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 2 2 197734081776211553 197734081776211553 197734081776211553 endpoint_10_79_w0 endpoint_10_79_w2
private theorem endpoint_10_79_w4 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 4 2 197734081776211553 = some 197734081776211553 := by decide +kernel
private theorem endpoint_10_79_p6 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 6 197734081776211553 = some 197734081776211553 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 4 2 197734081776211553 197734081776211553 197734081776211553 endpoint_10_79_p4 endpoint_10_79_w4
private theorem endpoint_10_79_w6 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 6 2 197734081776211553 = some 197734081776211553 := by decide +kernel
private theorem endpoint_10_79_p8 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 8 197734081776211553 = some 197734081776211553 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 6 2 197734081776211553 197734081776211553 197734081776211553 endpoint_10_79_p6 endpoint_10_79_w6
private theorem endpoint_10_79_w8 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 8 1 197734081776211553 = some 197734081776211553 := by decide +kernel
private theorem endpoint_10_79_p9 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 9 197734081776211553 = some 197734081776211553 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 8 1 197734081776211553 197734081776211553 197734081776211553 endpoint_10_79_p8 endpoint_10_79_w8
def endpoint_10_79 : CertifiedEndpoint :=
  ⟨⟨10, 79, 1896⟩, 197734081776211553, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_10_79_flag endpoint_10_79_sources 9 197734081776211553 197734081776211553 rfl endpoint_10_79_base endpoint_10_79_p9) (by decide)⟩
private def endpoint_10_80_flag : Flag := ⟨10, 80, 1807⟩
private def endpoint_10_80_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_10_80_base : receiptBase endpoint_10_80_flag endpoint_10_80_sources = some 190656156240189170 := by decide +kernel
private theorem endpoint_10_80_w0 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 2 190656156240189170 = some 190656156240189170 := by decide +kernel
private theorem endpoint_10_80_w2 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 2 2 190656156240189170 = some 190656156240189170 := by decide +kernel
private theorem endpoint_10_80_p4 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 4 190656156240189170 = some 190656156240189170 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 2 2 190656156240189170 190656156240189170 190656156240189170 endpoint_10_80_w0 endpoint_10_80_w2
private theorem endpoint_10_80_w4 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 4 2 190656156240189170 = some 190656156240189170 := by decide +kernel
private theorem endpoint_10_80_p6 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 6 190656156240189170 = some 190656156240189170 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 4 2 190656156240189170 190656156240189170 190656156240189170 endpoint_10_80_p4 endpoint_10_80_w4
private theorem endpoint_10_80_w6 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 6 2 190656156240189170 = some 190656156240189170 := by decide +kernel
private theorem endpoint_10_80_p8 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 8 190656156240189170 = some 190656156240189170 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 6 2 190656156240189170 190656156240189170 190656156240189170 endpoint_10_80_p6 endpoint_10_80_w6
private theorem endpoint_10_80_w8 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 8 1 190656156240189170 = some 190656156240189170 := by decide +kernel
private theorem endpoint_10_80_p9 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 9 190656156240189170 = some 190656156240189170 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 8 1 190656156240189170 190656156240189170 190656156240189170 endpoint_10_80_p8 endpoint_10_80_w8
def endpoint_10_80 : CertifiedEndpoint :=
  ⟨⟨10, 80, 1807⟩, 190656156240189170, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_10_80_flag endpoint_10_80_sources 9 190656156240189170 190656156240189170 rfl endpoint_10_80_base endpoint_10_80_p9) (by decide)⟩
private def endpoint_10_81_flag : Flag := ⟨10, 81, 1715⟩
private def endpoint_10_81_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_81_base : receiptBase endpoint_10_81_flag endpoint_10_81_sources = some 186676622772265162 := by decide +kernel
private theorem endpoint_10_81_w0 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 2 186676622772265162 = some 186676622772265162 := by decide +kernel
private theorem endpoint_10_81_w2 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 2 2 186676622772265162 = some 186676622772265162 := by decide +kernel
private theorem endpoint_10_81_p4 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 4 186676622772265162 = some 186676622772265162 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 2 2 186676622772265162 186676622772265162 186676622772265162 endpoint_10_81_w0 endpoint_10_81_w2
private theorem endpoint_10_81_w4 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 4 2 186676622772265162 = some 186676622772265162 := by decide +kernel
private theorem endpoint_10_81_p6 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 6 186676622772265162 = some 186676622772265162 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 4 2 186676622772265162 186676622772265162 186676622772265162 endpoint_10_81_p4 endpoint_10_81_w4
private theorem endpoint_10_81_w6 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 6 2 186676622772265162 = some 186676622772265162 := by decide +kernel
private theorem endpoint_10_81_p8 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 8 186676622772265162 = some 186676622772265162 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 6 2 186676622772265162 186676622772265162 186676622772265162 endpoint_10_81_p6 endpoint_10_81_w6
private theorem endpoint_10_81_w8 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 8 1 186676622772265162 = some 186676622772265162 := by decide +kernel
private theorem endpoint_10_81_p9 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 9 186676622772265162 = some 186676622772265162 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 8 1 186676622772265162 186676622772265162 186676622772265162 endpoint_10_81_p8 endpoint_10_81_w8
def endpoint_10_81 : CertifiedEndpoint :=
  ⟨⟨10, 81, 1715⟩, 186676622772265162, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_81_flag endpoint_10_81_sources 9 186676622772265162 186676622772265162 rfl endpoint_10_81_base endpoint_10_81_p9) (by decide)⟩
private def endpoint_10_82_flag : Flag := ⟨10, 82, 1620⟩
private def endpoint_10_82_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_82_base : receiptBase endpoint_10_82_flag endpoint_10_82_sources = some 178319269726549750 := by decide +kernel
private theorem endpoint_10_82_w0 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 2 178319269726549750 = some 178319269726549750 := by decide +kernel
private theorem endpoint_10_82_w2 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 2 2 178319269726549750 = some 178319269726549750 := by decide +kernel
private theorem endpoint_10_82_p4 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 4 178319269726549750 = some 178319269726549750 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 2 2 178319269726549750 178319269726549750 178319269726549750 endpoint_10_82_w0 endpoint_10_82_w2
private theorem endpoint_10_82_w4 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 4 2 178319269726549750 = some 178319269726549750 := by decide +kernel
private theorem endpoint_10_82_p6 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 6 178319269726549750 = some 178319269726549750 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 4 2 178319269726549750 178319269726549750 178319269726549750 endpoint_10_82_p4 endpoint_10_82_w4
private theorem endpoint_10_82_w6 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 6 2 178319269726549750 = some 178319269726549750 := by decide +kernel
private theorem endpoint_10_82_p8 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 8 178319269726549750 = some 178319269726549750 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 6 2 178319269726549750 178319269726549750 178319269726549750 endpoint_10_82_p6 endpoint_10_82_w6
private theorem endpoint_10_82_w8 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 8 1 178319269726549750 = some 178319269726549750 := by decide +kernel
private theorem endpoint_10_82_p9 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 9 178319269726549750 = some 178319269726549750 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 8 1 178319269726549750 178319269726549750 178319269726549750 endpoint_10_82_p8 endpoint_10_82_w8
def endpoint_10_82 : CertifiedEndpoint :=
  ⟨⟨10, 82, 1620⟩, 178319269726549750, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_82_flag endpoint_10_82_sources 9 178319269726549750 178319269726549750 rfl endpoint_10_82_base endpoint_10_82_p9) (by decide)⟩
private def endpoint_10_83_flag : Flag := ⟨10, 83, 1522⟩
private def endpoint_10_83_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_83_base : receiptBase endpoint_10_83_flag endpoint_10_83_sources = some 169397733620832565 := by decide +kernel
private theorem endpoint_10_83_w0 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 0 2 169397733620832565 = some 169397733620832565 := by decide +kernel
private theorem endpoint_10_83_w2 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 2 2 169397733620832565 = some 169397733620832565 := by decide +kernel
private theorem endpoint_10_83_p4 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 0 4 169397733620832565 = some 169397733620832565 :=
  join_receipt_window endpoint_10_83_flag endpoint_10_83_sources 0 2 2 169397733620832565 169397733620832565 169397733620832565 endpoint_10_83_w0 endpoint_10_83_w2
private theorem endpoint_10_83_w4 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 4 2 169397733620832565 = some 169397733620832565 := by decide +kernel
private theorem endpoint_10_83_p6 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 0 6 169397733620832565 = some 169397733620832565 :=
  join_receipt_window endpoint_10_83_flag endpoint_10_83_sources 0 4 2 169397733620832565 169397733620832565 169397733620832565 endpoint_10_83_p4 endpoint_10_83_w4
private theorem endpoint_10_83_w6 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 6 2 169397733620832565 = some 169397733620832565 := by decide +kernel
private theorem endpoint_10_83_p8 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 0 8 169397733620832565 = some 169397733620832565 :=
  join_receipt_window endpoint_10_83_flag endpoint_10_83_sources 0 6 2 169397733620832565 169397733620832565 169397733620832565 endpoint_10_83_p6 endpoint_10_83_w6
private theorem endpoint_10_83_w8 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 8 1 169397733620832565 = some 169397733620832565 := by decide +kernel
private theorem endpoint_10_83_p9 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 0 9 169397733620832565 = some 169397733620832565 :=
  join_receipt_window endpoint_10_83_flag endpoint_10_83_sources 0 8 1 169397733620832565 169397733620832565 169397733620832565 endpoint_10_83_p8 endpoint_10_83_w8
def endpoint_10_83 : CertifiedEndpoint :=
  ⟨⟨10, 83, 1522⟩, 169397733620832565, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_83_flag endpoint_10_83_sources 9 169397733620832565 169397733620832565 rfl endpoint_10_83_base endpoint_10_83_p9) (by decide)⟩
private def endpoint_10_84_flag : Flag := ⟨10, 84, 1422⟩
private def endpoint_10_84_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_84_base : receiptBase endpoint_10_84_flag endpoint_10_84_sources = some 160013059926752212 := by decide +kernel
private theorem endpoint_10_84_w0 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 0 2 160013059926752212 = some 160013059926752212 := by decide +kernel
private theorem endpoint_10_84_w2 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 2 2 160013059926752212 = some 160013059926752212 := by decide +kernel
private theorem endpoint_10_84_p4 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 0 4 160013059926752212 = some 160013059926752212 :=
  join_receipt_window endpoint_10_84_flag endpoint_10_84_sources 0 2 2 160013059926752212 160013059926752212 160013059926752212 endpoint_10_84_w0 endpoint_10_84_w2
private theorem endpoint_10_84_w4 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 4 2 160013059926752212 = some 160013059926752212 := by decide +kernel
private theorem endpoint_10_84_p6 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 0 6 160013059926752212 = some 160013059926752212 :=
  join_receipt_window endpoint_10_84_flag endpoint_10_84_sources 0 4 2 160013059926752212 160013059926752212 160013059926752212 endpoint_10_84_p4 endpoint_10_84_w4
private theorem endpoint_10_84_w6 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 6 2 160013059926752212 = some 160013059926752212 := by decide +kernel
private theorem endpoint_10_84_p8 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 0 8 160013059926752212 = some 160013059926752212 :=
  join_receipt_window endpoint_10_84_flag endpoint_10_84_sources 0 6 2 160013059926752212 160013059926752212 160013059926752212 endpoint_10_84_p6 endpoint_10_84_w6
private theorem endpoint_10_84_w8 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 8 1 160013059926752212 = some 160013059926752212 := by decide +kernel
private theorem endpoint_10_84_p9 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 0 9 160013059926752212 = some 160013059926752212 :=
  join_receipt_window endpoint_10_84_flag endpoint_10_84_sources 0 8 1 160013059926752212 160013059926752212 160013059926752212 endpoint_10_84_p8 endpoint_10_84_w8
def endpoint_10_84 : CertifiedEndpoint :=
  ⟨⟨10, 84, 1422⟩, 160013059926752212, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_84_flag endpoint_10_84_sources 9 160013059926752212 160013059926752212 rfl endpoint_10_84_base endpoint_10_84_p9) (by decide)⟩
def endpoint_10_85 : CertifiedEndpoint :=
  ⟨⟨10, 85, 1319⟩, 248802121707980144, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_86 : CertifiedEndpoint :=
  ⟨⟨10, 86, 1214⟩, 231065700150005454, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_87 : CertifiedEndpoint :=
  ⟨⟨10, 87, 1106⟩, 212210188068948491, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_88 : CertifiedEndpoint :=
  ⟨⟨10, 88, 995⟩, 192213474417551945, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_89 : CertifiedEndpoint :=
  ⟨⟨10, 89, 881⟩, 171053448148558506, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_90 : CertifiedEndpoint :=
  ⟨⟨10, 90, 765⟩, 148915604998479895, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_91 : CertifiedEndpoint :=
  ⟨⟨10, 91, 646⟩, 125575140702346951, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_92 : CertifiedEndpoint :=
  ⟨⟨10, 92, 525⟩, 101222464562728575, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_93 : CertifiedEndpoint :=
  ⟨⟨10, 93, 400⟩, 75412881615743625, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_94 : CertifiedEndpoint :=
  ⟨⟨10, 94, 273⟩, 48551778296815803, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_95 : CertifiedEndpoint :=
  ⟨⟨10, 95, 144⟩, 20624413907773569, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_11 : CertifiedEndpoint :=
  ⟨⟨11, 11, 4280⟩, 73644126931689469, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_12 : CertifiedEndpoint :=
  ⟨⟨11, 12, 4261⟩, 77075128010379026, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_13 : CertifiedEndpoint :=
  ⟨⟨11, 13, 4242⟩, 80472507230874141, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_14 : CertifiedEndpoint :=
  ⟨⟨11, 14, 4223⟩, 91537951152363323, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_15 : CertifiedEndpoint :=
  ⟨⟨11, 15, 4204⟩, 102497530066896667, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_16 : CertifiedEndpoint :=
  ⟨⟨11, 16, 4184⟩, 113324090480224504, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_17 : CertifiedEndpoint :=
  ⟨⟨11, 17, 4164⟩, 124039356911880819, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_18 : CertifiedEndpoint :=
  ⟨⟨11, 18, 4144⟩, 134643329361865612, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_19 : CertifiedEndpoint :=
  ⟨⟨11, 19, 4124⟩, 145136007830178883, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_20 : CertifiedEndpoint :=
  ⟨⟨11, 20, 4104⟩, 155517392316820632, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_21 : CertifiedEndpoint :=
  ⟨⟨11, 21, 4083⟩, 165746756890751980, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_22 : CertifiedEndpoint :=
  ⟨⟨11, 22, 4063⟩, 175902838926692843, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_23 : CertifiedEndpoint :=
  ⟨⟨11, 23, 4042⟩, 185901472075207621, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_24 : CertifiedEndpoint :=
  ⟨⟨11, 24, 4020⟩, 195734512874222788, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_25 : CertifiedEndpoint :=
  ⟨⟨11, 25, 3999⟩, 205496985622605312, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_26 : CertifiedEndpoint :=
  ⟨⟨11, 26, 3977⟩, 215088437046772541, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_27 : CertifiedEndpoint :=
  ⟨⟨11, 27, 3955⟩, 224557736539836880, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_28 : CertifiedEndpoint :=
  ⟨⟨11, 28, 3933⟩, 233904884101798329, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_29 : CertifiedEndpoint :=
  ⟨⟨11, 29, 3910⟩, 243067437902755273, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_30 : CertifiedEndpoint :=
  ⟨⟨11, 30, 3888⟩, 252167567115153100, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_11_31_flag : Flag := ⟨11, 31, 3865⟩
private def endpoint_11_31_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_31_base : receiptBase endpoint_11_31_flag endpoint_11_31_sources = some 173758705788137098 := by decide +kernel
private theorem endpoint_11_31_w0 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 2 173758705788137098 = some 173758705788137098 := by decide +kernel
private theorem endpoint_11_31_w2 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 2 2 173758705788137098 = some 173758705788137098 := by decide +kernel
private theorem endpoint_11_31_p4 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 4 173758705788137098 = some 173758705788137098 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 2 2 173758705788137098 173758705788137098 173758705788137098 endpoint_11_31_w0 endpoint_11_31_w2
private theorem endpoint_11_31_w4 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 4 2 173758705788137098 = some 173758705788137098 := by decide +kernel
private theorem endpoint_11_31_p6 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 6 173758705788137098 = some 173758705788137098 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 4 2 173758705788137098 173758705788137098 173758705788137098 endpoint_11_31_p4 endpoint_11_31_w4
private theorem endpoint_11_31_w6 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 6 2 173758705788137098 = some 173758705788137098 := by decide +kernel
private theorem endpoint_11_31_p8 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 8 173758705788137098 = some 173758705788137098 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 6 2 173758705788137098 173758705788137098 173758705788137098 endpoint_11_31_p6 endpoint_11_31_w6
private theorem endpoint_11_31_w8 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 8 2 173758705788137098 = some 173758705788137098 := by decide +kernel
private theorem endpoint_11_31_p10 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 10 173758705788137098 = some 173758705788137098 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 8 2 173758705788137098 173758705788137098 173758705788137098 endpoint_11_31_p8 endpoint_11_31_w8
def endpoint_11_31 : CertifiedEndpoint :=
  ⟨⟨11, 31, 3865⟩, 173758705788137098, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_31_flag endpoint_11_31_sources 10 173758705788137098 173758705788137098 rfl endpoint_11_31_base endpoint_11_31_p10) (by decide)⟩
private def endpoint_11_32_flag : Flag := ⟨11, 32, 3841⟩
private def endpoint_11_32_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_32_base : receiptBase endpoint_11_32_flag endpoint_11_32_sources = some 177210026967479243 := by decide +kernel
private theorem endpoint_11_32_w0 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 2 177210026967479243 = some 177210026967479243 := by decide +kernel
private theorem endpoint_11_32_w2 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 2 2 177210026967479243 = some 177210026967479243 := by decide +kernel
private theorem endpoint_11_32_p4 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 4 177210026967479243 = some 177210026967479243 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 2 2 177210026967479243 177210026967479243 177210026967479243 endpoint_11_32_w0 endpoint_11_32_w2
private theorem endpoint_11_32_w4 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 4 2 177210026967479243 = some 177210026967479243 := by decide +kernel
private theorem endpoint_11_32_p6 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 6 177210026967479243 = some 177210026967479243 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 4 2 177210026967479243 177210026967479243 177210026967479243 endpoint_11_32_p4 endpoint_11_32_w4
private theorem endpoint_11_32_w6 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 6 2 177210026967479243 = some 177210026967479243 := by decide +kernel
private theorem endpoint_11_32_p8 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 8 177210026967479243 = some 177210026967479243 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 6 2 177210026967479243 177210026967479243 177210026967479243 endpoint_11_32_p6 endpoint_11_32_w6
private theorem endpoint_11_32_w8 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 8 2 177210026967479243 = some 177210026967479243 := by decide +kernel
private theorem endpoint_11_32_p10 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 10 177210026967479243 = some 177210026967479243 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 8 2 177210026967479243 177210026967479243 177210026967479243 endpoint_11_32_p8 endpoint_11_32_w8
def endpoint_11_32 : CertifiedEndpoint :=
  ⟨⟨11, 32, 3841⟩, 177210026967479243, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_32_flag endpoint_11_32_sources 10 177210026967479243 177210026967479243 rfl endpoint_11_32_base endpoint_11_32_p10) (by decide)⟩
private def endpoint_11_33_flag : Flag := ⟨11, 33, 3818⟩
private def endpoint_11_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_33_base : receiptBase endpoint_11_33_flag endpoint_11_33_sources = some 180651494497705474 := by decide +kernel
private theorem endpoint_11_33_w0 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 2 180651494497705474 = some 180651494497705474 := by decide +kernel
private theorem endpoint_11_33_w2 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 2 2 180651494497705474 = some 180651494497705474 := by decide +kernel
private theorem endpoint_11_33_p4 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 4 180651494497705474 = some 180651494497705474 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 2 2 180651494497705474 180651494497705474 180651494497705474 endpoint_11_33_w0 endpoint_11_33_w2
private theorem endpoint_11_33_w4 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 4 2 180651494497705474 = some 180651494497705474 := by decide +kernel
private theorem endpoint_11_33_p6 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 6 180651494497705474 = some 180651494497705474 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 4 2 180651494497705474 180651494497705474 180651494497705474 endpoint_11_33_p4 endpoint_11_33_w4
private theorem endpoint_11_33_w6 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 6 2 180651494497705474 = some 180651494497705474 := by decide +kernel
private theorem endpoint_11_33_p8 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 8 180651494497705474 = some 180651494497705474 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 6 2 180651494497705474 180651494497705474 180651494497705474 endpoint_11_33_p6 endpoint_11_33_w6
private theorem endpoint_11_33_w8 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 8 2 180651494497705474 = some 180651494497705474 := by decide +kernel
private theorem endpoint_11_33_p10 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 10 180651494497705474 = some 180651494497705474 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 8 2 180651494497705474 180651494497705474 180651494497705474 endpoint_11_33_p8 endpoint_11_33_w8
def endpoint_11_33 : CertifiedEndpoint :=
  ⟨⟨11, 33, 3818⟩, 180651494497705474, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_33_flag endpoint_11_33_sources 10 180651494497705474 180651494497705474 rfl endpoint_11_33_base endpoint_11_33_p10) (by decide)⟩
private def endpoint_11_34_flag : Flag := ⟨11, 34, 3794⟩
private def endpoint_11_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_34_base : receiptBase endpoint_11_34_flag endpoint_11_34_sources = some 183991019664669532 := by decide +kernel
private theorem endpoint_11_34_w0 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 2 183991019664669532 = some 183991019664669532 := by decide +kernel
private theorem endpoint_11_34_w2 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 2 2 183991019664669532 = some 183991019664669532 := by decide +kernel
private theorem endpoint_11_34_p4 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 4 183991019664669532 = some 183991019664669532 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 2 2 183991019664669532 183991019664669532 183991019664669532 endpoint_11_34_w0 endpoint_11_34_w2
private theorem endpoint_11_34_w4 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 4 2 183991019664669532 = some 183991019664669532 := by decide +kernel
private theorem endpoint_11_34_p6 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 6 183991019664669532 = some 183991019664669532 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 4 2 183991019664669532 183991019664669532 183991019664669532 endpoint_11_34_p4 endpoint_11_34_w4
private theorem endpoint_11_34_w6 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 6 2 183991019664669532 = some 183991019664669532 := by decide +kernel
private theorem endpoint_11_34_p8 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 8 183991019664669532 = some 183991019664669532 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 6 2 183991019664669532 183991019664669532 183991019664669532 endpoint_11_34_p6 endpoint_11_34_w6
private theorem endpoint_11_34_w8 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 8 2 183991019664669532 = some 183991019664669532 := by decide +kernel
private theorem endpoint_11_34_p10 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 10 183991019664669532 = some 183991019664669532 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 8 2 183991019664669532 183991019664669532 183991019664669532 endpoint_11_34_p8 endpoint_11_34_w8
def endpoint_11_34 : CertifiedEndpoint :=
  ⟨⟨11, 34, 3794⟩, 183991019664669532, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_34_flag endpoint_11_34_sources 10 183991019664669532 183991019664669532 rfl endpoint_11_34_base endpoint_11_34_p10) (by decide)⟩
private def endpoint_11_35_flag : Flag := ⟨11, 35, 3769⟩
private def endpoint_11_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_35_base : receiptBase endpoint_11_35_flag endpoint_11_35_sources = some 187225145138067252 := by decide +kernel
private theorem endpoint_11_35_w0 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 2 187225145138067252 = some 187225145138067252 := by decide +kernel
private theorem endpoint_11_35_w2 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 2 2 187225145138067252 = some 187225145138067252 := by decide +kernel
private theorem endpoint_11_35_p4 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 4 187225145138067252 = some 187225145138067252 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 2 2 187225145138067252 187225145138067252 187225145138067252 endpoint_11_35_w0 endpoint_11_35_w2
private theorem endpoint_11_35_w4 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 4 2 187225145138067252 = some 187225145138067252 := by decide +kernel
private theorem endpoint_11_35_p6 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 6 187225145138067252 = some 187225145138067252 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 4 2 187225145138067252 187225145138067252 187225145138067252 endpoint_11_35_p4 endpoint_11_35_w4
private theorem endpoint_11_35_w6 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 6 2 187225145138067252 = some 187225145138067252 := by decide +kernel
private theorem endpoint_11_35_p8 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 8 187225145138067252 = some 187225145138067252 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 6 2 187225145138067252 187225145138067252 187225145138067252 endpoint_11_35_p6 endpoint_11_35_w6
private theorem endpoint_11_35_w8 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 8 2 187225145138067252 = some 187225145138067252 := by decide +kernel
private theorem endpoint_11_35_p10 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 10 187225145138067252 = some 187225145138067252 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 8 2 187225145138067252 187225145138067252 187225145138067252 endpoint_11_35_p8 endpoint_11_35_w8
def endpoint_11_35 : CertifiedEndpoint :=
  ⟨⟨11, 35, 3769⟩, 187225145138067252, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_35_flag endpoint_11_35_sources 10 187225145138067252 187225145138067252 rfl endpoint_11_35_base endpoint_11_35_p10) (by decide)⟩
private def endpoint_11_36_flag : Flag := ⟨11, 36, 3745⟩
private def endpoint_11_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_36_base : receiptBase endpoint_11_36_flag endpoint_11_36_sources = some 190450569405783779 := by decide +kernel
private theorem endpoint_11_36_w0 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 2 190450569405783779 = some 190450569405783779 := by decide +kernel
private theorem endpoint_11_36_w2 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 2 2 190450569405783779 = some 190450569405783779 := by decide +kernel
private theorem endpoint_11_36_p4 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 4 190450569405783779 = some 190450569405783779 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 2 2 190450569405783779 190450569405783779 190450569405783779 endpoint_11_36_w0 endpoint_11_36_w2
private theorem endpoint_11_36_w4 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 4 2 190450569405783779 = some 190450569405783779 := by decide +kernel
private theorem endpoint_11_36_p6 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 6 190450569405783779 = some 190450569405783779 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 4 2 190450569405783779 190450569405783779 190450569405783779 endpoint_11_36_p4 endpoint_11_36_w4
private theorem endpoint_11_36_w6 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 6 2 190450569405783779 = some 190450569405783779 := by decide +kernel
private theorem endpoint_11_36_p8 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 8 190450569405783779 = some 190450569405783779 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 6 2 190450569405783779 190450569405783779 190450569405783779 endpoint_11_36_p6 endpoint_11_36_w6
private theorem endpoint_11_36_w8 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 8 2 190450569405783779 = some 190450569405783779 := by decide +kernel
private theorem endpoint_11_36_p10 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 10 190450569405783779 = some 190450569405783779 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 8 2 190450569405783779 190450569405783779 190450569405783779 endpoint_11_36_p8 endpoint_11_36_w8
def endpoint_11_36 : CertifiedEndpoint :=
  ⟨⟨11, 36, 3745⟩, 190450569405783779, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_36_flag endpoint_11_36_sources 10 190450569405783779 190450569405783779 rfl endpoint_11_36_base endpoint_11_36_p10) (by decide)⟩
private def endpoint_11_37_flag : Flag := ⟨11, 37, 3720⟩
private def endpoint_11_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_37_base : receiptBase endpoint_11_37_flag endpoint_11_37_sources = some 193568289093064523 := by decide +kernel
private theorem endpoint_11_37_w0 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 2 193568289093064523 = some 193568289093064523 := by decide +kernel
private theorem endpoint_11_37_w2 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 2 2 193568289093064523 = some 193568289093064523 := by decide +kernel
private theorem endpoint_11_37_p4 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 4 193568289093064523 = some 193568289093064523 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 2 2 193568289093064523 193568289093064523 193568289093064523 endpoint_11_37_w0 endpoint_11_37_w2
private theorem endpoint_11_37_w4 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 4 2 193568289093064523 = some 193568289093064523 := by decide +kernel
private theorem endpoint_11_37_p6 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 6 193568289093064523 = some 193568289093064523 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 4 2 193568289093064523 193568289093064523 193568289093064523 endpoint_11_37_p4 endpoint_11_37_w4
private theorem endpoint_11_37_w6 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 6 2 193568289093064523 = some 193568289093064523 := by decide +kernel
private theorem endpoint_11_37_p8 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 8 193568289093064523 = some 193568289093064523 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 6 2 193568289093064523 193568289093064523 193568289093064523 endpoint_11_37_p6 endpoint_11_37_w6
private theorem endpoint_11_37_w8 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 8 2 193568289093064523 = some 193568289093064523 := by decide +kernel
private theorem endpoint_11_37_p10 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 10 193568289093064523 = some 193568289093064523 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 8 2 193568289093064523 193568289093064523 193568289093064523 endpoint_11_37_p8 endpoint_11_37_w8
def endpoint_11_37 : CertifiedEndpoint :=
  ⟨⟨11, 37, 3720⟩, 193568289093064523, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_37_flag endpoint_11_37_sources 10 193568289093064523 193568289093064523 rfl endpoint_11_37_base endpoint_11_37_p10) (by decide)⟩
private def endpoint_11_38_flag : Flag := ⟨11, 38, 3694⟩
private def endpoint_11_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_38_base : receiptBase endpoint_11_38_flag endpoint_11_38_sources = some 196574846869605317 := by decide +kernel
private theorem endpoint_11_38_w0 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 2 196574846869605317 = some 196574846869605317 := by decide +kernel
private theorem endpoint_11_38_w2 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 2 2 196574846869605317 = some 196574846869605317 := by decide +kernel
private theorem endpoint_11_38_p4 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 4 196574846869605317 = some 196574846869605317 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 2 2 196574846869605317 196574846869605317 196574846869605317 endpoint_11_38_w0 endpoint_11_38_w2
private theorem endpoint_11_38_w4 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 4 2 196574846869605317 = some 196574846869605317 := by decide +kernel
private theorem endpoint_11_38_p6 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 6 196574846869605317 = some 196574846869605317 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 4 2 196574846869605317 196574846869605317 196574846869605317 endpoint_11_38_p4 endpoint_11_38_w4
private theorem endpoint_11_38_w6 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 6 2 196574846869605317 = some 196574846869605317 := by decide +kernel
private theorem endpoint_11_38_p8 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 8 196574846869605317 = some 196574846869605317 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 6 2 196574846869605317 196574846869605317 196574846869605317 endpoint_11_38_p6 endpoint_11_38_w6
private theorem endpoint_11_38_w8 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 8 2 196574846869605317 = some 196574846869605317 := by decide +kernel
private theorem endpoint_11_38_p10 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 10 196574846869605317 = some 196574846869605317 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 8 2 196574846869605317 196574846869605317 196574846869605317 endpoint_11_38_p8 endpoint_11_38_w8
def endpoint_11_38 : CertifiedEndpoint :=
  ⟨⟨11, 38, 3694⟩, 196574846869605317, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_38_flag endpoint_11_38_sources 10 196574846869605317 196574846869605317 rfl endpoint_11_38_base endpoint_11_38_p10) (by decide)⟩
private def endpoint_11_39_flag : Flag := ⟨11, 39, 3668⟩
private def endpoint_11_39_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_39_base : receiptBase endpoint_11_39_flag endpoint_11_39_sources = some 199520320644500817 := by decide +kernel
private theorem endpoint_11_39_w0 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 2 199520320644500817 = some 199520320644500817 := by decide +kernel
private theorem endpoint_11_39_w2 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 2 2 199520320644500817 = some 199520320644500817 := by decide +kernel
private theorem endpoint_11_39_p4 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 4 199520320644500817 = some 199520320644500817 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 2 2 199520320644500817 199520320644500817 199520320644500817 endpoint_11_39_w0 endpoint_11_39_w2
private theorem endpoint_11_39_w4 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 4 2 199520320644500817 = some 199520320644500817 := by decide +kernel
private theorem endpoint_11_39_p6 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 6 199520320644500817 = some 199520320644500817 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 4 2 199520320644500817 199520320644500817 199520320644500817 endpoint_11_39_p4 endpoint_11_39_w4
private theorem endpoint_11_39_w6 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 6 2 199520320644500817 = some 199520320644500817 := by decide +kernel
private theorem endpoint_11_39_p8 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 8 199520320644500817 = some 199520320644500817 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 6 2 199520320644500817 199520320644500817 199520320644500817 endpoint_11_39_p6 endpoint_11_39_w6
private theorem endpoint_11_39_w8 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 8 2 199520320644500817 = some 199520320644500817 := by decide +kernel
private theorem endpoint_11_39_p10 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 10 199520320644500817 = some 199520320644500817 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 8 2 199520320644500817 199520320644500817 199520320644500817 endpoint_11_39_p8 endpoint_11_39_w8
def endpoint_11_39 : CertifiedEndpoint :=
  ⟨⟨11, 39, 3668⟩, 199520320644500817, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_39_flag endpoint_11_39_sources 10 199520320644500817 199520320644500817 rfl endpoint_11_39_base endpoint_11_39_p10) (by decide)⟩
private def endpoint_11_40_flag : Flag := ⟨11, 40, 3642⟩
private def endpoint_11_40_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_40_base : receiptBase endpoint_11_40_flag endpoint_11_40_sources = some 202404710417751024 := by decide +kernel
private theorem endpoint_11_40_w0 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 2 202404710417751024 = some 202404710417751024 := by decide +kernel
private theorem endpoint_11_40_w2 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 2 2 202404710417751024 = some 202404710417751024 := by decide +kernel
private theorem endpoint_11_40_p4 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 4 202404710417751024 = some 202404710417751024 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 2 2 202404710417751024 202404710417751024 202404710417751024 endpoint_11_40_w0 endpoint_11_40_w2
private theorem endpoint_11_40_w4 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 4 2 202404710417751024 = some 202404710417751024 := by decide +kernel
private theorem endpoint_11_40_p6 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 6 202404710417751024 = some 202404710417751024 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 4 2 202404710417751024 202404710417751024 202404710417751024 endpoint_11_40_p4 endpoint_11_40_w4
private theorem endpoint_11_40_w6 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 6 2 202404710417751024 = some 202404710417751024 := by decide +kernel
private theorem endpoint_11_40_p8 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 8 202404710417751024 = some 202404710417751024 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 6 2 202404710417751024 202404710417751024 202404710417751024 endpoint_11_40_p6 endpoint_11_40_w6
private theorem endpoint_11_40_w8 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 8 2 202404710417751024 = some 202404710417751024 := by decide +kernel
private theorem endpoint_11_40_p10 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 10 202404710417751024 = some 202404710417751024 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 8 2 202404710417751024 202404710417751024 202404710417751024 endpoint_11_40_p8 endpoint_11_40_w8
def endpoint_11_40 : CertifiedEndpoint :=
  ⟨⟨11, 40, 3642⟩, 202404710417751024, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_40_flag endpoint_11_40_sources 10 202404710417751024 202404710417751024 rfl endpoint_11_40_base endpoint_11_40_p10) (by decide)⟩
private def endpoint_11_41_flag : Flag := ⟨11, 41, 3616⟩
private def endpoint_11_41_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_41_base : receiptBase endpoint_11_41_flag endpoint_11_41_sources = some 205228016189355938 := by decide +kernel
private theorem endpoint_11_41_w0 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 2 205228016189355938 = some 205228016189355938 := by decide +kernel
private theorem endpoint_11_41_w2 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 2 2 205228016189355938 = some 205228016189355938 := by decide +kernel
private theorem endpoint_11_41_p4 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 4 205228016189355938 = some 205228016189355938 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 2 2 205228016189355938 205228016189355938 205228016189355938 endpoint_11_41_w0 endpoint_11_41_w2
private theorem endpoint_11_41_w4 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 4 2 205228016189355938 = some 205228016189355938 := by decide +kernel
private theorem endpoint_11_41_p6 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 6 205228016189355938 = some 205228016189355938 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 4 2 205228016189355938 205228016189355938 205228016189355938 endpoint_11_41_p4 endpoint_11_41_w4
private theorem endpoint_11_41_w6 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 6 2 205228016189355938 = some 205228016189355938 := by decide +kernel
private theorem endpoint_11_41_p8 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 8 205228016189355938 = some 205228016189355938 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 6 2 205228016189355938 205228016189355938 205228016189355938 endpoint_11_41_p6 endpoint_11_41_w6
private theorem endpoint_11_41_w8 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 8 2 205228016189355938 = some 205228016189355938 := by decide +kernel
private theorem endpoint_11_41_p10 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 10 205228016189355938 = some 205228016189355938 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 8 2 205228016189355938 205228016189355938 205228016189355938 endpoint_11_41_p8 endpoint_11_41_w8
def endpoint_11_41 : CertifiedEndpoint :=
  ⟨⟨11, 41, 3616⟩, 205228016189355938, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_41_flag endpoint_11_41_sources 10 205228016189355938 205228016189355938 rfl endpoint_11_41_base endpoint_11_41_p10) (by decide)⟩
private def endpoint_11_42_flag : Flag := ⟨11, 42, 3588⟩
private def endpoint_11_42_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_42_base : receiptBase endpoint_11_42_flag endpoint_11_42_sources = some 207876252819909579 := by decide +kernel
private theorem endpoint_11_42_w0 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 2 207876252819909579 = some 207876252819909579 := by decide +kernel
private theorem endpoint_11_42_w2 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 2 2 207876252819909579 = some 207876252819909579 := by decide +kernel
private theorem endpoint_11_42_p4 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 4 207876252819909579 = some 207876252819909579 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 2 2 207876252819909579 207876252819909579 207876252819909579 endpoint_11_42_w0 endpoint_11_42_w2
private theorem endpoint_11_42_w4 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 4 2 207876252819909579 = some 207876252819909579 := by decide +kernel
private theorem endpoint_11_42_p6 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 6 207876252819909579 = some 207876252819909579 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 4 2 207876252819909579 207876252819909579 207876252819909579 endpoint_11_42_p4 endpoint_11_42_w4
private theorem endpoint_11_42_w6 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 6 2 207876252819909579 = some 207876252819909579 := by decide +kernel
private theorem endpoint_11_42_p8 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 8 207876252819909579 = some 207876252819909579 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 6 2 207876252819909579 207876252819909579 207876252819909579 endpoint_11_42_p6 endpoint_11_42_w6
private theorem endpoint_11_42_w8 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 8 2 207876252819909579 = some 207876252819909579 := by decide +kernel
private theorem endpoint_11_42_p10 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 10 207876252819909579 = some 207876252819909579 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 8 2 207876252819909579 207876252819909579 207876252819909579 endpoint_11_42_p8 endpoint_11_42_w8
def endpoint_11_42 : CertifiedEndpoint :=
  ⟨⟨11, 42, 3588⟩, 207876252819909579, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_42_flag endpoint_11_42_sources 10 207876252819909579 207876252819909579 rfl endpoint_11_42_base endpoint_11_42_p10) (by decide)⟩
private def endpoint_11_43_flag : Flag := ⟨11, 43, 3561⟩
private def endpoint_11_43_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_43_base : receiptBase endpoint_11_43_flag endpoint_11_43_sources = some 210516940688216750 := by decide +kernel
private theorem endpoint_11_43_w0 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 2 210516940688216750 = some 210516940688216750 := by decide +kernel
private theorem endpoint_11_43_w2 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 2 2 210516940688216750 = some 210516940688216750 := by decide +kernel
private theorem endpoint_11_43_p4 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 4 210516940688216750 = some 210516940688216750 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 2 2 210516940688216750 210516940688216750 210516940688216750 endpoint_11_43_w0 endpoint_11_43_w2
private theorem endpoint_11_43_w4 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 4 2 210516940688216750 = some 210516940688216750 := by decide +kernel
private theorem endpoint_11_43_p6 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 6 210516940688216750 = some 210516940688216750 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 4 2 210516940688216750 210516940688216750 210516940688216750 endpoint_11_43_p4 endpoint_11_43_w4
private theorem endpoint_11_43_w6 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 6 2 210516940688216750 = some 210516940688216750 := by decide +kernel
private theorem endpoint_11_43_p8 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 8 210516940688216750 = some 210516940688216750 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 6 2 210516940688216750 210516940688216750 210516940688216750 endpoint_11_43_p6 endpoint_11_43_w6
private theorem endpoint_11_43_w8 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 8 2 210516940688216750 = some 210516940688216750 := by decide +kernel
private theorem endpoint_11_43_p10 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 10 210516940688216750 = some 210516940688216750 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 8 2 210516940688216750 210516940688216750 210516940688216750 endpoint_11_43_p8 endpoint_11_43_w8
def endpoint_11_43 : CertifiedEndpoint :=
  ⟨⟨11, 43, 3561⟩, 210516940688216750, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_43_flag endpoint_11_43_sources 10 210516940688216750 210516940688216750 rfl endpoint_11_43_base endpoint_11_43_p10) (by decide)⟩
private def endpoint_11_44_flag : Flag := ⟨11, 44, 3533⟩
private def endpoint_11_44_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_44_base : receiptBase endpoint_11_44_flag endpoint_11_44_sources = some 213034942211436749 := by decide +kernel
private theorem endpoint_11_44_w0 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 2 213034942211436749 = some 215055749050472694 := by decide +kernel
private theorem endpoint_11_44_w2 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 2 2 215055749050472694 = some 215055749050472694 := by decide +kernel
private theorem endpoint_11_44_p4 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 4 213034942211436749 = some 215055749050472694 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 2 2 213034942211436749 215055749050472694 215055749050472694 endpoint_11_44_w0 endpoint_11_44_w2
private theorem endpoint_11_44_w4 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 4 2 215055749050472694 = some 215055749050472694 := by decide +kernel
private theorem endpoint_11_44_p6 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 6 213034942211436749 = some 215055749050472694 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 4 2 213034942211436749 215055749050472694 215055749050472694 endpoint_11_44_p4 endpoint_11_44_w4
private theorem endpoint_11_44_w6 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 6 2 215055749050472694 = some 215055749050472694 := by decide +kernel
private theorem endpoint_11_44_p8 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 8 213034942211436749 = some 215055749050472694 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 6 2 213034942211436749 215055749050472694 215055749050472694 endpoint_11_44_p6 endpoint_11_44_w6
private theorem endpoint_11_44_w8 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 8 2 215055749050472694 = some 215055749050472694 := by decide +kernel
private theorem endpoint_11_44_p10 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 10 213034942211436749 = some 215055749050472694 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 8 2 213034942211436749 215055749050472694 215055749050472694 endpoint_11_44_p8 endpoint_11_44_w8
def endpoint_11_44 : CertifiedEndpoint :=
  ⟨⟨11, 44, 3533⟩, 215055749050472694, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_44_flag endpoint_11_44_sources 10 213034942211436749 215055749050472694 rfl endpoint_11_44_base endpoint_11_44_p10) (by decide)⟩
private def endpoint_11_45_flag : Flag := ⟨11, 45, 3504⟩
private def endpoint_11_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_45_base : receiptBase endpoint_11_45_flag endpoint_11_45_sources = some 215964031217116267 := by decide +kernel
private theorem endpoint_11_45_w0 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 2 215964031217116267 = some 215964031217116267 := by decide +kernel
private theorem endpoint_11_45_w2 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 2 2 215964031217116267 = some 215964031217116267 := by decide +kernel
private theorem endpoint_11_45_p4 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 4 215964031217116267 = some 215964031217116267 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 2 2 215964031217116267 215964031217116267 215964031217116267 endpoint_11_45_w0 endpoint_11_45_w2
private theorem endpoint_11_45_w4 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 4 2 215964031217116267 = some 215964031217116267 := by decide +kernel
private theorem endpoint_11_45_p6 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 6 215964031217116267 = some 215964031217116267 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 4 2 215964031217116267 215964031217116267 215964031217116267 endpoint_11_45_p4 endpoint_11_45_w4
private theorem endpoint_11_45_w6 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 6 2 215964031217116267 = some 215964031217116267 := by decide +kernel
private theorem endpoint_11_45_p8 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 8 215964031217116267 = some 215964031217116267 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 6 2 215964031217116267 215964031217116267 215964031217116267 endpoint_11_45_p6 endpoint_11_45_w6
private theorem endpoint_11_45_w8 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 8 2 215964031217116267 = some 215964031217116267 := by decide +kernel
private theorem endpoint_11_45_p10 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 10 215964031217116267 = some 215964031217116267 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 8 2 215964031217116267 215964031217116267 215964031217116267 endpoint_11_45_p8 endpoint_11_45_w8
def endpoint_11_45 : CertifiedEndpoint :=
  ⟨⟨11, 45, 3504⟩, 215964031217116267, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_45_flag endpoint_11_45_sources 10 215964031217116267 215964031217116267 rfl endpoint_11_45_base endpoint_11_45_p10) (by decide)⟩
private def endpoint_11_46_flag : Flag := ⟨11, 46, 3475⟩
private def endpoint_11_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_46_base : receiptBase endpoint_11_46_flag endpoint_11_46_sources = some 218257004520897410 := by decide +kernel
private theorem endpoint_11_46_w0 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 2 218257004520897410 = some 218257004520897410 := by decide +kernel
private theorem endpoint_11_46_w2 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 2 2 218257004520897410 = some 218257004520897410 := by decide +kernel
private theorem endpoint_11_46_p4 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 4 218257004520897410 = some 218257004520897410 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 2 2 218257004520897410 218257004520897410 218257004520897410 endpoint_11_46_w0 endpoint_11_46_w2
private theorem endpoint_11_46_w4 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 4 2 218257004520897410 = some 218257004520897410 := by decide +kernel
private theorem endpoint_11_46_p6 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 6 218257004520897410 = some 218257004520897410 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 4 2 218257004520897410 218257004520897410 218257004520897410 endpoint_11_46_p4 endpoint_11_46_w4
private theorem endpoint_11_46_w6 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 6 2 218257004520897410 = some 218257004520897410 := by decide +kernel
private theorem endpoint_11_46_p8 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 8 218257004520897410 = some 218257004520897410 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 6 2 218257004520897410 218257004520897410 218257004520897410 endpoint_11_46_p6 endpoint_11_46_w6
private theorem endpoint_11_46_w8 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 8 2 218257004520897410 = some 218257004520897410 := by decide +kernel
private theorem endpoint_11_46_p10 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 10 218257004520897410 = some 218257004520897410 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 8 2 218257004520897410 218257004520897410 218257004520897410 endpoint_11_46_p8 endpoint_11_46_w8
def endpoint_11_46 : CertifiedEndpoint :=
  ⟨⟨11, 46, 3475⟩, 218257004520897410, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_46_flag endpoint_11_46_sources 10 218257004520897410 218257004520897410 rfl endpoint_11_46_base endpoint_11_46_p10) (by decide)⟩
private def endpoint_11_47_flag : Flag := ⟨11, 47, 3445⟩
private def endpoint_11_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_47_base : receiptBase endpoint_11_47_flag endpoint_11_47_sources = some 220419246934090543 := by decide +kernel
private theorem endpoint_11_47_w0 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 2 220419246934090543 = some 220419246934090543 := by decide +kernel
private theorem endpoint_11_47_w2 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 2 2 220419246934090543 = some 220419246934090543 := by decide +kernel
private theorem endpoint_11_47_p4 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 4 220419246934090543 = some 220419246934090543 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 2 2 220419246934090543 220419246934090543 220419246934090543 endpoint_11_47_w0 endpoint_11_47_w2
private theorem endpoint_11_47_w4 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 4 2 220419246934090543 = some 220419246934090543 := by decide +kernel
private theorem endpoint_11_47_p6 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 6 220419246934090543 = some 220419246934090543 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 4 2 220419246934090543 220419246934090543 220419246934090543 endpoint_11_47_p4 endpoint_11_47_w4
private theorem endpoint_11_47_w6 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 6 2 220419246934090543 = some 220419246934090543 := by decide +kernel
private theorem endpoint_11_47_p8 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 8 220419246934090543 = some 220419246934090543 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 6 2 220419246934090543 220419246934090543 220419246934090543 endpoint_11_47_p6 endpoint_11_47_w6
private theorem endpoint_11_47_w8 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 8 2 220419246934090543 = some 220419246934090543 := by decide +kernel
private theorem endpoint_11_47_p10 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 10 220419246934090543 = some 220419246934090543 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 8 2 220419246934090543 220419246934090543 220419246934090543 endpoint_11_47_p8 endpoint_11_47_w8
def endpoint_11_47 : CertifiedEndpoint :=
  ⟨⟨11, 47, 3445⟩, 220419246934090543, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_47_flag endpoint_11_47_sources 10 220419246934090543 220419246934090543 rfl endpoint_11_47_base endpoint_11_47_p10) (by decide)⟩
private def endpoint_11_48_flag : Flag := ⟨11, 48, 3415⟩
private def endpoint_11_48_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_48_base : receiptBase endpoint_11_48_flag endpoint_11_48_sources = some 222511464727342556 := by decide +kernel
private theorem endpoint_11_48_w0 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 2 222511464727342556 = some 223329076143578694 := by decide +kernel
private theorem endpoint_11_48_w2 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 2 2 223329076143578694 = some 223329076143578694 := by decide +kernel
private theorem endpoint_11_48_p4 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 4 222511464727342556 = some 223329076143578694 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 2 2 222511464727342556 223329076143578694 223329076143578694 endpoint_11_48_w0 endpoint_11_48_w2
private theorem endpoint_11_48_w4 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 4 2 223329076143578694 = some 223329076143578694 := by decide +kernel
private theorem endpoint_11_48_p6 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 6 222511464727342556 = some 223329076143578694 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 4 2 222511464727342556 223329076143578694 223329076143578694 endpoint_11_48_p4 endpoint_11_48_w4
private theorem endpoint_11_48_w6 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 6 2 223329076143578694 = some 223329076143578694 := by decide +kernel
private theorem endpoint_11_48_p8 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 8 222511464727342556 = some 223329076143578694 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 6 2 222511464727342556 223329076143578694 223329076143578694 endpoint_11_48_p6 endpoint_11_48_w6
private theorem endpoint_11_48_w8 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 8 2 223329076143578694 = some 223329076143578694 := by decide +kernel
private theorem endpoint_11_48_p10 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 10 222511464727342556 = some 223329076143578694 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 8 2 222511464727342556 223329076143578694 223329076143578694 endpoint_11_48_p8 endpoint_11_48_w8
def endpoint_11_48 : CertifiedEndpoint :=
  ⟨⟨11, 48, 3415⟩, 223329076143578694, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_48_flag endpoint_11_48_sources 10 222511464727342556 223329076143578694 rfl endpoint_11_48_base endpoint_11_48_p10) (by decide)⟩
private def endpoint_11_49_flag : Flag := ⟨11, 49, 3384⟩
private def endpoint_11_49_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_49_base : receiptBase endpoint_11_49_flag endpoint_11_49_sources = some 224468359851649764 := by decide +kernel
private theorem endpoint_11_49_w0 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 2 224468359851649764 = some 227605020832272258 := by decide +kernel
private theorem endpoint_11_49_w2 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 2 2 227605020832272258 = some 227605020832272258 := by decide +kernel
private theorem endpoint_11_49_p4 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 4 224468359851649764 = some 227605020832272258 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 2 2 224468359851649764 227605020832272258 227605020832272258 endpoint_11_49_w0 endpoint_11_49_w2
private theorem endpoint_11_49_w4 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 4 2 227605020832272258 = some 227605020832272258 := by decide +kernel
private theorem endpoint_11_49_p6 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 6 224468359851649764 = some 227605020832272258 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 4 2 224468359851649764 227605020832272258 227605020832272258 endpoint_11_49_p4 endpoint_11_49_w4
private theorem endpoint_11_49_w6 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 6 2 227605020832272258 = some 227605020832272258 := by decide +kernel
private theorem endpoint_11_49_p8 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 8 224468359851649764 = some 227605020832272258 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 6 2 224468359851649764 227605020832272258 227605020832272258 endpoint_11_49_p6 endpoint_11_49_w6
private theorem endpoint_11_49_w8 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 8 2 227605020832272258 = some 227605020832272258 := by decide +kernel
private theorem endpoint_11_49_p10 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 10 224468359851649764 = some 227605020832272258 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 8 2 224468359851649764 227605020832272258 227605020832272258 endpoint_11_49_p8 endpoint_11_49_w8
def endpoint_11_49 : CertifiedEndpoint :=
  ⟨⟨11, 49, 3384⟩, 227605020832272258, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_49_flag endpoint_11_49_sources 10 224468359851649764 227605020832272258 rfl endpoint_11_49_base endpoint_11_49_p10) (by decide)⟩
private def endpoint_11_50_flag : Flag := ⟨11, 50, 3352⟩
private def endpoint_11_50_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_50_base : receiptBase endpoint_11_50_flag endpoint_11_50_sources = some 226286488473244570 := by decide +kernel
private theorem endpoint_11_50_w0 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 2 226286488473244570 = some 231794402529184836 := by decide +kernel
private theorem endpoint_11_50_w2 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 2 2 231794402529184836 = some 231794402529184836 := by decide +kernel
private theorem endpoint_11_50_p4 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 4 226286488473244570 = some 231794402529184836 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 2 2 226286488473244570 231794402529184836 231794402529184836 endpoint_11_50_w0 endpoint_11_50_w2
private theorem endpoint_11_50_w4 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 4 2 231794402529184836 = some 231794402529184836 := by decide +kernel
private theorem endpoint_11_50_p6 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 6 226286488473244570 = some 231794402529184836 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 4 2 226286488473244570 231794402529184836 231794402529184836 endpoint_11_50_p4 endpoint_11_50_w4
private theorem endpoint_11_50_w6 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 6 2 231794402529184836 = some 231794402529184836 := by decide +kernel
private theorem endpoint_11_50_p8 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 8 226286488473244570 = some 231794402529184836 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 6 2 226286488473244570 231794402529184836 231794402529184836 endpoint_11_50_p6 endpoint_11_50_w6
private theorem endpoint_11_50_w8 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 8 2 231794402529184836 = some 231794402529184836 := by decide +kernel
private theorem endpoint_11_50_p10 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 10 226286488473244570 = some 231794402529184836 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 8 2 226286488473244570 231794402529184836 231794402529184836 endpoint_11_50_p8 endpoint_11_50_w8
def endpoint_11_50 : CertifiedEndpoint :=
  ⟨⟨11, 50, 3352⟩, 231794402529184836, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_50_flag endpoint_11_50_sources 10 226286488473244570 231794402529184836 rfl endpoint_11_50_base endpoint_11_50_p10) (by decide)⟩
private def endpoint_11_51_flag : Flag := ⟨11, 51, 3320⟩
private def endpoint_11_51_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_11_51_base : receiptBase endpoint_11_51_flag endpoint_11_51_sources = some 228618430730242201 := by decide +kernel
private theorem endpoint_11_51_w0 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 2 228618430730242201 = some 228618430730242201 := by decide +kernel
private theorem endpoint_11_51_w2 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 2 2 228618430730242201 = some 228618430730242201 := by decide +kernel
private theorem endpoint_11_51_p4 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 4 228618430730242201 = some 228618430730242201 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 2 2 228618430730242201 228618430730242201 228618430730242201 endpoint_11_51_w0 endpoint_11_51_w2
private theorem endpoint_11_51_w4 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 4 2 228618430730242201 = some 228618430730242201 := by decide +kernel
private theorem endpoint_11_51_p6 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 6 228618430730242201 = some 228618430730242201 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 4 2 228618430730242201 228618430730242201 228618430730242201 endpoint_11_51_p4 endpoint_11_51_w4
private theorem endpoint_11_51_w6 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 6 2 228618430730242201 = some 228618430730242201 := by decide +kernel
private theorem endpoint_11_51_p8 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 8 228618430730242201 = some 228618430730242201 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 6 2 228618430730242201 228618430730242201 228618430730242201 endpoint_11_51_p6 endpoint_11_51_w6
private theorem endpoint_11_51_w8 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 8 2 228618430730242201 = some 228618430730242201 := by decide +kernel
private theorem endpoint_11_51_p10 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 10 228618430730242201 = some 228618430730242201 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 8 2 228618430730242201 228618430730242201 228618430730242201 endpoint_11_51_p8 endpoint_11_51_w8
def endpoint_11_51 : CertifiedEndpoint :=
  ⟨⟨11, 51, 3320⟩, 228618430730242201, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_11_51_flag endpoint_11_51_sources 10 228618430730242201 228618430730242201 rfl endpoint_11_51_base endpoint_11_51_p10) (by decide)⟩
private def endpoint_11_52_flag : Flag := ⟨11, 52, 3287⟩
private def endpoint_11_52_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_11_52_base : receiptBase endpoint_11_52_flag endpoint_11_52_sources = some 230227022041450875 := by decide +kernel
private theorem endpoint_11_52_w0 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 2 230227022041450875 = some 231925100732830010 := by decide +kernel
private theorem endpoint_11_52_w2 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 2 2 231925100732830010 = some 231925100732830010 := by decide +kernel
private theorem endpoint_11_52_p4 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 4 230227022041450875 = some 231925100732830010 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 2 2 230227022041450875 231925100732830010 231925100732830010 endpoint_11_52_w0 endpoint_11_52_w2
private theorem endpoint_11_52_w4 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 4 2 231925100732830010 = some 231925100732830010 := by decide +kernel
private theorem endpoint_11_52_p6 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 6 230227022041450875 = some 231925100732830010 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 4 2 230227022041450875 231925100732830010 231925100732830010 endpoint_11_52_p4 endpoint_11_52_w4
private theorem endpoint_11_52_w6 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 6 2 231925100732830010 = some 231925100732830010 := by decide +kernel
private theorem endpoint_11_52_p8 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 8 230227022041450875 = some 231925100732830010 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 6 2 230227022041450875 231925100732830010 231925100732830010 endpoint_11_52_p6 endpoint_11_52_w6
private theorem endpoint_11_52_w8 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 8 2 231925100732830010 = some 231925100732830010 := by decide +kernel
private theorem endpoint_11_52_p10 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 10 230227022041450875 = some 231925100732830010 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 8 2 230227022041450875 231925100732830010 231925100732830010 endpoint_11_52_p8 endpoint_11_52_w8
def endpoint_11_52 : CertifiedEndpoint :=
  ⟨⟨11, 52, 3287⟩, 231925100732830010, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_11_52_flag endpoint_11_52_sources 10 230227022041450875 231925100732830010 rfl endpoint_11_52_base endpoint_11_52_p10) (by decide)⟩
private def endpoint_11_53_flag : Flag := ⟨11, 53, 3252⟩
private def endpoint_11_53_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_11_53_base : receiptBase endpoint_11_53_flag endpoint_11_53_sources = some 231618237355816229 := by decide +kernel
private theorem endpoint_11_53_w0 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 2 231618237355816229 = some 235666274040267840 := by decide +kernel
private theorem endpoint_11_53_w2 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 2 2 235666274040267840 = some 235666274040267840 := by decide +kernel
private theorem endpoint_11_53_p4 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 4 231618237355816229 = some 235666274040267840 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 2 2 231618237355816229 235666274040267840 235666274040267840 endpoint_11_53_w0 endpoint_11_53_w2
private theorem endpoint_11_53_w4 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 4 2 235666274040267840 = some 235666274040267840 := by decide +kernel
private theorem endpoint_11_53_p6 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 6 231618237355816229 = some 235666274040267840 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 4 2 231618237355816229 235666274040267840 235666274040267840 endpoint_11_53_p4 endpoint_11_53_w4
private theorem endpoint_11_53_w6 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 6 2 235666274040267840 = some 235666274040267840 := by decide +kernel
private theorem endpoint_11_53_p8 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 8 231618237355816229 = some 235666274040267840 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 6 2 231618237355816229 235666274040267840 235666274040267840 endpoint_11_53_p6 endpoint_11_53_w6
private theorem endpoint_11_53_w8 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 8 2 235666274040267840 = some 235666274040267840 := by decide +kernel
private theorem endpoint_11_53_p10 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 10 231618237355816229 = some 235666274040267840 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 8 2 231618237355816229 235666274040267840 235666274040267840 endpoint_11_53_p8 endpoint_11_53_w8
def endpoint_11_53 : CertifiedEndpoint :=
  ⟨⟨11, 53, 3252⟩, 235666274040267840, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_11_53_flag endpoint_11_53_sources 10 231618237355816229 235666274040267840 rfl endpoint_11_53_base endpoint_11_53_p10) (by decide)⟩
private def endpoint_11_54_flag : Flag := ⟨11, 54, 3217⟩
private def endpoint_11_54_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_54_base : receiptBase endpoint_11_54_flag endpoint_11_54_sources = some 235444486318983899 := by decide +kernel
private theorem endpoint_11_54_w0 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 2 235444486318983899 = some 235444486318983899 := by decide +kernel
private theorem endpoint_11_54_w2 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 2 2 235444486318983899 = some 235444486318983899 := by decide +kernel
private theorem endpoint_11_54_p4 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 4 235444486318983899 = some 235444486318983899 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 2 2 235444486318983899 235444486318983899 235444486318983899 endpoint_11_54_w0 endpoint_11_54_w2
private theorem endpoint_11_54_w4 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 4 2 235444486318983899 = some 235444486318983899 := by decide +kernel
private theorem endpoint_11_54_p6 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 6 235444486318983899 = some 235444486318983899 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 4 2 235444486318983899 235444486318983899 235444486318983899 endpoint_11_54_p4 endpoint_11_54_w4
private theorem endpoint_11_54_w6 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 6 2 235444486318983899 = some 235444486318983899 := by decide +kernel
private theorem endpoint_11_54_p8 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 8 235444486318983899 = some 235444486318983899 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 6 2 235444486318983899 235444486318983899 235444486318983899 endpoint_11_54_p6 endpoint_11_54_w6
private theorem endpoint_11_54_w8 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 8 2 235444486318983899 = some 235444486318983899 := by decide +kernel
private theorem endpoint_11_54_p10 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 10 235444486318983899 = some 235444486318983899 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 8 2 235444486318983899 235444486318983899 235444486318983899 endpoint_11_54_p8 endpoint_11_54_w8
def endpoint_11_54 : CertifiedEndpoint :=
  ⟨⟨11, 54, 3217⟩, 235444486318983899, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_54_flag endpoint_11_54_sources 10 235444486318983899 235444486318983899 rfl endpoint_11_54_base endpoint_11_54_p10) (by decide)⟩
private def endpoint_11_55_flag : Flag := ⟨11, 55, 3181⟩
private def endpoint_11_55_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_55_base : receiptBase endpoint_11_55_flag endpoint_11_55_sources = some 236563064004147257 := by decide +kernel
private theorem endpoint_11_55_w0 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 2 236563064004147257 = some 236563064004147257 := by decide +kernel
private theorem endpoint_11_55_w2 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 2 2 236563064004147257 = some 236563064004147257 := by decide +kernel
private theorem endpoint_11_55_p4 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 4 236563064004147257 = some 236563064004147257 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 2 2 236563064004147257 236563064004147257 236563064004147257 endpoint_11_55_w0 endpoint_11_55_w2
private theorem endpoint_11_55_w4 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 4 2 236563064004147257 = some 236563064004147257 := by decide +kernel
private theorem endpoint_11_55_p6 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 6 236563064004147257 = some 236563064004147257 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 4 2 236563064004147257 236563064004147257 236563064004147257 endpoint_11_55_p4 endpoint_11_55_w4
private theorem endpoint_11_55_w6 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 6 2 236563064004147257 = some 236563064004147257 := by decide +kernel
private theorem endpoint_11_55_p8 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 8 236563064004147257 = some 236563064004147257 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 6 2 236563064004147257 236563064004147257 236563064004147257 endpoint_11_55_p6 endpoint_11_55_w6
private theorem endpoint_11_55_w8 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 8 2 236563064004147257 = some 236563064004147257 := by decide +kernel
private theorem endpoint_11_55_p10 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 10 236563064004147257 = some 236563064004147257 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 8 2 236563064004147257 236563064004147257 236563064004147257 endpoint_11_55_p8 endpoint_11_55_w8
def endpoint_11_55 : CertifiedEndpoint :=
  ⟨⟨11, 55, 3181⟩, 236563064004147257, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_55_flag endpoint_11_55_sources 10 236563064004147257 236563064004147257 rfl endpoint_11_55_base endpoint_11_55_p10) (by decide)⟩
private def endpoint_11_56_flag : Flag := ⟨11, 56, 3144⟩
private def endpoint_11_56_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_56_base : receiptBase endpoint_11_56_flag endpoint_11_56_sources = some 237522632973236792 := by decide +kernel
private theorem endpoint_11_56_w0 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 2 237522632973236792 = some 237522632973236792 := by decide +kernel
private theorem endpoint_11_56_w2 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 2 2 237522632973236792 = some 237522632973236792 := by decide +kernel
private theorem endpoint_11_56_p4 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 4 237522632973236792 = some 237522632973236792 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 2 2 237522632973236792 237522632973236792 237522632973236792 endpoint_11_56_w0 endpoint_11_56_w2
private theorem endpoint_11_56_w4 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 4 2 237522632973236792 = some 237522632973236792 := by decide +kernel
private theorem endpoint_11_56_p6 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 6 237522632973236792 = some 237522632973236792 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 4 2 237522632973236792 237522632973236792 237522632973236792 endpoint_11_56_p4 endpoint_11_56_w4
private theorem endpoint_11_56_w6 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 6 2 237522632973236792 = some 237522632973236792 := by decide +kernel
private theorem endpoint_11_56_p8 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 8 237522632973236792 = some 237522632973236792 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 6 2 237522632973236792 237522632973236792 237522632973236792 endpoint_11_56_p6 endpoint_11_56_w6
private theorem endpoint_11_56_w8 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 8 2 237522632973236792 = some 237522632973236792 := by decide +kernel
private theorem endpoint_11_56_p10 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 10 237522632973236792 = some 237522632973236792 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 8 2 237522632973236792 237522632973236792 237522632973236792 endpoint_11_56_p8 endpoint_11_56_w8
def endpoint_11_56 : CertifiedEndpoint :=
  ⟨⟨11, 56, 3144⟩, 237522632973236792, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_56_flag endpoint_11_56_sources 10 237522632973236792 237522632973236792 rfl endpoint_11_56_base endpoint_11_56_p10) (by decide)⟩
private def endpoint_11_57_flag : Flag := ⟨11, 57, 3106⟩
private def endpoint_11_57_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_57_base : receiptBase endpoint_11_57_flag endpoint_11_57_sources = some 238319722406247206 := by decide +kernel
private theorem endpoint_11_57_w0 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 2 238319722406247206 = some 238770262616024343 := by decide +kernel
private theorem endpoint_11_57_w2 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 2 2 238770262616024343 = some 238770262616024343 := by decide +kernel
private theorem endpoint_11_57_p4 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 4 238319722406247206 = some 238770262616024343 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 2 2 238319722406247206 238770262616024343 238770262616024343 endpoint_11_57_w0 endpoint_11_57_w2
private theorem endpoint_11_57_w4 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 4 2 238770262616024343 = some 238770262616024343 := by decide +kernel
private theorem endpoint_11_57_p6 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 6 238319722406247206 = some 238770262616024343 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 4 2 238319722406247206 238770262616024343 238770262616024343 endpoint_11_57_p4 endpoint_11_57_w4
private theorem endpoint_11_57_w6 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 6 2 238770262616024343 = some 238770262616024343 := by decide +kernel
private theorem endpoint_11_57_p8 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 8 238319722406247206 = some 238770262616024343 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 6 2 238319722406247206 238770262616024343 238770262616024343 endpoint_11_57_p6 endpoint_11_57_w6
private theorem endpoint_11_57_w8 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 8 2 238770262616024343 = some 238770262616024343 := by decide +kernel
private theorem endpoint_11_57_p10 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 10 238319722406247206 = some 238770262616024343 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 8 2 238319722406247206 238770262616024343 238770262616024343 endpoint_11_57_p8 endpoint_11_57_w8
def endpoint_11_57 : CertifiedEndpoint :=
  ⟨⟨11, 57, 3106⟩, 238770262616024343, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_57_flag endpoint_11_57_sources 10 238319722406247206 238770262616024343 rfl endpoint_11_57_base endpoint_11_57_p10) (by decide)⟩
private def endpoint_11_58_flag : Flag := ⟨11, 58, 3066⟩
private def endpoint_11_58_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_58_base : receiptBase endpoint_11_58_flag endpoint_11_58_sources = some 238873995507224756 := by decide +kernel
private theorem endpoint_11_58_w0 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 2 238873995507224756 = some 241792732181261328 := by decide +kernel
private theorem endpoint_11_58_w2 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 2 2 241792732181261328 = some 241792732181261328 := by decide +kernel
private theorem endpoint_11_58_p4 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 4 238873995507224756 = some 241792732181261328 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 2 2 238873995507224756 241792732181261328 241792732181261328 endpoint_11_58_w0 endpoint_11_58_w2
private theorem endpoint_11_58_w4 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 4 2 241792732181261328 = some 241792732181261328 := by decide +kernel
private theorem endpoint_11_58_p6 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 6 238873995507224756 = some 241792732181261328 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 4 2 238873995507224756 241792732181261328 241792732181261328 endpoint_11_58_p4 endpoint_11_58_w4
private theorem endpoint_11_58_w6 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 6 2 241792732181261328 = some 241792732181261328 := by decide +kernel
private theorem endpoint_11_58_p8 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 8 238873995507224756 = some 241792732181261328 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 6 2 238873995507224756 241792732181261328 241792732181261328 endpoint_11_58_p6 endpoint_11_58_w6
private theorem endpoint_11_58_w8 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 8 2 241792732181261328 = some 241792732181261328 := by decide +kernel
private theorem endpoint_11_58_p10 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 10 238873995507224756 = some 241792732181261328 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 8 2 238873995507224756 241792732181261328 241792732181261328 endpoint_11_58_p8 endpoint_11_58_w8
def endpoint_11_58 : CertifiedEndpoint :=
  ⟨⟨11, 58, 3066⟩, 241792732181261328, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_58_flag endpoint_11_58_sources 10 238873995507224756 241792732181261328 rfl endpoint_11_58_base endpoint_11_58_p10) (by decide)⟩
private def endpoint_11_59_flag : Flag := ⟨11, 59, 3025⟩
private def endpoint_11_59_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_59_base : receiptBase endpoint_11_59_flag endpoint_11_59_sources = some 239256533552109057 := by decide +kernel
private theorem endpoint_11_59_w0 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 2 239256533552109057 = some 244707068878647702 := by decide +kernel
private theorem endpoint_11_59_w2 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 2 2 244707068878647702 = some 244707068878647702 := by decide +kernel
private theorem endpoint_11_59_p4 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 4 239256533552109057 = some 244707068878647702 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 2 2 239256533552109057 244707068878647702 244707068878647702 endpoint_11_59_w0 endpoint_11_59_w2
private theorem endpoint_11_59_w4 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 4 2 244707068878647702 = some 244707068878647702 := by decide +kernel
private theorem endpoint_11_59_p6 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 6 239256533552109057 = some 244707068878647702 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 4 2 239256533552109057 244707068878647702 244707068878647702 endpoint_11_59_p4 endpoint_11_59_w4
private theorem endpoint_11_59_w6 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 6 2 244707068878647702 = some 244707068878647702 := by decide +kernel
private theorem endpoint_11_59_p8 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 8 239256533552109057 = some 244707068878647702 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 6 2 239256533552109057 244707068878647702 244707068878647702 endpoint_11_59_p6 endpoint_11_59_w6
private theorem endpoint_11_59_w8 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 8 2 244707068878647702 = some 244707068878647702 := by decide +kernel
private theorem endpoint_11_59_p10 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 10 239256533552109057 = some 244707068878647702 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 8 2 239256533552109057 244707068878647702 244707068878647702 endpoint_11_59_p8 endpoint_11_59_w8
def endpoint_11_59 : CertifiedEndpoint :=
  ⟨⟨11, 59, 3025⟩, 244707068878647702, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_59_flag endpoint_11_59_sources 10 239256533552109057 244707068878647702 rfl endpoint_11_59_base endpoint_11_59_p10) (by decide)⟩
private def endpoint_11_60_flag : Flag := ⟨11, 60, 2983⟩
private def endpoint_11_60_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_11_60_base : receiptBase endpoint_11_60_flag endpoint_11_60_sources = some 240558100264745892 := by decide +kernel
private theorem endpoint_11_60_w0 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 2 240558100264745892 = some 240558100264745892 := by decide +kernel
private theorem endpoint_11_60_w2 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 2 2 240558100264745892 = some 240558100264745892 := by decide +kernel
private theorem endpoint_11_60_p4 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 4 240558100264745892 = some 240558100264745892 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 2 2 240558100264745892 240558100264745892 240558100264745892 endpoint_11_60_w0 endpoint_11_60_w2
private theorem endpoint_11_60_w4 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 4 2 240558100264745892 = some 240558100264745892 := by decide +kernel
private theorem endpoint_11_60_p6 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 6 240558100264745892 = some 240558100264745892 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 4 2 240558100264745892 240558100264745892 240558100264745892 endpoint_11_60_p4 endpoint_11_60_w4
private theorem endpoint_11_60_w6 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 6 2 240558100264745892 = some 240558100264745892 := by decide +kernel
private theorem endpoint_11_60_p8 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 8 240558100264745892 = some 240558100264745892 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 6 2 240558100264745892 240558100264745892 240558100264745892 endpoint_11_60_p6 endpoint_11_60_w6
private theorem endpoint_11_60_w8 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 8 2 240558100264745892 = some 240558100264745892 := by decide +kernel
private theorem endpoint_11_60_p10 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 10 240558100264745892 = some 240558100264745892 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 8 2 240558100264745892 240558100264745892 240558100264745892 endpoint_11_60_p8 endpoint_11_60_w8
def endpoint_11_60 : CertifiedEndpoint :=
  ⟨⟨11, 60, 2983⟩, 240558100264745892, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_11_60_flag endpoint_11_60_sources 10 240558100264745892 240558100264745892 rfl endpoint_11_60_base endpoint_11_60_p10) (by decide)⟩
private def endpoint_11_61_flag : Flag := ⟨11, 61, 2939⟩
private def endpoint_11_61_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_11_61_base : receiptBase endpoint_11_61_flag endpoint_11_61_sources = some 240509006000446230 := by decide +kernel
private theorem endpoint_11_61_w0 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 2 240509006000446230 = some 242706627476799224 := by decide +kernel
private theorem endpoint_11_61_w2 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 2 2 242706627476799224 = some 242706627476799224 := by decide +kernel
private theorem endpoint_11_61_p4 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 4 240509006000446230 = some 242706627476799224 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 2 2 240509006000446230 242706627476799224 242706627476799224 endpoint_11_61_w0 endpoint_11_61_w2
private theorem endpoint_11_61_w4 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 4 2 242706627476799224 = some 242706627476799224 := by decide +kernel
private theorem endpoint_11_61_p6 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 6 240509006000446230 = some 242706627476799224 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 4 2 240509006000446230 242706627476799224 242706627476799224 endpoint_11_61_p4 endpoint_11_61_w4
private theorem endpoint_11_61_w6 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 6 2 242706627476799224 = some 242706627476799224 := by decide +kernel
private theorem endpoint_11_61_p8 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 8 240509006000446230 = some 242706627476799224 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 6 2 240509006000446230 242706627476799224 242706627476799224 endpoint_11_61_p6 endpoint_11_61_w6
private theorem endpoint_11_61_w8 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 8 2 242706627476799224 = some 242706627476799224 := by decide +kernel
private theorem endpoint_11_61_p10 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 10 240509006000446230 = some 242706627476799224 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 8 2 240509006000446230 242706627476799224 242706627476799224 endpoint_11_61_p8 endpoint_11_61_w8
def endpoint_11_61 : CertifiedEndpoint :=
  ⟨⟨11, 61, 2939⟩, 242706627476799224, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_11_61_flag endpoint_11_61_sources 10 240509006000446230 242706627476799224 rfl endpoint_11_61_base endpoint_11_61_p10) (by decide)⟩
private def endpoint_11_62_flag : Flag := ⟨11, 62, 2893⟩
private def endpoint_11_62_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_11_62_base : receiptBase endpoint_11_62_flag endpoint_11_62_sources = some 241347191204384670 := by decide +kernel
private theorem endpoint_11_62_w0 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 2 241347191204384670 = some 241347191204384670 := by decide +kernel
private theorem endpoint_11_62_w2 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 2 2 241347191204384670 = some 241347191204384670 := by decide +kernel
private theorem endpoint_11_62_p4 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 4 241347191204384670 = some 241347191204384670 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 2 2 241347191204384670 241347191204384670 241347191204384670 endpoint_11_62_w0 endpoint_11_62_w2
private theorem endpoint_11_62_w4 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 4 2 241347191204384670 = some 241347191204384670 := by decide +kernel
private theorem endpoint_11_62_p6 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 6 241347191204384670 = some 241347191204384670 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 4 2 241347191204384670 241347191204384670 241347191204384670 endpoint_11_62_p4 endpoint_11_62_w4
private theorem endpoint_11_62_w6 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 6 2 241347191204384670 = some 241347191204384670 := by decide +kernel
private theorem endpoint_11_62_p8 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 8 241347191204384670 = some 241347191204384670 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 6 2 241347191204384670 241347191204384670 241347191204384670 endpoint_11_62_p6 endpoint_11_62_w6
private theorem endpoint_11_62_w8 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 8 2 241347191204384670 = some 241347191204384670 := by decide +kernel
private theorem endpoint_11_62_p10 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 10 241347191204384670 = some 241347191204384670 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 8 2 241347191204384670 241347191204384670 241347191204384670 endpoint_11_62_p8 endpoint_11_62_w8
def endpoint_11_62 : CertifiedEndpoint :=
  ⟨⟨11, 62, 2893⟩, 241347191204384670, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_11_62_flag endpoint_11_62_sources 10 241347191204384670 241347191204384670 rfl endpoint_11_62_base endpoint_11_62_p10) (by decide)⟩
private def endpoint_11_63_flag : Flag := ⟨11, 63, 2844⟩
private def endpoint_11_63_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_11_63_base : receiptBase endpoint_11_63_flag endpoint_11_63_sources = some 240672432267879982 := by decide +kernel
private theorem endpoint_11_63_w0 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 2 240672432267879982 = some 241639497019463650 := by decide +kernel
private theorem endpoint_11_63_w2 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 2 2 241639497019463650 = some 241639497019463650 := by decide +kernel
private theorem endpoint_11_63_p4 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 4 240672432267879982 = some 241639497019463650 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 2 2 240672432267879982 241639497019463650 241639497019463650 endpoint_11_63_w0 endpoint_11_63_w2
private theorem endpoint_11_63_w4 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 4 2 241639497019463650 = some 241639497019463650 := by decide +kernel
private theorem endpoint_11_63_p6 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 6 240672432267879982 = some 241639497019463650 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 4 2 240672432267879982 241639497019463650 241639497019463650 endpoint_11_63_p4 endpoint_11_63_w4
private theorem endpoint_11_63_w6 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 6 2 241639497019463650 = some 241639497019463650 := by decide +kernel
private theorem endpoint_11_63_p8 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 8 240672432267879982 = some 241639497019463650 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 6 2 240672432267879982 241639497019463650 241639497019463650 endpoint_11_63_p6 endpoint_11_63_w6
private theorem endpoint_11_63_w8 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 8 2 241639497019463650 = some 241639497019463650 := by decide +kernel
private theorem endpoint_11_63_p10 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 10 240672432267879982 = some 241639497019463650 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 8 2 240672432267879982 241639497019463650 241639497019463650 endpoint_11_63_p8 endpoint_11_63_w8
def endpoint_11_63 : CertifiedEndpoint :=
  ⟨⟨11, 63, 2844⟩, 241639497019463650, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_11_63_flag endpoint_11_63_sources 10 240672432267879982 241639497019463650 rfl endpoint_11_63_base endpoint_11_63_p10) (by decide)⟩
private def endpoint_11_64_flag : Flag := ⟨11, 64, 2793⟩
private def endpoint_11_64_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_11_64_base : receiptBase endpoint_11_64_flag endpoint_11_64_sources = some 240916280207059321 := by decide +kernel
private theorem endpoint_11_64_w0 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 2 240916280207059321 = some 240916280207059321 := by decide +kernel
private theorem endpoint_11_64_w2 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 2 2 240916280207059321 = some 240916280207059321 := by decide +kernel
private theorem endpoint_11_64_p4 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 4 240916280207059321 = some 240916280207059321 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 2 2 240916280207059321 240916280207059321 240916280207059321 endpoint_11_64_w0 endpoint_11_64_w2
private theorem endpoint_11_64_w4 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 4 2 240916280207059321 = some 240916280207059321 := by decide +kernel
private theorem endpoint_11_64_p6 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 6 240916280207059321 = some 240916280207059321 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 4 2 240916280207059321 240916280207059321 240916280207059321 endpoint_11_64_p4 endpoint_11_64_w4
private theorem endpoint_11_64_w6 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 6 2 240916280207059321 = some 240916280207059321 := by decide +kernel
private theorem endpoint_11_64_p8 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 8 240916280207059321 = some 240916280207059321 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 6 2 240916280207059321 240916280207059321 240916280207059321 endpoint_11_64_p6 endpoint_11_64_w6
private theorem endpoint_11_64_w8 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 8 2 240916280207059321 = some 240916280207059321 := by decide +kernel
private theorem endpoint_11_64_p10 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 10 240916280207059321 = some 240916280207059321 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 8 2 240916280207059321 240916280207059321 240916280207059321 endpoint_11_64_p8 endpoint_11_64_w8
def endpoint_11_64 : CertifiedEndpoint :=
  ⟨⟨11, 64, 2793⟩, 240916280207059321, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_11_64_flag endpoint_11_64_sources 10 240916280207059321 240916280207059321 rfl endpoint_11_64_base endpoint_11_64_p10) (by decide)⟩
private def endpoint_11_65_flag : Flag := ⟨11, 65, 2740⟩
private def endpoint_11_65_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_11_65_base : receiptBase endpoint_11_65_flag endpoint_11_65_sources = some 240898258766000099 := by decide +kernel
private theorem endpoint_11_65_w0 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 2 240898258766000099 = some 240898258766000099 := by decide +kernel
private theorem endpoint_11_65_w2 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 2 2 240898258766000099 = some 240898258766000099 := by decide +kernel
private theorem endpoint_11_65_p4 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 4 240898258766000099 = some 240898258766000099 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 2 2 240898258766000099 240898258766000099 240898258766000099 endpoint_11_65_w0 endpoint_11_65_w2
private theorem endpoint_11_65_w4 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 4 2 240898258766000099 = some 240898258766000099 := by decide +kernel
private theorem endpoint_11_65_p6 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 6 240898258766000099 = some 240898258766000099 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 4 2 240898258766000099 240898258766000099 240898258766000099 endpoint_11_65_p4 endpoint_11_65_w4
private theorem endpoint_11_65_w6 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 6 2 240898258766000099 = some 240898258766000099 := by decide +kernel
private theorem endpoint_11_65_p8 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 8 240898258766000099 = some 240898258766000099 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 6 2 240898258766000099 240898258766000099 240898258766000099 endpoint_11_65_p6 endpoint_11_65_w6
private theorem endpoint_11_65_w8 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 8 2 240898258766000099 = some 240898258766000099 := by decide +kernel
private theorem endpoint_11_65_p10 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 10 240898258766000099 = some 240898258766000099 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 8 2 240898258766000099 240898258766000099 240898258766000099 endpoint_11_65_p8 endpoint_11_65_w8
def endpoint_11_65 : CertifiedEndpoint :=
  ⟨⟨11, 65, 2740⟩, 240898258766000099, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_11_65_flag endpoint_11_65_sources 10 240898258766000099 240898258766000099 rfl endpoint_11_65_base endpoint_11_65_p10) (by decide)⟩
private def endpoint_11_66_flag : Flag := ⟨11, 66, 2685⟩
private def endpoint_11_66_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_66_base : receiptBase endpoint_11_66_flag endpoint_11_66_sources = some 240453901116260438 := by decide +kernel
private theorem endpoint_11_66_w0 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 2 240453901116260438 = some 240453901116260438 := by decide +kernel
private theorem endpoint_11_66_w2 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 2 2 240453901116260438 = some 240453901116260438 := by decide +kernel
private theorem endpoint_11_66_p4 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 4 240453901116260438 = some 240453901116260438 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 2 2 240453901116260438 240453901116260438 240453901116260438 endpoint_11_66_w0 endpoint_11_66_w2
private theorem endpoint_11_66_w4 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 4 2 240453901116260438 = some 240453901116260438 := by decide +kernel
private theorem endpoint_11_66_p6 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 6 240453901116260438 = some 240453901116260438 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 4 2 240453901116260438 240453901116260438 240453901116260438 endpoint_11_66_p4 endpoint_11_66_w4
private theorem endpoint_11_66_w6 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 6 2 240453901116260438 = some 240453901116260438 := by decide +kernel
private theorem endpoint_11_66_p8 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 8 240453901116260438 = some 240453901116260438 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 6 2 240453901116260438 240453901116260438 240453901116260438 endpoint_11_66_p6 endpoint_11_66_w6
private theorem endpoint_11_66_w8 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 8 2 240453901116260438 = some 240453901116260438 := by decide +kernel
private theorem endpoint_11_66_p10 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 10 240453901116260438 = some 240453901116260438 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 8 2 240453901116260438 240453901116260438 240453901116260438 endpoint_11_66_p8 endpoint_11_66_w8
def endpoint_11_66 : CertifiedEndpoint :=
  ⟨⟨11, 66, 2685⟩, 240453901116260438, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_66_flag endpoint_11_66_sources 10 240453901116260438 240453901116260438 rfl endpoint_11_66_base endpoint_11_66_p10) (by decide)⟩

def endpointBlock07 : List CertifiedEndpoint := [
  endpoint_10_25, endpoint_10_26, endpoint_10_27, endpoint_10_28, endpoint_10_29, endpoint_10_30, endpoint_10_31,
  endpoint_10_32, endpoint_10_33, endpoint_10_34, endpoint_10_35, endpoint_10_36, endpoint_10_37, endpoint_10_38,
  endpoint_10_39, endpoint_10_40, endpoint_10_41, endpoint_10_42, endpoint_10_43, endpoint_10_44, endpoint_10_45,
  endpoint_10_46, endpoint_10_47, endpoint_10_48, endpoint_10_49, endpoint_10_50, endpoint_10_51, endpoint_10_52,
  endpoint_10_53, endpoint_10_54, endpoint_10_55, endpoint_10_56, endpoint_10_57, endpoint_10_58, endpoint_10_59,
  endpoint_10_60, endpoint_10_61, endpoint_10_62, endpoint_10_63, endpoint_10_64, endpoint_10_65, endpoint_10_66,
  endpoint_10_67, endpoint_10_68, endpoint_10_69, endpoint_10_70, endpoint_10_71, endpoint_10_72, endpoint_10_73,
  endpoint_10_74, endpoint_10_75, endpoint_10_76, endpoint_10_77, endpoint_10_78, endpoint_10_79, endpoint_10_80,
  endpoint_10_81, endpoint_10_82, endpoint_10_83, endpoint_10_84, endpoint_10_85, endpoint_10_86, endpoint_10_87,
  endpoint_10_88, endpoint_10_89, endpoint_10_90, endpoint_10_91, endpoint_10_92, endpoint_10_93, endpoint_10_94,
  endpoint_10_95, endpoint_11_11, endpoint_11_12, endpoint_11_13, endpoint_11_14, endpoint_11_15, endpoint_11_16,
  endpoint_11_17, endpoint_11_18, endpoint_11_19, endpoint_11_20, endpoint_11_21, endpoint_11_22, endpoint_11_23,
  endpoint_11_24, endpoint_11_25, endpoint_11_26, endpoint_11_27, endpoint_11_28, endpoint_11_29, endpoint_11_30,
  endpoint_11_31, endpoint_11_32, endpoint_11_33, endpoint_11_34, endpoint_11_35, endpoint_11_36, endpoint_11_37,
  endpoint_11_38, endpoint_11_39, endpoint_11_40, endpoint_11_41, endpoint_11_42, endpoint_11_43, endpoint_11_44,
  endpoint_11_45, endpoint_11_46, endpoint_11_47, endpoint_11_48, endpoint_11_49, endpoint_11_50, endpoint_11_51,
  endpoint_11_52, endpoint_11_53, endpoint_11_54, endpoint_11_55, endpoint_11_56, endpoint_11_57, endpoint_11_58,
  endpoint_11_59, endpoint_11_60, endpoint_11_61, endpoint_11_62, endpoint_11_63, endpoint_11_64, endpoint_11_65,
  endpoint_11_66
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
