import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_10_38_flag : Flag := ⟨10, 38, 3867⟩
private def endpoint_10_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_38_base : receiptBase endpoint_10_38_flag endpoint_10_38_sources = some 193352229062095259 := by decide +kernel
private theorem endpoint_10_38_w0 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 2 193352229062095259 = some 193352229062095259 := by decide +kernel
private theorem endpoint_10_38_w2 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 2 2 193352229062095259 = some 193352229062095259 := by decide +kernel
private theorem endpoint_10_38_p4 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 4 193352229062095259 = some 193352229062095259 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 2 2 193352229062095259 193352229062095259 193352229062095259 endpoint_10_38_w0 endpoint_10_38_w2
private theorem endpoint_10_38_w4 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 4 2 193352229062095259 = some 193352229062095259 := by decide +kernel
private theorem endpoint_10_38_p6 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 6 193352229062095259 = some 193352229062095259 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 4 2 193352229062095259 193352229062095259 193352229062095259 endpoint_10_38_p4 endpoint_10_38_w4
private theorem endpoint_10_38_w6 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 6 2 193352229062095259 = some 193352229062095259 := by decide +kernel
private theorem endpoint_10_38_p8 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 8 193352229062095259 = some 193352229062095259 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 6 2 193352229062095259 193352229062095259 193352229062095259 endpoint_10_38_p6 endpoint_10_38_w6
private theorem endpoint_10_38_w8 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 8 1 193352229062095259 = some 193352229062095259 := by decide +kernel
private theorem endpoint_10_38_p9 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 9 193352229062095259 = some 193352229062095259 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 8 1 193352229062095259 193352229062095259 193352229062095259 endpoint_10_38_p8 endpoint_10_38_w8
def endpoint_10_38 : CertifiedEndpoint :=
  ⟨⟨10, 38, 3867⟩, 193352229062095259, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_38_flag endpoint_10_38_sources 9 193352229062095259 193352229062095259 rfl endpoint_10_38_base endpoint_10_38_p9) (by decide)⟩
private def endpoint_10_39_flag : Flag := ⟨10, 39, 3842⟩
private def endpoint_10_39_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_39_base : receiptBase endpoint_10_39_flag endpoint_10_39_sources = some 196356002374640489 := by decide +kernel
private theorem endpoint_10_39_w0 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 2 196356002374640489 = some 196356002374640489 := by decide +kernel
private theorem endpoint_10_39_w2 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 2 2 196356002374640489 = some 196356002374640489 := by decide +kernel
private theorem endpoint_10_39_p4 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 4 196356002374640489 = some 196356002374640489 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 2 2 196356002374640489 196356002374640489 196356002374640489 endpoint_10_39_w0 endpoint_10_39_w2
private theorem endpoint_10_39_w4 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 4 2 196356002374640489 = some 196356002374640489 := by decide +kernel
private theorem endpoint_10_39_p6 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 6 196356002374640489 = some 196356002374640489 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 4 2 196356002374640489 196356002374640489 196356002374640489 endpoint_10_39_p4 endpoint_10_39_w4
private theorem endpoint_10_39_w6 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 6 2 196356002374640489 = some 196356002374640489 := by decide +kernel
private theorem endpoint_10_39_p8 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 8 196356002374640489 = some 196356002374640489 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 6 2 196356002374640489 196356002374640489 196356002374640489 endpoint_10_39_p6 endpoint_10_39_w6
private theorem endpoint_10_39_w8 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 8 1 196356002374640489 = some 196356002374640489 := by decide +kernel
private theorem endpoint_10_39_p9 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 9 196356002374640489 = some 196356002374640489 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 8 1 196356002374640489 196356002374640489 196356002374640489 endpoint_10_39_p8 endpoint_10_39_w8
def endpoint_10_39 : CertifiedEndpoint :=
  ⟨⟨10, 39, 3842⟩, 196356002374640489, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_39_flag endpoint_10_39_sources 9 196356002374640489 196356002374640489 rfl endpoint_10_39_base endpoint_10_39_p9) (by decide)⟩
private def endpoint_10_40_flag : Flag := ⟨10, 40, 3817⟩
private def endpoint_10_40_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_40_base : receiptBase endpoint_10_40_flag endpoint_10_40_sources = some 199304501319160754 := by decide +kernel
private theorem endpoint_10_40_w0 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 2 199304501319160754 = some 199304501319160754 := by decide +kernel
private theorem endpoint_10_40_w2 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 2 2 199304501319160754 = some 199304501319160754 := by decide +kernel
private theorem endpoint_10_40_p4 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 4 199304501319160754 = some 199304501319160754 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 2 2 199304501319160754 199304501319160754 199304501319160754 endpoint_10_40_w0 endpoint_10_40_w2
private theorem endpoint_10_40_w4 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 4 2 199304501319160754 = some 199304501319160754 := by decide +kernel
private theorem endpoint_10_40_p6 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 6 199304501319160754 = some 199304501319160754 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 4 2 199304501319160754 199304501319160754 199304501319160754 endpoint_10_40_p4 endpoint_10_40_w4
private theorem endpoint_10_40_w6 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 6 2 199304501319160754 = some 199304501319160754 := by decide +kernel
private theorem endpoint_10_40_p8 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 8 199304501319160754 = some 199304501319160754 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 6 2 199304501319160754 199304501319160754 199304501319160754 endpoint_10_40_p6 endpoint_10_40_w6
private theorem endpoint_10_40_w8 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 8 1 199304501319160754 = some 199304501319160754 := by decide +kernel
private theorem endpoint_10_40_p9 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 9 199304501319160754 = some 199304501319160754 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 8 1 199304501319160754 199304501319160754 199304501319160754 endpoint_10_40_p8 endpoint_10_40_w8
def endpoint_10_40 : CertifiedEndpoint :=
  ⟨⟨10, 40, 3817⟩, 199304501319160754, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_40_flag endpoint_10_40_sources 9 199304501319160754 199304501319160754 rfl endpoint_10_40_base endpoint_10_40_p9) (by decide)⟩
private def endpoint_10_41_flag : Flag := ⟨10, 41, 3791⟩
private def endpoint_10_41_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_41_base : receiptBase endpoint_10_41_flag endpoint_10_41_sources = some 202145207494673669 := by decide +kernel
private theorem endpoint_10_41_w0 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 2 202145207494673669 = some 202145207494673669 := by decide +kernel
private theorem endpoint_10_41_w2 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 2 2 202145207494673669 = some 202145207494673669 := by decide +kernel
private theorem endpoint_10_41_p4 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 4 202145207494673669 = some 202145207494673669 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 2 2 202145207494673669 202145207494673669 202145207494673669 endpoint_10_41_w0 endpoint_10_41_w2
private theorem endpoint_10_41_w4 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 4 2 202145207494673669 = some 202145207494673669 := by decide +kernel
private theorem endpoint_10_41_p6 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 6 202145207494673669 = some 202145207494673669 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 4 2 202145207494673669 202145207494673669 202145207494673669 endpoint_10_41_p4 endpoint_10_41_w4
private theorem endpoint_10_41_w6 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 6 2 202145207494673669 = some 202145207494673669 := by decide +kernel
private theorem endpoint_10_41_p8 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 8 202145207494673669 = some 202145207494673669 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 6 2 202145207494673669 202145207494673669 202145207494673669 endpoint_10_41_p6 endpoint_10_41_w6
private theorem endpoint_10_41_w8 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 8 1 202145207494673669 = some 202145207494673669 := by decide +kernel
private theorem endpoint_10_41_p9 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 9 202145207494673669 = some 202145207494673669 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 8 1 202145207494673669 202145207494673669 202145207494673669 endpoint_10_41_p8 endpoint_10_41_w8
def endpoint_10_41 : CertifiedEndpoint :=
  ⟨⟨10, 41, 3791⟩, 202145207494673669, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_41_flag endpoint_10_41_sources 9 202145207494673669 202145207494673669 rfl endpoint_10_41_base endpoint_10_41_p9) (by decide)⟩
private def endpoint_10_42_flag : Flag := ⟨10, 42, 3765⟩
private def endpoint_10_42_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_42_base : receiptBase endpoint_10_42_flag endpoint_10_42_sources = some 204928471856341230 := by decide +kernel
private theorem endpoint_10_42_w0 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 2 204928471856341230 = some 204928471856341230 := by decide +kernel
private theorem endpoint_10_42_w2 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 2 2 204928471856341230 = some 204928471856341230 := by decide +kernel
private theorem endpoint_10_42_p4 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 4 204928471856341230 = some 204928471856341230 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 2 2 204928471856341230 204928471856341230 204928471856341230 endpoint_10_42_w0 endpoint_10_42_w2
private theorem endpoint_10_42_w4 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 4 2 204928471856341230 = some 204928471856341230 := by decide +kernel
private theorem endpoint_10_42_p6 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 6 204928471856341230 = some 204928471856341230 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 4 2 204928471856341230 204928471856341230 204928471856341230 endpoint_10_42_p4 endpoint_10_42_w4
private theorem endpoint_10_42_w6 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 6 2 204928471856341230 = some 204928471856341230 := by decide +kernel
private theorem endpoint_10_42_p8 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 8 204928471856341230 = some 204928471856341230 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 6 2 204928471856341230 204928471856341230 204928471856341230 endpoint_10_42_p6 endpoint_10_42_w6
private theorem endpoint_10_42_w8 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 8 1 204928471856341230 = some 204928471856341230 := by decide +kernel
private theorem endpoint_10_42_p9 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 9 204928471856341230 = some 204928471856341230 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 8 1 204928471856341230 204928471856341230 204928471856341230 endpoint_10_42_p8 endpoint_10_42_w8
def endpoint_10_42 : CertifiedEndpoint :=
  ⟨⟨10, 42, 3765⟩, 204928471856341230, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_42_flag endpoint_10_42_sources 9 204928471856341230 204928471856341230 rfl endpoint_10_42_base endpoint_10_42_p9) (by decide)⟩
private def endpoint_10_43_flag : Flag := ⟨10, 43, 3739⟩
private def endpoint_10_43_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_43_base : receiptBase endpoint_10_43_flag endpoint_10_43_sources = some 208172437324788956 := by decide +kernel
private theorem endpoint_10_43_w0 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 2 208172437324788956 = some 208172437324788956 := by decide +kernel
private theorem endpoint_10_43_w2 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 2 2 208172437324788956 = some 208172437324788956 := by decide +kernel
private theorem endpoint_10_43_p4 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 4 208172437324788956 = some 208172437324788956 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 2 2 208172437324788956 208172437324788956 208172437324788956 endpoint_10_43_w0 endpoint_10_43_w2
private theorem endpoint_10_43_w4 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 4 2 208172437324788956 = some 208172437324788956 := by decide +kernel
private theorem endpoint_10_43_p6 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 6 208172437324788956 = some 208172437324788956 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 4 2 208172437324788956 208172437324788956 208172437324788956 endpoint_10_43_p4 endpoint_10_43_w4
private theorem endpoint_10_43_w6 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 6 2 208172437324788956 = some 208172437324788956 := by decide +kernel
private theorem endpoint_10_43_p8 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 8 208172437324788956 = some 208172437324788956 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 6 2 208172437324788956 208172437324788956 208172437324788956 endpoint_10_43_p6 endpoint_10_43_w6
private theorem endpoint_10_43_w8 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 8 1 208172437324788956 = some 208172437324788956 := by decide +kernel
private theorem endpoint_10_43_p9 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 9 208172437324788956 = some 208172437324788956 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 8 1 208172437324788956 208172437324788956 208172437324788956 endpoint_10_43_p8 endpoint_10_43_w8
def endpoint_10_43 : CertifiedEndpoint :=
  ⟨⟨10, 43, 3739⟩, 208172437324788956, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_43_flag endpoint_10_43_sources 9 208172437324788956 208172437324788956 rfl endpoint_10_43_base endpoint_10_43_p9) (by decide)⟩
private def endpoint_10_44_flag : Flag := ⟨10, 44, 3712⟩
private def endpoint_10_44_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_44_base : receiptBase endpoint_10_44_flag endpoint_10_44_sources = some 210755228395869763 := by decide +kernel
private theorem endpoint_10_44_w0 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 2 210755228395869763 = some 210755228395869763 := by decide +kernel
private theorem endpoint_10_44_w2 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 2 2 210755228395869763 = some 210755228395869763 := by decide +kernel
private theorem endpoint_10_44_p4 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 4 210755228395869763 = some 210755228395869763 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 2 2 210755228395869763 210755228395869763 210755228395869763 endpoint_10_44_w0 endpoint_10_44_w2
private theorem endpoint_10_44_w4 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 4 2 210755228395869763 = some 210755228395869763 := by decide +kernel
private theorem endpoint_10_44_p6 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 6 210755228395869763 = some 210755228395869763 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 4 2 210755228395869763 210755228395869763 210755228395869763 endpoint_10_44_p4 endpoint_10_44_w4
private theorem endpoint_10_44_w6 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 6 2 210755228395869763 = some 210755228395869763 := by decide +kernel
private theorem endpoint_10_44_p8 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 8 210755228395869763 = some 210755228395869763 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 6 2 210755228395869763 210755228395869763 210755228395869763 endpoint_10_44_p6 endpoint_10_44_w6
private theorem endpoint_10_44_w8 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 8 1 210755228395869763 = some 210755228395869763 := by decide +kernel
private theorem endpoint_10_44_p9 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 9 210755228395869763 = some 210755228395869763 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 8 1 210755228395869763 210755228395869763 210755228395869763 endpoint_10_44_p8 endpoint_10_44_w8
def endpoint_10_44 : CertifiedEndpoint :=
  ⟨⟨10, 44, 3712⟩, 210755228395869763, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_44_flag endpoint_10_44_sources 9 210755228395869763 210755228395869763 rfl endpoint_10_44_base endpoint_10_44_p9) (by decide)⟩
private def endpoint_10_45_flag : Flag := ⟨10, 45, 3684⟩
private def endpoint_10_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_45_base : receiptBase endpoint_10_45_flag endpoint_10_45_sources = some 213221595232453603 := by decide +kernel
private theorem endpoint_10_45_w0 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 2 213221595232453603 = some 213221595232453603 := by decide +kernel
private theorem endpoint_10_45_w2 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 2 2 213221595232453603 = some 213221595232453603 := by decide +kernel
private theorem endpoint_10_45_p4 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 4 213221595232453603 = some 213221595232453603 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 2 2 213221595232453603 213221595232453603 213221595232453603 endpoint_10_45_w0 endpoint_10_45_w2
private theorem endpoint_10_45_w4 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 4 2 213221595232453603 = some 213221595232453603 := by decide +kernel
private theorem endpoint_10_45_p6 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 6 213221595232453603 = some 213221595232453603 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 4 2 213221595232453603 213221595232453603 213221595232453603 endpoint_10_45_p4 endpoint_10_45_w4
private theorem endpoint_10_45_w6 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 6 2 213221595232453603 = some 213221595232453603 := by decide +kernel
private theorem endpoint_10_45_p8 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 8 213221595232453603 = some 213221595232453603 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 6 2 213221595232453603 213221595232453603 213221595232453603 endpoint_10_45_p6 endpoint_10_45_w6
private theorem endpoint_10_45_w8 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 8 1 213221595232453603 = some 213221595232453603 := by decide +kernel
private theorem endpoint_10_45_p9 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 9 213221595232453603 = some 213221595232453603 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 8 1 213221595232453603 213221595232453603 213221595232453603 endpoint_10_45_p8 endpoint_10_45_w8
def endpoint_10_45 : CertifiedEndpoint :=
  ⟨⟨10, 45, 3684⟩, 213221595232453603, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_45_flag endpoint_10_45_sources 9 213221595232453603 213221595232453603 rfl endpoint_10_45_base endpoint_10_45_p9) (by decide)⟩
private def endpoint_10_46_flag : Flag := ⟨10, 46, 3656⟩
private def endpoint_10_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_46_base : receiptBase endpoint_10_46_flag endpoint_10_46_sources = some 215626446297350927 := by decide +kernel
private theorem endpoint_10_46_w0 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 2 215626446297350927 = some 215626446297350927 := by decide +kernel
private theorem endpoint_10_46_w2 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 2 2 215626446297350927 = some 215626446297350927 := by decide +kernel
private theorem endpoint_10_46_p4 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 4 215626446297350927 = some 215626446297350927 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 2 2 215626446297350927 215626446297350927 215626446297350927 endpoint_10_46_w0 endpoint_10_46_w2
private theorem endpoint_10_46_w4 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 4 2 215626446297350927 = some 215626446297350927 := by decide +kernel
private theorem endpoint_10_46_p6 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 6 215626446297350927 = some 215626446297350927 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 4 2 215626446297350927 215626446297350927 215626446297350927 endpoint_10_46_p4 endpoint_10_46_w4
private theorem endpoint_10_46_w6 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 6 2 215626446297350927 = some 215626446297350927 := by decide +kernel
private theorem endpoint_10_46_p8 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 8 215626446297350927 = some 215626446297350927 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 6 2 215626446297350927 215626446297350927 215626446297350927 endpoint_10_46_p6 endpoint_10_46_w6
private theorem endpoint_10_46_w8 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 8 1 215626446297350927 = some 215626446297350927 := by decide +kernel
private theorem endpoint_10_46_p9 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 9 215626446297350927 = some 215626446297350927 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 8 1 215626446297350927 215626446297350927 215626446297350927 endpoint_10_46_p8 endpoint_10_46_w8
def endpoint_10_46 : CertifiedEndpoint :=
  ⟨⟨10, 46, 3656⟩, 215626446297350927, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_46_flag endpoint_10_46_sources 9 215626446297350927 215626446297350927 rfl endpoint_10_46_base endpoint_10_46_p9) (by decide)⟩
private def endpoint_10_47_flag : Flag := ⟨10, 47, 3628⟩
private def endpoint_10_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_47_base : receiptBase endpoint_10_47_flag endpoint_10_47_sources = some 217969781590561735 := by decide +kernel
private theorem endpoint_10_47_w0 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 2 217969781590561735 = some 217969781590561735 := by decide +kernel
private theorem endpoint_10_47_w2 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 2 2 217969781590561735 = some 217969781590561735 := by decide +kernel
private theorem endpoint_10_47_p4 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 4 217969781590561735 = some 217969781590561735 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 2 2 217969781590561735 217969781590561735 217969781590561735 endpoint_10_47_w0 endpoint_10_47_w2
private theorem endpoint_10_47_w4 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 4 2 217969781590561735 = some 217969781590561735 := by decide +kernel
private theorem endpoint_10_47_p6 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 6 217969781590561735 = some 217969781590561735 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 4 2 217969781590561735 217969781590561735 217969781590561735 endpoint_10_47_p4 endpoint_10_47_w4
private theorem endpoint_10_47_w6 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 6 2 217969781590561735 = some 217969781590561735 := by decide +kernel
private theorem endpoint_10_47_p8 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 8 217969781590561735 = some 217969781590561735 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 6 2 217969781590561735 217969781590561735 217969781590561735 endpoint_10_47_p6 endpoint_10_47_w6
private theorem endpoint_10_47_w8 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 8 1 217969781590561735 = some 217969781590561735 := by decide +kernel
private theorem endpoint_10_47_p9 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 9 217969781590561735 = some 217969781590561735 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 8 1 217969781590561735 217969781590561735 217969781590561735 endpoint_10_47_p8 endpoint_10_47_w8
def endpoint_10_47 : CertifiedEndpoint :=
  ⟨⟨10, 47, 3628⟩, 217969781590561735, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_47_flag endpoint_10_47_sources 9 217969781590561735 217969781590561735 rfl endpoint_10_47_base endpoint_10_47_p9) (by decide)⟩
private def endpoint_10_48_flag : Flag := ⟨10, 48, 3599⟩
private def endpoint_10_48_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_48_base : receiptBase endpoint_10_48_flag endpoint_10_48_sources = some 220191296528952199 := by decide +kernel
private theorem endpoint_10_48_w0 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 2 220191296528952199 = some 220191296528952199 := by decide +kernel
private theorem endpoint_10_48_w2 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 2 2 220191296528952199 = some 220191296528952199 := by decide +kernel
private theorem endpoint_10_48_p4 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 4 220191296528952199 = some 220191296528952199 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 2 2 220191296528952199 220191296528952199 220191296528952199 endpoint_10_48_w0 endpoint_10_48_w2
private theorem endpoint_10_48_w4 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 4 2 220191296528952199 = some 220191296528952199 := by decide +kernel
private theorem endpoint_10_48_p6 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 6 220191296528952199 = some 220191296528952199 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 4 2 220191296528952199 220191296528952199 220191296528952199 endpoint_10_48_p4 endpoint_10_48_w4
private theorem endpoint_10_48_w6 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 6 2 220191296528952199 = some 220191296528952199 := by decide +kernel
private theorem endpoint_10_48_p8 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 8 220191296528952199 = some 220191296528952199 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 6 2 220191296528952199 220191296528952199 220191296528952199 endpoint_10_48_p6 endpoint_10_48_w6
private theorem endpoint_10_48_w8 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 8 1 220191296528952199 = some 220191296528952199 := by decide +kernel
private theorem endpoint_10_48_p9 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 9 220191296528952199 = some 220191296528952199 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 8 1 220191296528952199 220191296528952199 220191296528952199 endpoint_10_48_p8 endpoint_10_48_w8
def endpoint_10_48 : CertifiedEndpoint :=
  ⟨⟨10, 48, 3599⟩, 220191296528952199, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_48_flag endpoint_10_48_sources 9 220191296528952199 220191296528952199 rfl endpoint_10_48_base endpoint_10_48_p9) (by decide)⟩
private def endpoint_10_49_flag : Flag := ⟨10, 49, 3569⟩
private def endpoint_10_49_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_49_base : receiptBase endpoint_10_49_flag endpoint_10_49_sources = some 222287753440328290 := by decide +kernel
private theorem endpoint_10_49_w0 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 2 222287753440328290 = some 222287753440328290 := by decide +kernel
private theorem endpoint_10_49_w2 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 2 2 222287753440328290 = some 222287753440328290 := by decide +kernel
private theorem endpoint_10_49_p4 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 4 222287753440328290 = some 222287753440328290 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 2 2 222287753440328290 222287753440328290 222287753440328290 endpoint_10_49_w0 endpoint_10_49_w2
private theorem endpoint_10_49_w4 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 4 2 222287753440328290 = some 222287753440328290 := by decide +kernel
private theorem endpoint_10_49_p6 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 6 222287753440328290 = some 222287753440328290 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 4 2 222287753440328290 222287753440328290 222287753440328290 endpoint_10_49_p4 endpoint_10_49_w4
private theorem endpoint_10_49_w6 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 6 2 222287753440328290 = some 222287753440328290 := by decide +kernel
private theorem endpoint_10_49_p8 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 8 222287753440328290 = some 222287753440328290 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 6 2 222287753440328290 222287753440328290 222287753440328290 endpoint_10_49_p6 endpoint_10_49_w6
private theorem endpoint_10_49_w8 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 8 1 222287753440328290 = some 222287753440328290 := by decide +kernel
private theorem endpoint_10_49_p9 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 9 222287753440328290 = some 222287753440328290 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 8 1 222287753440328290 222287753440328290 222287753440328290 endpoint_10_49_p8 endpoint_10_49_w8
def endpoint_10_49 : CertifiedEndpoint :=
  ⟨⟨10, 49, 3569⟩, 222287753440328290, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_49_flag endpoint_10_49_sources 9 222287753440328290 222287753440328290 rfl endpoint_10_49_base endpoint_10_49_p9) (by decide)⟩
private def endpoint_10_50_flag : Flag := ⟨10, 50, 3539⟩
private def endpoint_10_50_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_50_base : receiptBase endpoint_10_50_flag endpoint_10_50_sources = some 224318377683759163 := by decide +kernel
private theorem endpoint_10_50_w0 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 2 224318377683759163 = some 224318377683759163 := by decide +kernel
private theorem endpoint_10_50_w2 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 2 2 224318377683759163 = some 224318377683759163 := by decide +kernel
private theorem endpoint_10_50_p4 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 4 224318377683759163 = some 224318377683759163 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 2 2 224318377683759163 224318377683759163 224318377683759163 endpoint_10_50_w0 endpoint_10_50_w2
private theorem endpoint_10_50_w4 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 4 2 224318377683759163 = some 224318377683759163 := by decide +kernel
private theorem endpoint_10_50_p6 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 6 224318377683759163 = some 224318377683759163 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 4 2 224318377683759163 224318377683759163 224318377683759163 endpoint_10_50_p4 endpoint_10_50_w4
private theorem endpoint_10_50_w6 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 6 2 224318377683759163 = some 224318377683759163 := by decide +kernel
private theorem endpoint_10_50_p8 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 8 224318377683759163 = some 224318377683759163 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 6 2 224318377683759163 224318377683759163 224318377683759163 endpoint_10_50_p6 endpoint_10_50_w6
private theorem endpoint_10_50_w8 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 8 1 224318377683759163 = some 224318377683759163 := by decide +kernel
private theorem endpoint_10_50_p9 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 9 224318377683759163 = some 224318377683759163 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 8 1 224318377683759163 224318377683759163 224318377683759163 endpoint_10_50_p8 endpoint_10_50_w8
def endpoint_10_50 : CertifiedEndpoint :=
  ⟨⟨10, 50, 3539⟩, 224318377683759163, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_50_flag endpoint_10_50_sources 9 224318377683759163 224318377683759163 rfl endpoint_10_50_base endpoint_10_50_p9) (by decide)⟩
private def endpoint_10_51_flag : Flag := ⟨10, 51, 3508⟩
private def endpoint_10_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_51_base : receiptBase endpoint_10_51_flag endpoint_10_51_sources = some 226219627003916961 := by decide +kernel
private theorem endpoint_10_51_w0 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 2 226219627003916961 = some 226219627003916961 := by decide +kernel
private theorem endpoint_10_51_w2 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 2 2 226219627003916961 = some 226219627003916961 := by decide +kernel
private theorem endpoint_10_51_p4 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 4 226219627003916961 = some 226219627003916961 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 2 2 226219627003916961 226219627003916961 226219627003916961 endpoint_10_51_w0 endpoint_10_51_w2
private theorem endpoint_10_51_w4 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 4 2 226219627003916961 = some 226219627003916961 := by decide +kernel
private theorem endpoint_10_51_p6 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 6 226219627003916961 = some 226219627003916961 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 4 2 226219627003916961 226219627003916961 226219627003916961 endpoint_10_51_p4 endpoint_10_51_w4
private theorem endpoint_10_51_w6 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 6 2 226219627003916961 = some 226219627003916961 := by decide +kernel
private theorem endpoint_10_51_p8 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 8 226219627003916961 = some 226219627003916961 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 6 2 226219627003916961 226219627003916961 226219627003916961 endpoint_10_51_p6 endpoint_10_51_w6
private theorem endpoint_10_51_w8 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 8 1 226219627003916961 = some 226219627003916961 := by decide +kernel
private theorem endpoint_10_51_p9 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 9 226219627003916961 = some 226219627003916961 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 8 1 226219627003916961 226219627003916961 226219627003916961 endpoint_10_51_p8 endpoint_10_51_w8
def endpoint_10_51 : CertifiedEndpoint :=
  ⟨⟨10, 51, 3508⟩, 226219627003916961, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_51_flag endpoint_10_51_sources 9 226219627003916961 226219627003916961 rfl endpoint_10_51_base endpoint_10_51_p9) (by decide)⟩
private def endpoint_10_52_flag : Flag := ⟨10, 52, 3477⟩
private def endpoint_10_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_52_base : receiptBase endpoint_10_52_flag endpoint_10_52_sources = some 228052885208000189 := by decide +kernel
private theorem endpoint_10_52_w0 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 2 228052885208000189 = some 228052885208000189 := by decide +kernel
private theorem endpoint_10_52_w2 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 2 2 228052885208000189 = some 228052885208000189 := by decide +kernel
private theorem endpoint_10_52_p4 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 4 228052885208000189 = some 228052885208000189 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 2 2 228052885208000189 228052885208000189 228052885208000189 endpoint_10_52_w0 endpoint_10_52_w2
private theorem endpoint_10_52_w4 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 4 2 228052885208000189 = some 228052885208000189 := by decide +kernel
private theorem endpoint_10_52_p6 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 6 228052885208000189 = some 228052885208000189 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 4 2 228052885208000189 228052885208000189 228052885208000189 endpoint_10_52_p4 endpoint_10_52_w4
private theorem endpoint_10_52_w6 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 6 2 228052885208000189 = some 228052885208000189 := by decide +kernel
private theorem endpoint_10_52_p8 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 8 228052885208000189 = some 228052885208000189 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 6 2 228052885208000189 228052885208000189 228052885208000189 endpoint_10_52_p6 endpoint_10_52_w6
private theorem endpoint_10_52_w8 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 8 1 228052885208000189 = some 228052885208000189 := by decide +kernel
private theorem endpoint_10_52_p9 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 9 228052885208000189 = some 228052885208000189 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 8 1 228052885208000189 228052885208000189 228052885208000189 endpoint_10_52_p8 endpoint_10_52_w8
def endpoint_10_52 : CertifiedEndpoint :=
  ⟨⟨10, 52, 3477⟩, 228052885208000189, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_52_flag endpoint_10_52_sources 9 228052885208000189 228052885208000189 rfl endpoint_10_52_base endpoint_10_52_p9) (by decide)⟩
private def endpoint_10_53_flag : Flag := ⟨10, 53, 3444⟩
private def endpoint_10_53_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_10_53_base : receiptBase endpoint_10_53_flag endpoint_10_53_sources = some 230342926391433915 := by decide +kernel
private theorem endpoint_10_53_w0 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 2 230342926391433915 = some 230342926391433915 := by decide +kernel
private theorem endpoint_10_53_w2 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 2 2 230342926391433915 = some 230342926391433915 := by decide +kernel
private theorem endpoint_10_53_p4 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 4 230342926391433915 = some 230342926391433915 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 2 2 230342926391433915 230342926391433915 230342926391433915 endpoint_10_53_w0 endpoint_10_53_w2
private theorem endpoint_10_53_w4 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 4 2 230342926391433915 = some 230342926391433915 := by decide +kernel
private theorem endpoint_10_53_p6 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 6 230342926391433915 = some 230342926391433915 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 4 2 230342926391433915 230342926391433915 230342926391433915 endpoint_10_53_p4 endpoint_10_53_w4
private theorem endpoint_10_53_w6 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 6 2 230342926391433915 = some 230342926391433915 := by decide +kernel
private theorem endpoint_10_53_p8 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 8 230342926391433915 = some 230342926391433915 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 6 2 230342926391433915 230342926391433915 230342926391433915 endpoint_10_53_p6 endpoint_10_53_w6
private theorem endpoint_10_53_w8 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 8 1 230342926391433915 = some 230342926391433915 := by decide +kernel
private theorem endpoint_10_53_p9 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 9 230342926391433915 = some 230342926391433915 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 8 1 230342926391433915 230342926391433915 230342926391433915 endpoint_10_53_p8 endpoint_10_53_w8
def endpoint_10_53 : CertifiedEndpoint :=
  ⟨⟨10, 53, 3444⟩, 230342926391433915, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_10_53_flag endpoint_10_53_sources 9 230342926391433915 230342926391433915 rfl endpoint_10_53_base endpoint_10_53_p9) (by decide)⟩
private def endpoint_10_54_flag : Flag := ⟨10, 54, 3411⟩
private def endpoint_10_54_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_10_54_base : receiptBase endpoint_10_54_flag endpoint_10_54_sources = some 231913011512039517 := by decide +kernel
private theorem endpoint_10_54_w0 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 2 231913011512039517 = some 231913011512039517 := by decide +kernel
private theorem endpoint_10_54_w2 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 2 2 231913011512039517 = some 231913011512039517 := by decide +kernel
private theorem endpoint_10_54_p4 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 4 231913011512039517 = some 231913011512039517 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 2 2 231913011512039517 231913011512039517 231913011512039517 endpoint_10_54_w0 endpoint_10_54_w2
private theorem endpoint_10_54_w4 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 4 2 231913011512039517 = some 231913011512039517 := by decide +kernel
private theorem endpoint_10_54_p6 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 6 231913011512039517 = some 231913011512039517 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 4 2 231913011512039517 231913011512039517 231913011512039517 endpoint_10_54_p4 endpoint_10_54_w4
private theorem endpoint_10_54_w6 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 6 2 231913011512039517 = some 231913011512039517 := by decide +kernel
private theorem endpoint_10_54_p8 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 8 231913011512039517 = some 231913011512039517 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 6 2 231913011512039517 231913011512039517 231913011512039517 endpoint_10_54_p6 endpoint_10_54_w6
private theorem endpoint_10_54_w8 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 8 1 231913011512039517 = some 231913011512039517 := by decide +kernel
private theorem endpoint_10_54_p9 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 9 231913011512039517 = some 231913011512039517 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 8 1 231913011512039517 231913011512039517 231913011512039517 endpoint_10_54_p8 endpoint_10_54_w8
def endpoint_10_54 : CertifiedEndpoint :=
  ⟨⟨10, 54, 3411⟩, 231913011512039517, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_10_54_flag endpoint_10_54_sources 9 231913011512039517 231913011512039517 rfl endpoint_10_54_base endpoint_10_54_p9) (by decide)⟩
private def endpoint_10_55_flag : Flag := ⟨10, 55, 3378⟩
private def endpoint_10_55_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_10_55_base : receiptBase endpoint_10_55_flag endpoint_10_55_sources = some 233410482596284372 := by decide +kernel
private theorem endpoint_10_55_w0 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 2 233410482596284372 = some 233410482596284372 := by decide +kernel
private theorem endpoint_10_55_w2 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 2 2 233410482596284372 = some 233410482596284372 := by decide +kernel
private theorem endpoint_10_55_p4 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 4 233410482596284372 = some 233410482596284372 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 2 2 233410482596284372 233410482596284372 233410482596284372 endpoint_10_55_w0 endpoint_10_55_w2
private theorem endpoint_10_55_w4 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 4 2 233410482596284372 = some 233410482596284372 := by decide +kernel
private theorem endpoint_10_55_p6 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 6 233410482596284372 = some 233410482596284372 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 4 2 233410482596284372 233410482596284372 233410482596284372 endpoint_10_55_p4 endpoint_10_55_w4
private theorem endpoint_10_55_w6 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 6 2 233410482596284372 = some 233410482596284372 := by decide +kernel
private theorem endpoint_10_55_p8 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 8 233410482596284372 = some 233410482596284372 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 6 2 233410482596284372 233410482596284372 233410482596284372 endpoint_10_55_p6 endpoint_10_55_w6
private theorem endpoint_10_55_w8 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 8 1 233410482596284372 = some 233410482596284372 := by decide +kernel
private theorem endpoint_10_55_p9 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 9 233410482596284372 = some 233410482596284372 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 8 1 233410482596284372 233410482596284372 233410482596284372 endpoint_10_55_p8 endpoint_10_55_w8
def endpoint_10_55 : CertifiedEndpoint :=
  ⟨⟨10, 55, 3378⟩, 233410482596284372, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_10_55_flag endpoint_10_55_sources 9 233410482596284372 233410482596284372 rfl endpoint_10_55_base endpoint_10_55_p9) (by decide)⟩
private def endpoint_10_56_flag : Flag := ⟨10, 56, 3343⟩
private def endpoint_10_56_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_10_56_base : receiptBase endpoint_10_56_flag endpoint_10_56_sources = some 234904133216634830 := by decide +kernel
private theorem endpoint_10_56_w0 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 2 234904133216634830 = some 234904133216634830 := by decide +kernel
private theorem endpoint_10_56_w2 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 2 2 234904133216634830 = some 234904133216634830 := by decide +kernel
private theorem endpoint_10_56_p4 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 4 234904133216634830 = some 234904133216634830 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 2 2 234904133216634830 234904133216634830 234904133216634830 endpoint_10_56_w0 endpoint_10_56_w2
private theorem endpoint_10_56_w4 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 4 2 234904133216634830 = some 234904133216634830 := by decide +kernel
private theorem endpoint_10_56_p6 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 6 234904133216634830 = some 234904133216634830 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 4 2 234904133216634830 234904133216634830 234904133216634830 endpoint_10_56_p4 endpoint_10_56_w4
private theorem endpoint_10_56_w6 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 6 2 234904133216634830 = some 234904133216634830 := by decide +kernel
private theorem endpoint_10_56_p8 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 8 234904133216634830 = some 234904133216634830 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 6 2 234904133216634830 234904133216634830 234904133216634830 endpoint_10_56_p6 endpoint_10_56_w6
private theorem endpoint_10_56_w8 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 8 1 234904133216634830 = some 234904133216634830 := by decide +kernel
private theorem endpoint_10_56_p9 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 9 234904133216634830 = some 234904133216634830 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 8 1 234904133216634830 234904133216634830 234904133216634830 endpoint_10_56_p8 endpoint_10_56_w8
def endpoint_10_56 : CertifiedEndpoint :=
  ⟨⟨10, 56, 3343⟩, 234904133216634830, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_10_56_flag endpoint_10_56_sources 9 234904133216634830 234904133216634830 rfl endpoint_10_56_base endpoint_10_56_p9) (by decide)⟩
private def endpoint_10_57_flag : Flag := ⟨10, 57, 3307⟩
private def endpoint_10_57_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_57_base : receiptBase endpoint_10_57_flag endpoint_10_57_sources = some 238265204536306487 := by decide +kernel
private theorem endpoint_10_57_w0 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 2 238265204536306487 = some 238265204536306487 := by decide +kernel
private theorem endpoint_10_57_w2 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 2 2 238265204536306487 = some 238265204536306487 := by decide +kernel
private theorem endpoint_10_57_p4 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 4 238265204536306487 = some 238265204536306487 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 2 2 238265204536306487 238265204536306487 238265204536306487 endpoint_10_57_w0 endpoint_10_57_w2
private theorem endpoint_10_57_w4 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 4 2 238265204536306487 = some 238265204536306487 := by decide +kernel
private theorem endpoint_10_57_p6 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 6 238265204536306487 = some 238265204536306487 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 4 2 238265204536306487 238265204536306487 238265204536306487 endpoint_10_57_p4 endpoint_10_57_w4
private theorem endpoint_10_57_w6 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 6 2 238265204536306487 = some 238265204536306487 := by decide +kernel
private theorem endpoint_10_57_p8 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 8 238265204536306487 = some 238265204536306487 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 6 2 238265204536306487 238265204536306487 238265204536306487 endpoint_10_57_p6 endpoint_10_57_w6
private theorem endpoint_10_57_w8 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 8 1 238265204536306487 = some 238265204536306487 := by decide +kernel
private theorem endpoint_10_57_p9 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 9 238265204536306487 = some 238265204536306487 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 8 1 238265204536306487 238265204536306487 238265204536306487 endpoint_10_57_p8 endpoint_10_57_w8
def endpoint_10_57 : CertifiedEndpoint :=
  ⟨⟨10, 57, 3307⟩, 238265204536306487, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_57_flag endpoint_10_57_sources 9 238265204536306487 238265204536306487 rfl endpoint_10_57_base endpoint_10_57_p9) (by decide)⟩
private def endpoint_10_58_flag : Flag := ⟨10, 58, 3270⟩
private def endpoint_10_58_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_58_base : receiptBase endpoint_10_58_flag endpoint_10_58_sources = some 239220454459235473 := by decide +kernel
private theorem endpoint_10_58_w0 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 2 239220454459235473 = some 239220454459235473 := by decide +kernel
private theorem endpoint_10_58_w2 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 2 2 239220454459235473 = some 239220454459235473 := by decide +kernel
private theorem endpoint_10_58_p4 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 4 239220454459235473 = some 239220454459235473 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 2 2 239220454459235473 239220454459235473 239220454459235473 endpoint_10_58_w0 endpoint_10_58_w2
private theorem endpoint_10_58_w4 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 4 2 239220454459235473 = some 239220454459235473 := by decide +kernel
private theorem endpoint_10_58_p6 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 6 239220454459235473 = some 239220454459235473 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 4 2 239220454459235473 239220454459235473 239220454459235473 endpoint_10_58_p4 endpoint_10_58_w4
private theorem endpoint_10_58_w6 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 6 2 239220454459235473 = some 239220454459235473 := by decide +kernel
private theorem endpoint_10_58_p8 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 8 239220454459235473 = some 239220454459235473 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 6 2 239220454459235473 239220454459235473 239220454459235473 endpoint_10_58_p6 endpoint_10_58_w6
private theorem endpoint_10_58_w8 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 8 1 239220454459235473 = some 239220454459235473 := by decide +kernel
private theorem endpoint_10_58_p9 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 9 239220454459235473 = some 239220454459235473 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 8 1 239220454459235473 239220454459235473 239220454459235473 endpoint_10_58_p8 endpoint_10_58_w8
def endpoint_10_58 : CertifiedEndpoint :=
  ⟨⟨10, 58, 3270⟩, 239220454459235473, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_58_flag endpoint_10_58_sources 9 239220454459235473 239220454459235473 rfl endpoint_10_58_base endpoint_10_58_p9) (by decide)⟩
private def endpoint_10_59_flag : Flag := ⟨10, 59, 3232⟩
private def endpoint_10_59_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_59_base : receiptBase endpoint_10_59_flag endpoint_10_59_sources = some 240020735068412934 := by decide +kernel
private theorem endpoint_10_59_w0 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 2 240020735068412934 = some 240020735068412934 := by decide +kernel
private theorem endpoint_10_59_w2 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 2 2 240020735068412934 = some 240020735068412934 := by decide +kernel
private theorem endpoint_10_59_p4 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 4 240020735068412934 = some 240020735068412934 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 2 2 240020735068412934 240020735068412934 240020735068412934 endpoint_10_59_w0 endpoint_10_59_w2
private theorem endpoint_10_59_w4 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 4 2 240020735068412934 = some 240020735068412934 := by decide +kernel
private theorem endpoint_10_59_p6 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 6 240020735068412934 = some 240020735068412934 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 4 2 240020735068412934 240020735068412934 240020735068412934 endpoint_10_59_p4 endpoint_10_59_w4
private theorem endpoint_10_59_w6 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 6 2 240020735068412934 = some 240020735068412934 := by decide +kernel
private theorem endpoint_10_59_p8 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 8 240020735068412934 = some 240020735068412934 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 6 2 240020735068412934 240020735068412934 240020735068412934 endpoint_10_59_p6 endpoint_10_59_w6
private theorem endpoint_10_59_w8 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 8 1 240020735068412934 = some 240020735068412934 := by decide +kernel
private theorem endpoint_10_59_p9 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 9 240020735068412934 = some 240020735068412934 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 8 1 240020735068412934 240020735068412934 240020735068412934 endpoint_10_59_p8 endpoint_10_59_w8
def endpoint_10_59 : CertifiedEndpoint :=
  ⟨⟨10, 59, 3232⟩, 240020735068412934, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_59_flag endpoint_10_59_sources 9 240020735068412934 240020735068412934 rfl endpoint_10_59_base endpoint_10_59_p9) (by decide)⟩
private def endpoint_10_60_flag : Flag := ⟨10, 60, 3193⟩
private def endpoint_10_60_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_60_base : receiptBase endpoint_10_60_flag endpoint_10_60_sources = some 240662781705407205 := by decide +kernel
private theorem endpoint_10_60_w0 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 2 240662781705407205 = some 240662781705407205 := by decide +kernel
private theorem endpoint_10_60_w2 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 2 2 240662781705407205 = some 240662781705407205 := by decide +kernel
private theorem endpoint_10_60_p4 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 4 240662781705407205 = some 240662781705407205 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 2 2 240662781705407205 240662781705407205 240662781705407205 endpoint_10_60_w0 endpoint_10_60_w2
private theorem endpoint_10_60_w4 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 4 2 240662781705407205 = some 240662781705407205 := by decide +kernel
private theorem endpoint_10_60_p6 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 6 240662781705407205 = some 240662781705407205 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 4 2 240662781705407205 240662781705407205 240662781705407205 endpoint_10_60_p4 endpoint_10_60_w4
private theorem endpoint_10_60_w6 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 6 2 240662781705407205 = some 240662781705407205 := by decide +kernel
private theorem endpoint_10_60_p8 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 8 240662781705407205 = some 240662781705407205 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 6 2 240662781705407205 240662781705407205 240662781705407205 endpoint_10_60_p6 endpoint_10_60_w6
private theorem endpoint_10_60_w8 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 8 1 240662781705407205 = some 240662781705407205 := by decide +kernel
private theorem endpoint_10_60_p9 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 9 240662781705407205 = some 240662781705407205 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 8 1 240662781705407205 240662781705407205 240662781705407205 endpoint_10_60_p8 endpoint_10_60_w8
def endpoint_10_60 : CertifiedEndpoint :=
  ⟨⟨10, 60, 3193⟩, 240662781705407205, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_60_flag endpoint_10_60_sources 9 240662781705407205 240662781705407205 rfl endpoint_10_60_base endpoint_10_60_p9) (by decide)⟩
private def endpoint_10_61_flag : Flag := ⟨10, 61, 3152⟩
private def endpoint_10_61_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_61_base : receiptBase endpoint_10_61_flag endpoint_10_61_sources = some 241067800419872294 := by decide +kernel
private theorem endpoint_10_61_w0 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 2 241067800419872294 = some 241067800419872294 := by decide +kernel
private theorem endpoint_10_61_w2 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 2 2 241067800419872294 = some 241067800419872294 := by decide +kernel
private theorem endpoint_10_61_p4 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 4 241067800419872294 = some 241067800419872294 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 2 2 241067800419872294 241067800419872294 241067800419872294 endpoint_10_61_w0 endpoint_10_61_w2
private theorem endpoint_10_61_w4 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 4 2 241067800419872294 = some 241067800419872294 := by decide +kernel
private theorem endpoint_10_61_p6 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 6 241067800419872294 = some 241067800419872294 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 4 2 241067800419872294 241067800419872294 241067800419872294 endpoint_10_61_p4 endpoint_10_61_w4
private theorem endpoint_10_61_w6 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 6 2 241067800419872294 = some 241067800419872294 := by decide +kernel
private theorem endpoint_10_61_p8 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 8 241067800419872294 = some 241067800419872294 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 6 2 241067800419872294 241067800419872294 241067800419872294 endpoint_10_61_p6 endpoint_10_61_w6
private theorem endpoint_10_61_w8 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 8 1 241067800419872294 = some 241067800419872294 := by decide +kernel
private theorem endpoint_10_61_p9 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 9 241067800419872294 = some 241067800419872294 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 8 1 241067800419872294 241067800419872294 241067800419872294 endpoint_10_61_p8 endpoint_10_61_w8
def endpoint_10_61 : CertifiedEndpoint :=
  ⟨⟨10, 61, 3152⟩, 241067800419872294, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_61_flag endpoint_10_61_sources 9 241067800419872294 241067800419872294 rfl endpoint_10_61_base endpoint_10_61_p9) (by decide)⟩
private def endpoint_10_62_flag : Flag := ⟨10, 62, 3110⟩
private def endpoint_10_62_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_10_62_base : receiptBase endpoint_10_62_flag endpoint_10_62_sources = some 242542928792549935 := by decide +kernel
private theorem endpoint_10_62_w0 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 2 242542928792549935 = some 242542928792549935 := by decide +kernel
private theorem endpoint_10_62_w2 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 2 2 242542928792549935 = some 242542928792549935 := by decide +kernel
private theorem endpoint_10_62_p4 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 4 242542928792549935 = some 242542928792549935 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 2 2 242542928792549935 242542928792549935 242542928792549935 endpoint_10_62_w0 endpoint_10_62_w2
private theorem endpoint_10_62_w4 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 4 2 242542928792549935 = some 242542928792549935 := by decide +kernel
private theorem endpoint_10_62_p6 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 6 242542928792549935 = some 242542928792549935 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 4 2 242542928792549935 242542928792549935 242542928792549935 endpoint_10_62_p4 endpoint_10_62_w4
private theorem endpoint_10_62_w6 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 6 2 242542928792549935 = some 242542928792549935 := by decide +kernel
private theorem endpoint_10_62_p8 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 8 242542928792549935 = some 242542928792549935 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 6 2 242542928792549935 242542928792549935 242542928792549935 endpoint_10_62_p6 endpoint_10_62_w6
private theorem endpoint_10_62_w8 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 8 1 242542928792549935 = some 242542928792549935 := by decide +kernel
private theorem endpoint_10_62_p9 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 9 242542928792549935 = some 242542928792549935 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 8 1 242542928792549935 242542928792549935 242542928792549935 endpoint_10_62_p8 endpoint_10_62_w8
def endpoint_10_62 : CertifiedEndpoint :=
  ⟨⟨10, 62, 3110⟩, 242542928792549935, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_10_62_flag endpoint_10_62_sources 9 242542928792549935 242542928792549935 rfl endpoint_10_62_base endpoint_10_62_p9) (by decide)⟩
private def endpoint_10_63_flag : Flag := ⟨10, 63, 3066⟩
private def endpoint_10_63_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_10_63_base : receiptBase endpoint_10_63_flag endpoint_10_63_sources = some 242535945797268811 := by decide +kernel
private theorem endpoint_10_63_w0 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 2 242535945797268811 = some 242535945797268811 := by decide +kernel
private theorem endpoint_10_63_w2 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 2 2 242535945797268811 = some 242535945797268811 := by decide +kernel
private theorem endpoint_10_63_p4 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 4 242535945797268811 = some 242535945797268811 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 2 2 242535945797268811 242535945797268811 242535945797268811 endpoint_10_63_w0 endpoint_10_63_w2
private theorem endpoint_10_63_w4 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 4 2 242535945797268811 = some 242535945797268811 := by decide +kernel
private theorem endpoint_10_63_p6 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 6 242535945797268811 = some 242535945797268811 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 4 2 242535945797268811 242535945797268811 242535945797268811 endpoint_10_63_p4 endpoint_10_63_w4
private theorem endpoint_10_63_w6 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 6 2 242535945797268811 = some 242535945797268811 := by decide +kernel
private theorem endpoint_10_63_p8 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 8 242535945797268811 = some 242535945797268811 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 6 2 242535945797268811 242535945797268811 242535945797268811 endpoint_10_63_p6 endpoint_10_63_w6
private theorem endpoint_10_63_w8 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 8 1 242535945797268811 = some 242535945797268811 := by decide +kernel
private theorem endpoint_10_63_p9 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 9 242535945797268811 = some 242535945797268811 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 8 1 242535945797268811 242535945797268811 242535945797268811 endpoint_10_63_p8 endpoint_10_63_w8
def endpoint_10_63 : CertifiedEndpoint :=
  ⟨⟨10, 63, 3066⟩, 242535945797268811, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_10_63_flag endpoint_10_63_sources 9 242535945797268811 242535945797268811 rfl endpoint_10_63_base endpoint_10_63_p9) (by decide)⟩
private def endpoint_10_64_flag : Flag := ⟨10, 64, 3020⟩
private def endpoint_10_64_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_10_64_base : receiptBase endpoint_10_64_flag endpoint_10_64_sources = some 243571285685286903 := by decide +kernel
private theorem endpoint_10_64_w0 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 2 243571285685286903 = some 243571285685286903 := by decide +kernel
private theorem endpoint_10_64_w2 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 2 2 243571285685286903 = some 243571285685286903 := by decide +kernel
private theorem endpoint_10_64_p4 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 4 243571285685286903 = some 243571285685286903 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 2 2 243571285685286903 243571285685286903 243571285685286903 endpoint_10_64_w0 endpoint_10_64_w2
private theorem endpoint_10_64_w4 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 4 2 243571285685286903 = some 243571285685286903 := by decide +kernel
private theorem endpoint_10_64_p6 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 6 243571285685286903 = some 243571285685286903 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 4 2 243571285685286903 243571285685286903 243571285685286903 endpoint_10_64_p4 endpoint_10_64_w4
private theorem endpoint_10_64_w6 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 6 2 243571285685286903 = some 243571285685286903 := by decide +kernel
private theorem endpoint_10_64_p8 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 8 243571285685286903 = some 243571285685286903 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 6 2 243571285685286903 243571285685286903 243571285685286903 endpoint_10_64_p6 endpoint_10_64_w6
private theorem endpoint_10_64_w8 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 8 1 243571285685286903 = some 243571285685286903 := by decide +kernel
private theorem endpoint_10_64_p9 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 9 243571285685286903 = some 243571285685286903 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 8 1 243571285685286903 243571285685286903 243571285685286903 endpoint_10_64_p8 endpoint_10_64_w8
def endpoint_10_64 : CertifiedEndpoint :=
  ⟨⟨10, 64, 3020⟩, 243571285685286903, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_10_64_flag endpoint_10_64_sources 9 243571285685286903 243571285685286903 rfl endpoint_10_64_base endpoint_10_64_p9) (by decide)⟩
private def endpoint_10_65_flag : Flag := ⟨10, 65, 2971⟩
private def endpoint_10_65_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_10_65_base : receiptBase endpoint_10_65_flag endpoint_10_65_sources = some 242964782782225097 := by decide +kernel
private theorem endpoint_10_65_w0 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 2 242964782782225097 = some 242964782782225097 := by decide +kernel
private theorem endpoint_10_65_w2 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 2 2 242964782782225097 = some 242964782782225097 := by decide +kernel
private theorem endpoint_10_65_p4 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 4 242964782782225097 = some 242964782782225097 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 2 2 242964782782225097 242964782782225097 242964782782225097 endpoint_10_65_w0 endpoint_10_65_w2
private theorem endpoint_10_65_w4 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 4 2 242964782782225097 = some 242964782782225097 := by decide +kernel
private theorem endpoint_10_65_p6 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 6 242964782782225097 = some 242964782782225097 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 4 2 242964782782225097 242964782782225097 242964782782225097 endpoint_10_65_p4 endpoint_10_65_w4
private theorem endpoint_10_65_w6 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 6 2 242964782782225097 = some 242964782782225097 := by decide +kernel
private theorem endpoint_10_65_p8 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 8 242964782782225097 = some 242964782782225097 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 6 2 242964782782225097 242964782782225097 242964782782225097 endpoint_10_65_p6 endpoint_10_65_w6
private theorem endpoint_10_65_w8 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 8 1 242964782782225097 = some 242964782782225097 := by decide +kernel
private theorem endpoint_10_65_p9 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 9 242964782782225097 = some 242964782782225097 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 8 1 242964782782225097 242964782782225097 242964782782225097 endpoint_10_65_p8 endpoint_10_65_w8
def endpoint_10_65 : CertifiedEndpoint :=
  ⟨⟨10, 65, 2971⟩, 242964782782225097, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_10_65_flag endpoint_10_65_sources 9 242964782782225097 242964782782225097 rfl endpoint_10_65_base endpoint_10_65_p9) (by decide)⟩
private def endpoint_10_66_flag : Flag := ⟨10, 66, 2921⟩
private def endpoint_10_66_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_10_66_base : receiptBase endpoint_10_66_flag endpoint_10_66_sources = some 243510898692859558 := by decide +kernel
private theorem endpoint_10_66_w0 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 2 243510898692859558 = some 243510898692859558 := by decide +kernel
private theorem endpoint_10_66_w2 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 2 2 243510898692859558 = some 243510898692859558 := by decide +kernel
private theorem endpoint_10_66_p4 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 4 243510898692859558 = some 243510898692859558 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 2 2 243510898692859558 243510898692859558 243510898692859558 endpoint_10_66_w0 endpoint_10_66_w2
private theorem endpoint_10_66_w4 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 4 2 243510898692859558 = some 243510898692859558 := by decide +kernel
private theorem endpoint_10_66_p6 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 6 243510898692859558 = some 243510898692859558 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 4 2 243510898692859558 243510898692859558 243510898692859558 endpoint_10_66_p4 endpoint_10_66_w4
private theorem endpoint_10_66_w6 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 6 2 243510898692859558 = some 243510898692859558 := by decide +kernel
private theorem endpoint_10_66_p8 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 8 243510898692859558 = some 243510898692859558 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 6 2 243510898692859558 243510898692859558 243510898692859558 endpoint_10_66_p6 endpoint_10_66_w6
private theorem endpoint_10_66_w8 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 8 1 243510898692859558 = some 243510898692859558 := by decide +kernel
private theorem endpoint_10_66_p9 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 9 243510898692859558 = some 243510898692859558 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 8 1 243510898692859558 243510898692859558 243510898692859558 endpoint_10_66_p8 endpoint_10_66_w8
def endpoint_10_66 : CertifiedEndpoint :=
  ⟨⟨10, 66, 2921⟩, 243510898692859558, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_10_66_flag endpoint_10_66_sources 9 243510898692859558 243510898692859558 rfl endpoint_10_66_base endpoint_10_66_p9) (by decide)⟩
private def endpoint_10_67_flag : Flag := ⟨10, 67, 2868⟩
private def endpoint_10_67_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_10_67_base : receiptBase endpoint_10_67_flag endpoint_10_67_sources = some 243727794769201481 := by decide +kernel
private theorem endpoint_10_67_w0 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 2 243727794769201481 = some 243727794769201481 := by decide +kernel
private theorem endpoint_10_67_w2 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 2 2 243727794769201481 = some 243727794769201481 := by decide +kernel
private theorem endpoint_10_67_p4 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 4 243727794769201481 = some 243727794769201481 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 2 2 243727794769201481 243727794769201481 243727794769201481 endpoint_10_67_w0 endpoint_10_67_w2
private theorem endpoint_10_67_w4 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 4 2 243727794769201481 = some 243727794769201481 := by decide +kernel
private theorem endpoint_10_67_p6 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 6 243727794769201481 = some 243727794769201481 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 4 2 243727794769201481 243727794769201481 243727794769201481 endpoint_10_67_p4 endpoint_10_67_w4
private theorem endpoint_10_67_w6 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 6 2 243727794769201481 = some 243727794769201481 := by decide +kernel
private theorem endpoint_10_67_p8 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 8 243727794769201481 = some 243727794769201481 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 6 2 243727794769201481 243727794769201481 243727794769201481 endpoint_10_67_p6 endpoint_10_67_w6
private theorem endpoint_10_67_w8 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 8 1 243727794769201481 = some 243727794769201481 := by decide +kernel
private theorem endpoint_10_67_p9 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 9 243727794769201481 = some 243727794769201481 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 8 1 243727794769201481 243727794769201481 243727794769201481 endpoint_10_67_p8 endpoint_10_67_w8
def endpoint_10_67 : CertifiedEndpoint :=
  ⟨⟨10, 67, 2868⟩, 243727794769201481, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_10_67_flag endpoint_10_67_sources 9 243727794769201481 243727794769201481 rfl endpoint_10_67_base endpoint_10_67_p9) (by decide)⟩
private def endpoint_10_68_flag : Flag := ⟨10, 68, 2812⟩
private def endpoint_10_68_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_68_base : receiptBase endpoint_10_68_flag endpoint_10_68_sources = some 243449931941165945 := by decide +kernel
private theorem endpoint_10_68_w0 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 2 243449931941165945 = some 243449931941165945 := by decide +kernel
private theorem endpoint_10_68_w2 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 2 2 243449931941165945 = some 243449931941165945 := by decide +kernel
private theorem endpoint_10_68_p4 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 4 243449931941165945 = some 243449931941165945 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 2 2 243449931941165945 243449931941165945 243449931941165945 endpoint_10_68_w0 endpoint_10_68_w2
private theorem endpoint_10_68_w4 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 4 2 243449931941165945 = some 243449931941165945 := by decide +kernel
private theorem endpoint_10_68_p6 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 6 243449931941165945 = some 243449931941165945 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 4 2 243449931941165945 243449931941165945 243449931941165945 endpoint_10_68_p4 endpoint_10_68_w4
private theorem endpoint_10_68_w6 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 6 2 243449931941165945 = some 243449931941165945 := by decide +kernel
private theorem endpoint_10_68_p8 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 8 243449931941165945 = some 243449931941165945 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 6 2 243449931941165945 243449931941165945 243449931941165945 endpoint_10_68_p6 endpoint_10_68_w6
private theorem endpoint_10_68_w8 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 8 1 243449931941165945 = some 243449931941165945 := by decide +kernel
private theorem endpoint_10_68_p9 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 9 243449931941165945 = some 243449931941165945 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 8 1 243449931941165945 243449931941165945 243449931941165945 endpoint_10_68_p8 endpoint_10_68_w8
def endpoint_10_68 : CertifiedEndpoint :=
  ⟨⟨10, 68, 2812⟩, 243449931941165945, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_68_flag endpoint_10_68_sources 9 243449931941165945 243449931941165945 rfl endpoint_10_68_base endpoint_10_68_p9) (by decide)⟩
private def endpoint_10_69_flag : Flag := ⟨10, 69, 2754⟩
private def endpoint_10_69_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_69_base : receiptBase endpoint_10_69_flag endpoint_10_69_sources = some 241600740505595932 := by decide +kernel
private theorem endpoint_10_69_w0 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 2 241600740505595932 = some 241600740505595932 := by decide +kernel
private theorem endpoint_10_69_w2 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 2 2 241600740505595932 = some 241600740505595932 := by decide +kernel
private theorem endpoint_10_69_p4 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 4 241600740505595932 = some 241600740505595932 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 2 2 241600740505595932 241600740505595932 241600740505595932 endpoint_10_69_w0 endpoint_10_69_w2
private theorem endpoint_10_69_w4 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 4 2 241600740505595932 = some 241600740505595932 := by decide +kernel
private theorem endpoint_10_69_p6 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 6 241600740505595932 = some 241600740505595932 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 4 2 241600740505595932 241600740505595932 241600740505595932 endpoint_10_69_p4 endpoint_10_69_w4
private theorem endpoint_10_69_w6 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 6 2 241600740505595932 = some 241600740505595932 := by decide +kernel
private theorem endpoint_10_69_p8 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 8 241600740505595932 = some 241600740505595932 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 6 2 241600740505595932 241600740505595932 241600740505595932 endpoint_10_69_p6 endpoint_10_69_w6
private theorem endpoint_10_69_w8 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 8 1 241600740505595932 = some 241600740505595932 := by decide +kernel
private theorem endpoint_10_69_p9 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 9 241600740505595932 = some 241600740505595932 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 8 1 241600740505595932 241600740505595932 241600740505595932 endpoint_10_69_p8 endpoint_10_69_w8
def endpoint_10_69 : CertifiedEndpoint :=
  ⟨⟨10, 69, 2754⟩, 241600740505595932, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_69_flag endpoint_10_69_sources 9 241600740505595932 241600740505595932 rfl endpoint_10_69_base endpoint_10_69_p9) (by decide)⟩
private def endpoint_10_70_flag : Flag := ⟨10, 70, 2693⟩
private def endpoint_10_70_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_70_base : receiptBase endpoint_10_70_flag endpoint_10_70_sources = some 239354941537870386 := by decide +kernel
private theorem endpoint_10_70_w0 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 2 239354941537870386 = some 239354941537870386 := by decide +kernel
private theorem endpoint_10_70_w2 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 2 2 239354941537870386 = some 239354941537870386 := by decide +kernel
private theorem endpoint_10_70_p4 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 4 239354941537870386 = some 239354941537870386 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 2 2 239354941537870386 239354941537870386 239354941537870386 endpoint_10_70_w0 endpoint_10_70_w2
private theorem endpoint_10_70_w4 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 4 2 239354941537870386 = some 239354941537870386 := by decide +kernel
private theorem endpoint_10_70_p6 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 6 239354941537870386 = some 239354941537870386 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 4 2 239354941537870386 239354941537870386 239354941537870386 endpoint_10_70_p4 endpoint_10_70_w4
private theorem endpoint_10_70_w6 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 6 2 239354941537870386 = some 239354941537870386 := by decide +kernel
private theorem endpoint_10_70_p8 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 8 239354941537870386 = some 239354941537870386 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 6 2 239354941537870386 239354941537870386 239354941537870386 endpoint_10_70_p6 endpoint_10_70_w6
private theorem endpoint_10_70_w8 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 8 1 239354941537870386 = some 239354941537870386 := by decide +kernel
private theorem endpoint_10_70_p9 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 9 239354941537870386 = some 239354941537870386 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 8 1 239354941537870386 239354941537870386 239354941537870386 endpoint_10_70_p8 endpoint_10_70_w8
def endpoint_10_70 : CertifiedEndpoint :=
  ⟨⟨10, 70, 2693⟩, 239354941537870386, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_70_flag endpoint_10_70_sources 9 239354941537870386 239354941537870386 rfl endpoint_10_70_base endpoint_10_70_p9) (by decide)⟩
private def endpoint_10_71_flag : Flag := ⟨10, 71, 2630⟩
private def endpoint_10_71_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_71_base : receiptBase endpoint_10_71_flag endpoint_10_71_sources = some 236791476204742196 := by decide +kernel
private theorem endpoint_10_71_w0 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 2 236791476204742196 = some 236791476204742196 := by decide +kernel
private theorem endpoint_10_71_w2 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 2 2 236791476204742196 = some 236791476204742196 := by decide +kernel
private theorem endpoint_10_71_p4 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 4 236791476204742196 = some 236791476204742196 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 2 2 236791476204742196 236791476204742196 236791476204742196 endpoint_10_71_w0 endpoint_10_71_w2
private theorem endpoint_10_71_w4 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 4 2 236791476204742196 = some 236791476204742196 := by decide +kernel
private theorem endpoint_10_71_p6 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 6 236791476204742196 = some 236791476204742196 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 4 2 236791476204742196 236791476204742196 236791476204742196 endpoint_10_71_p4 endpoint_10_71_w4
private theorem endpoint_10_71_w6 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 6 2 236791476204742196 = some 236791476204742196 := by decide +kernel
private theorem endpoint_10_71_p8 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 8 236791476204742196 = some 236791476204742196 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 6 2 236791476204742196 236791476204742196 236791476204742196 endpoint_10_71_p6 endpoint_10_71_w6
private theorem endpoint_10_71_w8 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 8 1 236791476204742196 = some 236791476204742196 := by decide +kernel
private theorem endpoint_10_71_p9 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 9 236791476204742196 = some 236791476204742196 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 8 1 236791476204742196 236791476204742196 236791476204742196 endpoint_10_71_p8 endpoint_10_71_w8
def endpoint_10_71 : CertifiedEndpoint :=
  ⟨⟨10, 71, 2630⟩, 236791476204742196, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_71_flag endpoint_10_71_sources 9 236791476204742196 236791476204742196 rfl endpoint_10_71_base endpoint_10_71_p9) (by decide)⟩
private def endpoint_10_72_flag : Flag := ⟨10, 72, 2564⟩
private def endpoint_10_72_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_10_72_base : receiptBase endpoint_10_72_flag endpoint_10_72_sources = some 238747605441626661 := by decide +kernel
private theorem endpoint_10_72_w0 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 2 238747605441626661 = some 238747605441626661 := by decide +kernel
private theorem endpoint_10_72_w2 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 2 2 238747605441626661 = some 238747605441626661 := by decide +kernel
private theorem endpoint_10_72_p4 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 4 238747605441626661 = some 238747605441626661 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 2 2 238747605441626661 238747605441626661 238747605441626661 endpoint_10_72_w0 endpoint_10_72_w2
private theorem endpoint_10_72_w4 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 4 2 238747605441626661 = some 238747605441626661 := by decide +kernel
private theorem endpoint_10_72_p6 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 6 238747605441626661 = some 238747605441626661 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 4 2 238747605441626661 238747605441626661 238747605441626661 endpoint_10_72_p4 endpoint_10_72_w4
private theorem endpoint_10_72_w6 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 6 2 238747605441626661 = some 238747605441626661 := by decide +kernel
private theorem endpoint_10_72_p8 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 8 238747605441626661 = some 238747605441626661 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 6 2 238747605441626661 238747605441626661 238747605441626661 endpoint_10_72_p6 endpoint_10_72_w6
private theorem endpoint_10_72_w8 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 8 1 238747605441626661 = some 238747605441626661 := by decide +kernel
private theorem endpoint_10_72_p9 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 9 238747605441626661 = some 238747605441626661 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 8 1 238747605441626661 238747605441626661 238747605441626661 endpoint_10_72_p8 endpoint_10_72_w8
def endpoint_10_72 : CertifiedEndpoint :=
  ⟨⟨10, 72, 2564⟩, 238747605441626661, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_10_72_flag endpoint_10_72_sources 9 238747605441626661 238747605441626661 rfl endpoint_10_72_base endpoint_10_72_p9) (by decide)⟩
private def endpoint_10_73_flag : Flag := ⟨10, 73, 2496⟩
private def endpoint_10_73_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_10_73_base : receiptBase endpoint_10_73_flag endpoint_10_73_sources = some 235405806376874157 := by decide +kernel
private theorem endpoint_10_73_w0 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 2 235405806376874157 = some 235405806376874157 := by decide +kernel
private theorem endpoint_10_73_w2 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 2 2 235405806376874157 = some 235405806376874157 := by decide +kernel
private theorem endpoint_10_73_p4 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 4 235405806376874157 = some 235405806376874157 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 2 2 235405806376874157 235405806376874157 235405806376874157 endpoint_10_73_w0 endpoint_10_73_w2
private theorem endpoint_10_73_w4 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 4 2 235405806376874157 = some 235405806376874157 := by decide +kernel
private theorem endpoint_10_73_p6 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 6 235405806376874157 = some 235405806376874157 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 4 2 235405806376874157 235405806376874157 235405806376874157 endpoint_10_73_p4 endpoint_10_73_w4
private theorem endpoint_10_73_w6 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 6 2 235405806376874157 = some 235405806376874157 := by decide +kernel
private theorem endpoint_10_73_p8 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 8 235405806376874157 = some 235405806376874157 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 6 2 235405806376874157 235405806376874157 235405806376874157 endpoint_10_73_p6 endpoint_10_73_w6
private theorem endpoint_10_73_w8 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 8 1 235405806376874157 = some 235405806376874157 := by decide +kernel
private theorem endpoint_10_73_p9 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 9 235405806376874157 = some 235405806376874157 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 8 1 235405806376874157 235405806376874157 235405806376874157 endpoint_10_73_p8 endpoint_10_73_w8
def endpoint_10_73 : CertifiedEndpoint :=
  ⟨⟨10, 73, 2496⟩, 235405806376874157, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_10_73_flag endpoint_10_73_sources 9 235405806376874157 235405806376874157 rfl endpoint_10_73_base endpoint_10_73_p9) (by decide)⟩
private def endpoint_10_74_flag : Flag := ⟨10, 74, 2425⟩
private def endpoint_10_74_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_10_74_base : receiptBase endpoint_10_74_flag endpoint_10_74_sources = some 231627685901630246 := by decide +kernel
private theorem endpoint_10_74_w0 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 2 231627685901630246 = some 231627685901630246 := by decide +kernel
private theorem endpoint_10_74_w2 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 2 2 231627685901630246 = some 231627685901630246 := by decide +kernel
private theorem endpoint_10_74_p4 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 4 231627685901630246 = some 231627685901630246 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 2 2 231627685901630246 231627685901630246 231627685901630246 endpoint_10_74_w0 endpoint_10_74_w2
private theorem endpoint_10_74_w4 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 4 2 231627685901630246 = some 231627685901630246 := by decide +kernel
private theorem endpoint_10_74_p6 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 6 231627685901630246 = some 231627685901630246 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 4 2 231627685901630246 231627685901630246 231627685901630246 endpoint_10_74_p4 endpoint_10_74_w4
private theorem endpoint_10_74_w6 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 6 2 231627685901630246 = some 231627685901630246 := by decide +kernel
private theorem endpoint_10_74_p8 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 8 231627685901630246 = some 231627685901630246 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 6 2 231627685901630246 231627685901630246 231627685901630246 endpoint_10_74_p6 endpoint_10_74_w6
private theorem endpoint_10_74_w8 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 8 1 231627685901630246 = some 231627685901630246 := by decide +kernel
private theorem endpoint_10_74_p9 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 9 231627685901630246 = some 231627685901630246 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 8 1 231627685901630246 231627685901630246 231627685901630246 endpoint_10_74_p8 endpoint_10_74_w8
def endpoint_10_74 : CertifiedEndpoint :=
  ⟨⟨10, 74, 2425⟩, 231627685901630246, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_10_74_flag endpoint_10_74_sources 9 231627685901630246 231627685901630246 rfl endpoint_10_74_base endpoint_10_74_p9) (by decide)⟩
private def endpoint_10_75_flag : Flag := ⟨10, 75, 2352⟩
private def endpoint_10_75_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_10_75_base : receiptBase endpoint_10_75_flag endpoint_10_75_sources = some 229410321399015847 := by decide +kernel
private theorem endpoint_10_75_w0 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 2 229410321399015847 = some 229410321399015847 := by decide +kernel
private theorem endpoint_10_75_w2 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 2 2 229410321399015847 = some 229410321399015847 := by decide +kernel
private theorem endpoint_10_75_p4 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 4 229410321399015847 = some 229410321399015847 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 2 2 229410321399015847 229410321399015847 229410321399015847 endpoint_10_75_w0 endpoint_10_75_w2
private theorem endpoint_10_75_w4 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 4 2 229410321399015847 = some 229410321399015847 := by decide +kernel
private theorem endpoint_10_75_p6 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 6 229410321399015847 = some 229410321399015847 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 4 2 229410321399015847 229410321399015847 229410321399015847 endpoint_10_75_p4 endpoint_10_75_w4
private theorem endpoint_10_75_w6 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 6 2 229410321399015847 = some 229410321399015847 := by decide +kernel
private theorem endpoint_10_75_p8 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 8 229410321399015847 = some 229410321399015847 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 6 2 229410321399015847 229410321399015847 229410321399015847 endpoint_10_75_p6 endpoint_10_75_w6
private theorem endpoint_10_75_w8 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 8 1 229410321399015847 = some 229410321399015847 := by decide +kernel
private theorem endpoint_10_75_p9 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 9 229410321399015847 = some 229410321399015847 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 8 1 229410321399015847 229410321399015847 229410321399015847 endpoint_10_75_p8 endpoint_10_75_w8
def endpoint_10_75 : CertifiedEndpoint :=
  ⟨⟨10, 75, 2352⟩, 229410321399015847, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_10_75_flag endpoint_10_75_sources 9 229410321399015847 229410321399015847 rfl endpoint_10_75_base endpoint_10_75_p9) (by decide)⟩
private def endpoint_10_76_flag : Flag := ⟨10, 76, 2276⟩
private def endpoint_10_76_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_10_76_base : receiptBase endpoint_10_76_flag endpoint_10_76_sources = some 224711818463388273 := by decide +kernel
private theorem endpoint_10_76_w0 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 2 224711818463388273 = some 224711818463388273 := by decide +kernel
private theorem endpoint_10_76_w2 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 2 2 224711818463388273 = some 224711818463388273 := by decide +kernel
private theorem endpoint_10_76_p4 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 4 224711818463388273 = some 224711818463388273 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 2 2 224711818463388273 224711818463388273 224711818463388273 endpoint_10_76_w0 endpoint_10_76_w2
private theorem endpoint_10_76_w4 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 4 2 224711818463388273 = some 224711818463388273 := by decide +kernel
private theorem endpoint_10_76_p6 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 6 224711818463388273 = some 224711818463388273 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 4 2 224711818463388273 224711818463388273 224711818463388273 endpoint_10_76_p4 endpoint_10_76_w4
private theorem endpoint_10_76_w6 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 6 2 224711818463388273 = some 224711818463388273 := by decide +kernel
private theorem endpoint_10_76_p8 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 8 224711818463388273 = some 224711818463388273 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 6 2 224711818463388273 224711818463388273 224711818463388273 endpoint_10_76_p6 endpoint_10_76_w6
private theorem endpoint_10_76_w8 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 8 1 224711818463388273 = some 224711818463388273 := by decide +kernel
private theorem endpoint_10_76_p9 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 9 224711818463388273 = some 224711818463388273 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 8 1 224711818463388273 224711818463388273 224711818463388273 endpoint_10_76_p8 endpoint_10_76_w8
def endpoint_10_76 : CertifiedEndpoint :=
  ⟨⟨10, 76, 2276⟩, 224711818463388273, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_10_76_flag endpoint_10_76_sources 9 224711818463388273 224711818463388273 rfl endpoint_10_76_base endpoint_10_76_p9) (by decide)⟩
private def endpoint_10_77_flag : Flag := ⟨10, 77, 2197⟩
private def endpoint_10_77_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_10_77_base : receiptBase endpoint_10_77_flag endpoint_10_77_sources = some 221535028782268254 := by decide +kernel
private theorem endpoint_10_77_w0 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 2 221535028782268254 = some 221535028782268254 := by decide +kernel
private theorem endpoint_10_77_w2 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 2 2 221535028782268254 = some 221535028782268254 := by decide +kernel
private theorem endpoint_10_77_p4 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 4 221535028782268254 = some 221535028782268254 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 2 2 221535028782268254 221535028782268254 221535028782268254 endpoint_10_77_w0 endpoint_10_77_w2
private theorem endpoint_10_77_w4 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 4 2 221535028782268254 = some 221535028782268254 := by decide +kernel
private theorem endpoint_10_77_p6 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 6 221535028782268254 = some 221535028782268254 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 4 2 221535028782268254 221535028782268254 221535028782268254 endpoint_10_77_p4 endpoint_10_77_w4
private theorem endpoint_10_77_w6 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 6 2 221535028782268254 = some 221535028782268254 := by decide +kernel
private theorem endpoint_10_77_p8 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 8 221535028782268254 = some 221535028782268254 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 6 2 221535028782268254 221535028782268254 221535028782268254 endpoint_10_77_p6 endpoint_10_77_w6
private theorem endpoint_10_77_w8 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 8 1 221535028782268254 = some 221535028782268254 := by decide +kernel
private theorem endpoint_10_77_p9 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 9 221535028782268254 = some 221535028782268254 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 8 1 221535028782268254 221535028782268254 221535028782268254 endpoint_10_77_p8 endpoint_10_77_w8
def endpoint_10_77 : CertifiedEndpoint :=
  ⟨⟨10, 77, 2197⟩, 221535028782268254, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_10_77_flag endpoint_10_77_sources 9 221535028782268254 221535028782268254 rfl endpoint_10_77_base endpoint_10_77_p9) (by decide)⟩
private def endpoint_10_78_flag : Flag := ⟨10, 78, 2116⟩
private def endpoint_10_78_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_10_78_base : receiptBase endpoint_10_78_flag endpoint_10_78_sources = some 218004196690186091 := by decide +kernel
private theorem endpoint_10_78_w0 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 2 218004196690186091 = some 218004196690186091 := by decide +kernel
private theorem endpoint_10_78_w2 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 2 2 218004196690186091 = some 218004196690186091 := by decide +kernel
private theorem endpoint_10_78_p4 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 4 218004196690186091 = some 218004196690186091 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 2 2 218004196690186091 218004196690186091 218004196690186091 endpoint_10_78_w0 endpoint_10_78_w2
private theorem endpoint_10_78_w4 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 4 2 218004196690186091 = some 218004196690186091 := by decide +kernel
private theorem endpoint_10_78_p6 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 6 218004196690186091 = some 218004196690186091 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 4 2 218004196690186091 218004196690186091 218004196690186091 endpoint_10_78_p4 endpoint_10_78_w4
private theorem endpoint_10_78_w6 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 6 2 218004196690186091 = some 218004196690186091 := by decide +kernel
private theorem endpoint_10_78_p8 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 8 218004196690186091 = some 218004196690186091 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 6 2 218004196690186091 218004196690186091 218004196690186091 endpoint_10_78_p6 endpoint_10_78_w6
private theorem endpoint_10_78_w8 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 8 1 218004196690186091 = some 218004196690186091 := by decide +kernel
private theorem endpoint_10_78_p9 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 9 218004196690186091 = some 218004196690186091 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 8 1 218004196690186091 218004196690186091 218004196690186091 endpoint_10_78_p8 endpoint_10_78_w8
def endpoint_10_78 : CertifiedEndpoint :=
  ⟨⟨10, 78, 2116⟩, 218004196690186091, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_10_78_flag endpoint_10_78_sources 9 218004196690186091 218004196690186091 rfl endpoint_10_78_base endpoint_10_78_p9) (by decide)⟩
private def endpoint_10_79_flag : Flag := ⟨10, 79, 2032⟩
private def endpoint_10_79_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_10_79_base : receiptBase endpoint_10_79_flag endpoint_10_79_sources = some 211809925097223833 := by decide +kernel
private theorem endpoint_10_79_w0 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 2 211809925097223833 = some 211809925097223833 := by decide +kernel
private theorem endpoint_10_79_w2 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 2 2 211809925097223833 = some 211809925097223833 := by decide +kernel
private theorem endpoint_10_79_p4 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 4 211809925097223833 = some 211809925097223833 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 2 2 211809925097223833 211809925097223833 211809925097223833 endpoint_10_79_w0 endpoint_10_79_w2
private theorem endpoint_10_79_w4 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 4 2 211809925097223833 = some 211809925097223833 := by decide +kernel
private theorem endpoint_10_79_p6 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 6 211809925097223833 = some 211809925097223833 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 4 2 211809925097223833 211809925097223833 211809925097223833 endpoint_10_79_p4 endpoint_10_79_w4
private theorem endpoint_10_79_w6 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 6 2 211809925097223833 = some 211809925097223833 := by decide +kernel
private theorem endpoint_10_79_p8 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 8 211809925097223833 = some 211809925097223833 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 6 2 211809925097223833 211809925097223833 211809925097223833 endpoint_10_79_p6 endpoint_10_79_w6
private theorem endpoint_10_79_w8 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 8 1 211809925097223833 = some 211809925097223833 := by decide +kernel
private theorem endpoint_10_79_p9 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 9 211809925097223833 = some 211809925097223833 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 8 1 211809925097223833 211809925097223833 211809925097223833 endpoint_10_79_p8 endpoint_10_79_w8
def endpoint_10_79 : CertifiedEndpoint :=
  ⟨⟨10, 79, 2032⟩, 211809925097223833, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_10_79_flag endpoint_10_79_sources 9 211809925097223833 211809925097223833 rfl endpoint_10_79_base endpoint_10_79_p9) (by decide)⟩
private def endpoint_10_80_flag : Flag := ⟨10, 80, 1945⟩
private def endpoint_10_80_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_10_80_base : receiptBase endpoint_10_80_flag endpoint_10_80_sources = some 205102195334251208 := by decide +kernel
private theorem endpoint_10_80_w0 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 2 205102195334251208 = some 205102195334251208 := by decide +kernel
private theorem endpoint_10_80_w2 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 2 2 205102195334251208 = some 205102195334251208 := by decide +kernel
private theorem endpoint_10_80_p4 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 4 205102195334251208 = some 205102195334251208 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 2 2 205102195334251208 205102195334251208 205102195334251208 endpoint_10_80_w0 endpoint_10_80_w2
private theorem endpoint_10_80_w4 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 4 2 205102195334251208 = some 205102195334251208 := by decide +kernel
private theorem endpoint_10_80_p6 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 6 205102195334251208 = some 205102195334251208 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 4 2 205102195334251208 205102195334251208 205102195334251208 endpoint_10_80_p4 endpoint_10_80_w4
private theorem endpoint_10_80_w6 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 6 2 205102195334251208 = some 205102195334251208 := by decide +kernel
private theorem endpoint_10_80_p8 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 8 205102195334251208 = some 205102195334251208 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 6 2 205102195334251208 205102195334251208 205102195334251208 endpoint_10_80_p6 endpoint_10_80_w6
private theorem endpoint_10_80_w8 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 8 1 205102195334251208 = some 205102195334251208 := by decide +kernel
private theorem endpoint_10_80_p9 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 9 205102195334251208 = some 205102195334251208 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 8 1 205102195334251208 205102195334251208 205102195334251208 endpoint_10_80_p8 endpoint_10_80_w8
def endpoint_10_80 : CertifiedEndpoint :=
  ⟨⟨10, 80, 1945⟩, 205102195334251208, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_10_80_flag endpoint_10_80_sources 9 205102195334251208 205102195334251208 rfl endpoint_10_80_base endpoint_10_80_p9) (by decide)⟩
private def endpoint_10_81_flag : Flag := ⟨10, 81, 1856⟩
private def endpoint_10_81_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_81_base : receiptBase endpoint_10_81_flag endpoint_10_81_sources = some 201961489167154546 := by decide +kernel
private theorem endpoint_10_81_w0 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 2 201961489167154546 = some 201961489167154546 := by decide +kernel
private theorem endpoint_10_81_w2 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 2 2 201961489167154546 = some 201961489167154546 := by decide +kernel
private theorem endpoint_10_81_p4 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 4 201961489167154546 = some 201961489167154546 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 2 2 201961489167154546 201961489167154546 201961489167154546 endpoint_10_81_w0 endpoint_10_81_w2
private theorem endpoint_10_81_w4 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 4 2 201961489167154546 = some 201961489167154546 := by decide +kernel
private theorem endpoint_10_81_p6 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 6 201961489167154546 = some 201961489167154546 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 4 2 201961489167154546 201961489167154546 201961489167154546 endpoint_10_81_p4 endpoint_10_81_w4
private theorem endpoint_10_81_w6 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 6 2 201961489167154546 = some 201961489167154546 := by decide +kernel
private theorem endpoint_10_81_p8 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 8 201961489167154546 = some 201961489167154546 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 6 2 201961489167154546 201961489167154546 201961489167154546 endpoint_10_81_p6 endpoint_10_81_w6
private theorem endpoint_10_81_w8 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 8 1 201961489167154546 = some 201961489167154546 := by decide +kernel
private theorem endpoint_10_81_p9 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 9 201961489167154546 = some 201961489167154546 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 8 1 201961489167154546 201961489167154546 201961489167154546 endpoint_10_81_p8 endpoint_10_81_w8
def endpoint_10_81 : CertifiedEndpoint :=
  ⟨⟨10, 81, 1856⟩, 201961489167154546, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_81_flag endpoint_10_81_sources 9 201961489167154546 201961489167154546 rfl endpoint_10_81_base endpoint_10_81_p9) (by decide)⟩
private def endpoint_10_82_flag : Flag := ⟨10, 82, 1765⟩
private def endpoint_10_82_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_82_base : receiptBase endpoint_10_82_flag endpoint_10_82_sources = some 194213649986424792 := by decide +kernel
private theorem endpoint_10_82_w0 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 2 194213649986424792 = some 194213649986424792 := by decide +kernel
private theorem endpoint_10_82_w2 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 2 2 194213649986424792 = some 194213649986424792 := by decide +kernel
private theorem endpoint_10_82_p4 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 4 194213649986424792 = some 194213649986424792 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 2 2 194213649986424792 194213649986424792 194213649986424792 endpoint_10_82_w0 endpoint_10_82_w2
private theorem endpoint_10_82_w4 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 4 2 194213649986424792 = some 194213649986424792 := by decide +kernel
private theorem endpoint_10_82_p6 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 6 194213649986424792 = some 194213649986424792 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 4 2 194213649986424792 194213649986424792 194213649986424792 endpoint_10_82_p4 endpoint_10_82_w4
private theorem endpoint_10_82_w6 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 6 2 194213649986424792 = some 194213649986424792 := by decide +kernel
private theorem endpoint_10_82_p8 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 8 194213649986424792 = some 194213649986424792 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 6 2 194213649986424792 194213649986424792 194213649986424792 endpoint_10_82_p6 endpoint_10_82_w6
private theorem endpoint_10_82_w8 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 8 1 194213649986424792 = some 194213649986424792 := by decide +kernel
private theorem endpoint_10_82_p9 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 9 194213649986424792 = some 194213649986424792 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 8 1 194213649986424792 194213649986424792 194213649986424792 endpoint_10_82_p8 endpoint_10_82_w8
def endpoint_10_82 : CertifiedEndpoint :=
  ⟨⟨10, 82, 1765⟩, 194213649986424792, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_82_flag endpoint_10_82_sources 9 194213649986424792 194213649986424792 rfl endpoint_10_82_base endpoint_10_82_p9) (by decide)⟩
private def endpoint_10_83_flag : Flag := ⟨10, 83, 1670⟩
private def endpoint_10_83_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_83_base : receiptBase endpoint_10_83_flag endpoint_10_83_sources = some 185800582273722528 := by decide +kernel
private theorem endpoint_10_83_w0 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 0 2 185800582273722528 = some 185800582273722528 := by decide +kernel
private theorem endpoint_10_83_w2 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 2 2 185800582273722528 = some 185800582273722528 := by decide +kernel
private theorem endpoint_10_83_p4 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 0 4 185800582273722528 = some 185800582273722528 :=
  join_receipt_window endpoint_10_83_flag endpoint_10_83_sources 0 2 2 185800582273722528 185800582273722528 185800582273722528 endpoint_10_83_w0 endpoint_10_83_w2
private theorem endpoint_10_83_w4 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 4 2 185800582273722528 = some 185800582273722528 := by decide +kernel
private theorem endpoint_10_83_p6 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 0 6 185800582273722528 = some 185800582273722528 :=
  join_receipt_window endpoint_10_83_flag endpoint_10_83_sources 0 4 2 185800582273722528 185800582273722528 185800582273722528 endpoint_10_83_p4 endpoint_10_83_w4
private theorem endpoint_10_83_w6 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 6 2 185800582273722528 = some 185800582273722528 := by decide +kernel
private theorem endpoint_10_83_p8 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 0 8 185800582273722528 = some 185800582273722528 :=
  join_receipt_window endpoint_10_83_flag endpoint_10_83_sources 0 6 2 185800582273722528 185800582273722528 185800582273722528 endpoint_10_83_p6 endpoint_10_83_w6
private theorem endpoint_10_83_w8 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 8 1 185800582273722528 = some 185800582273722528 := by decide +kernel
private theorem endpoint_10_83_p9 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 0 9 185800582273722528 = some 185800582273722528 :=
  join_receipt_window endpoint_10_83_flag endpoint_10_83_sources 0 8 1 185800582273722528 185800582273722528 185800582273722528 endpoint_10_83_p8 endpoint_10_83_w8
def endpoint_10_83 : CertifiedEndpoint :=
  ⟨⟨10, 83, 1670⟩, 185800582273722528, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_83_flag endpoint_10_83_sources 9 185800582273722528 185800582273722528 rfl endpoint_10_83_base endpoint_10_83_p9) (by decide)⟩
private def endpoint_10_84_flag : Flag := ⟨10, 84, 1573⟩
private def endpoint_10_84_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_84_base : receiptBase endpoint_10_84_flag endpoint_10_84_sources = some 176931661995087932 := by decide +kernel
private theorem endpoint_10_84_w0 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 0 2 176931661995087932 = some 176931661995087932 := by decide +kernel
private theorem endpoint_10_84_w2 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 2 2 176931661995087932 = some 176931661995087932 := by decide +kernel
private theorem endpoint_10_84_p4 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 0 4 176931661995087932 = some 176931661995087932 :=
  join_receipt_window endpoint_10_84_flag endpoint_10_84_sources 0 2 2 176931661995087932 176931661995087932 176931661995087932 endpoint_10_84_w0 endpoint_10_84_w2
private theorem endpoint_10_84_w4 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 4 2 176931661995087932 = some 176931661995087932 := by decide +kernel
private theorem endpoint_10_84_p6 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 0 6 176931661995087932 = some 176931661995087932 :=
  join_receipt_window endpoint_10_84_flag endpoint_10_84_sources 0 4 2 176931661995087932 176931661995087932 176931661995087932 endpoint_10_84_p4 endpoint_10_84_w4
private theorem endpoint_10_84_w6 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 6 2 176931661995087932 = some 176931661995087932 := by decide +kernel
private theorem endpoint_10_84_p8 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 0 8 176931661995087932 = some 176931661995087932 :=
  join_receipt_window endpoint_10_84_flag endpoint_10_84_sources 0 6 2 176931661995087932 176931661995087932 176931661995087932 endpoint_10_84_p6 endpoint_10_84_w6
private theorem endpoint_10_84_w8 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 8 1 176931661995087932 = some 176931661995087932 := by decide +kernel
private theorem endpoint_10_84_p9 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 0 9 176931661995087932 = some 176931661995087932 :=
  join_receipt_window endpoint_10_84_flag endpoint_10_84_sources 0 8 1 176931661995087932 176931661995087932 176931661995087932 endpoint_10_84_p8 endpoint_10_84_w8
def endpoint_10_84 : CertifiedEndpoint :=
  ⟨⟨10, 84, 1573⟩, 176931661995087932, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_84_flag endpoint_10_84_sources 9 176931661995087932 176931661995087932 rfl endpoint_10_84_base endpoint_10_84_p9) (by decide)⟩
private def endpoint_10_85_flag : Flag := ⟨10, 85, 1474⟩
private def endpoint_10_85_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_85_base : receiptBase endpoint_10_85_flag endpoint_10_85_sources = some 167599604127864095 := by decide +kernel
private theorem endpoint_10_85_w0 : receiptWindow endpoint_10_85_flag endpoint_10_85_sources 0 2 167599604127864095 = some 167599604127864095 := by decide +kernel
private theorem endpoint_10_85_w2 : receiptWindow endpoint_10_85_flag endpoint_10_85_sources 2 2 167599604127864095 = some 167599604127864095 := by decide +kernel
private theorem endpoint_10_85_p4 : receiptWindow endpoint_10_85_flag endpoint_10_85_sources 0 4 167599604127864095 = some 167599604127864095 :=
  join_receipt_window endpoint_10_85_flag endpoint_10_85_sources 0 2 2 167599604127864095 167599604127864095 167599604127864095 endpoint_10_85_w0 endpoint_10_85_w2
private theorem endpoint_10_85_w4 : receiptWindow endpoint_10_85_flag endpoint_10_85_sources 4 2 167599604127864095 = some 167599604127864095 := by decide +kernel
private theorem endpoint_10_85_p6 : receiptWindow endpoint_10_85_flag endpoint_10_85_sources 0 6 167599604127864095 = some 167599604127864095 :=
  join_receipt_window endpoint_10_85_flag endpoint_10_85_sources 0 4 2 167599604127864095 167599604127864095 167599604127864095 endpoint_10_85_p4 endpoint_10_85_w4
private theorem endpoint_10_85_w6 : receiptWindow endpoint_10_85_flag endpoint_10_85_sources 6 2 167599604127864095 = some 167599604127864095 := by decide +kernel
private theorem endpoint_10_85_p8 : receiptWindow endpoint_10_85_flag endpoint_10_85_sources 0 8 167599604127864095 = some 167599604127864095 :=
  join_receipt_window endpoint_10_85_flag endpoint_10_85_sources 0 6 2 167599604127864095 167599604127864095 167599604127864095 endpoint_10_85_p6 endpoint_10_85_w6
private theorem endpoint_10_85_w8 : receiptWindow endpoint_10_85_flag endpoint_10_85_sources 8 1 167599604127864095 = some 167599604127864095 := by decide +kernel
private theorem endpoint_10_85_p9 : receiptWindow endpoint_10_85_flag endpoint_10_85_sources 0 9 167599604127864095 = some 167599604127864095 :=
  join_receipt_window endpoint_10_85_flag endpoint_10_85_sources 0 8 1 167599604127864095 167599604127864095 167599604127864095 endpoint_10_85_p8 endpoint_10_85_w8
def endpoint_10_85 : CertifiedEndpoint :=
  ⟨⟨10, 85, 1474⟩, 167599604127864095, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_85_flag endpoint_10_85_sources 9 167599604127864095 167599604127864095 rfl endpoint_10_85_base endpoint_10_85_p9) (by decide)⟩
private def endpoint_10_86_flag : Flag := ⟨10, 86, 1371⟩
private def endpoint_10_86_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_86_base : receiptBase endpoint_10_86_flag endpoint_10_86_sources = some 157568320956268829 := by decide +kernel
private theorem endpoint_10_86_w0 : receiptWindow endpoint_10_86_flag endpoint_10_86_sources 0 2 157568320956268829 = some 157568320956268829 := by decide +kernel
private theorem endpoint_10_86_w2 : receiptWindow endpoint_10_86_flag endpoint_10_86_sources 2 2 157568320956268829 = some 157568320956268829 := by decide +kernel
private theorem endpoint_10_86_p4 : receiptWindow endpoint_10_86_flag endpoint_10_86_sources 0 4 157568320956268829 = some 157568320956268829 :=
  join_receipt_window endpoint_10_86_flag endpoint_10_86_sources 0 2 2 157568320956268829 157568320956268829 157568320956268829 endpoint_10_86_w0 endpoint_10_86_w2
private theorem endpoint_10_86_w4 : receiptWindow endpoint_10_86_flag endpoint_10_86_sources 4 2 157568320956268829 = some 157568320956268829 := by decide +kernel
private theorem endpoint_10_86_p6 : receiptWindow endpoint_10_86_flag endpoint_10_86_sources 0 6 157568320956268829 = some 157568320956268829 :=
  join_receipt_window endpoint_10_86_flag endpoint_10_86_sources 0 4 2 157568320956268829 157568320956268829 157568320956268829 endpoint_10_86_p4 endpoint_10_86_w4
private theorem endpoint_10_86_w6 : receiptWindow endpoint_10_86_flag endpoint_10_86_sources 6 2 157568320956268829 = some 157568320956268829 := by decide +kernel
private theorem endpoint_10_86_p8 : receiptWindow endpoint_10_86_flag endpoint_10_86_sources 0 8 157568320956268829 = some 157568320956268829 :=
  join_receipt_window endpoint_10_86_flag endpoint_10_86_sources 0 6 2 157568320956268829 157568320956268829 157568320956268829 endpoint_10_86_p6 endpoint_10_86_w6
private theorem endpoint_10_86_w8 : receiptWindow endpoint_10_86_flag endpoint_10_86_sources 8 1 157568320956268829 = some 157568320956268829 := by decide +kernel
private theorem endpoint_10_86_p9 : receiptWindow endpoint_10_86_flag endpoint_10_86_sources 0 9 157568320956268829 = some 157568320956268829 :=
  join_receipt_window endpoint_10_86_flag endpoint_10_86_sources 0 8 1 157568320956268829 157568320956268829 157568320956268829 endpoint_10_86_p8 endpoint_10_86_w8
def endpoint_10_86 : CertifiedEndpoint :=
  ⟨⟨10, 86, 1371⟩, 157568320956268829, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_86_flag endpoint_10_86_sources 9 157568320956268829 157568320956268829 rfl endpoint_10_86_base endpoint_10_86_p9) (by decide)⟩
def endpoint_10_87 : CertifiedEndpoint :=
  ⟨⟨10, 87, 1266⟩, 244248017618270251, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_88 : CertifiedEndpoint :=
  ⟨⟨10, 88, 1159⟩, 225455162122295509, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_89 : CertifiedEndpoint :=
  ⟨⟨10, 89, 1049⟩, 205518648272952594, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_90 : CertifiedEndpoint :=
  ⟨⟨10, 90, 936⟩, 184416365022984196, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_91 : CertifiedEndpoint :=
  ⟨⟨10, 91, 820⟩, 162126201325133005, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_92 : CertifiedEndpoint :=
  ⟨⟨10, 92, 702⟩, 138838566481967922, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_93 : CertifiedEndpoint :=
  ⟨⟨10, 93, 581⟩, 114323742662462606, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_94 : CertifiedEndpoint :=
  ⟨⟨10, 94, 458⟩, 88777052735243138, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_95 : CertifiedEndpoint :=
  ⟨⟨10, 95, 332⟩, 61963865303225997, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_96 : CertifiedEndpoint :=
  ⟨⟨10, 96, 203⟩, 33862069319153873, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_11 : CertifiedEndpoint :=
  ⟨⟨11, 11, 4352⟩, 74885440101529669, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_12 : CertifiedEndpoint :=
  ⟨⟨11, 12, 4334⟩, 78398271000074458, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_13 : CertifiedEndpoint :=
  ⟨⟨11, 13, 4315⟩, 81860239579732580, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_14 : CertifiedEndpoint :=
  ⟨⟨11, 14, 4295⟩, 93102116558810243, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_15 : CertifiedEndpoint :=
  ⟨⟨11, 15, 4276⟩, 104257138563108211, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_16 : CertifiedEndpoint :=
  ⟨⟨11, 16, 4257⟩, 115306295560450341, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_17 : CertifiedEndpoint :=
  ⟨⟨11, 17, 4237⟩, 126219719569229122, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_18 : CertifiedEndpoint :=
  ⟨⟨11, 18, 4217⟩, 137021849596336381, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_19 : CertifiedEndpoint :=
  ⟨⟨11, 19, 4197⟩, 147712685641772118, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_20 : CertifiedEndpoint :=
  ⟨⟨11, 20, 4177⟩, 158292227705536333, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_21 : CertifiedEndpoint :=
  ⟨⟨11, 21, 4156⟩, 168719749856590147, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_22 : CertifiedEndpoint :=
  ⟨⟨11, 22, 4136⟩, 179073989469653476, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_23 : CertifiedEndpoint :=
  ⟨⟨11, 23, 4115⟩, 189270780195290720, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_24 : CertifiedEndpoint :=
  ⟨⟨11, 24, 4094⟩, 199350847964540758, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_25 : CertifiedEndpoint :=
  ⟨⟨11, 25, 4072⟩, 209262608896933343, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_26 : CertifiedEndpoint :=
  ⟨⟨11, 26, 4051⟩, 219106516266051127, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_27 : CertifiedEndpoint :=
  ⟨⟨11, 27, 4029⟩, 228776687823595774, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_28 : CertifiedEndpoint :=
  ⟨⟨11, 28, 4007⟩, 238324707450037531, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_29 : CertifiedEndpoint :=
  ⟨⟨11, 29, 3984⟩, 247688133315474783, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_30 : CertifiedEndpoint :=
  ⟨⟨11, 30, 3962⟩, 256989134592352918, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_11_31_flag : Flag := ⟨11, 31, 3939⟩
private def endpoint_11_31_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_31_base : receiptBase endpoint_11_31_flag endpoint_11_31_sources = some 177054780258867794 := by decide +kernel
private theorem endpoint_11_31_w0 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 2 177054780258867794 = some 177054780258867794 := by decide +kernel
private theorem endpoint_11_31_w2 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 2 2 177054780258867794 = some 177054780258867794 := by decide +kernel
private theorem endpoint_11_31_p4 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 4 177054780258867794 = some 177054780258867794 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 2 2 177054780258867794 177054780258867794 177054780258867794 endpoint_11_31_w0 endpoint_11_31_w2
private theorem endpoint_11_31_w4 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 4 2 177054780258867794 = some 177054780258867794 := by decide +kernel
private theorem endpoint_11_31_p6 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 6 177054780258867794 = some 177054780258867794 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 4 2 177054780258867794 177054780258867794 177054780258867794 endpoint_11_31_p4 endpoint_11_31_w4
private theorem endpoint_11_31_w6 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 6 2 177054780258867794 = some 177054780258867794 := by decide +kernel
private theorem endpoint_11_31_p8 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 8 177054780258867794 = some 177054780258867794 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 6 2 177054780258867794 177054780258867794 177054780258867794 endpoint_11_31_p6 endpoint_11_31_w6
private theorem endpoint_11_31_w8 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 8 2 177054780258867794 = some 177054780258867794 := by decide +kernel
private theorem endpoint_11_31_p10 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 10 177054780258867794 = some 177054780258867794 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 8 2 177054780258867794 177054780258867794 177054780258867794 endpoint_11_31_p8 endpoint_11_31_w8
def endpoint_11_31 : CertifiedEndpoint :=
  ⟨⟨11, 31, 3939⟩, 177054780258867794, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_31_flag endpoint_11_31_sources 10 177054780258867794 177054780258867794 rfl endpoint_11_31_base endpoint_11_31_p10) (by decide)⟩
private def endpoint_11_32_flag : Flag := ⟨11, 32, 3916⟩
private def endpoint_11_32_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_32_base : receiptBase endpoint_11_32_flag endpoint_11_32_sources = some 180637520629604287 := by decide +kernel
private theorem endpoint_11_32_w0 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 2 180637520629604287 = some 180637520629604287 := by decide +kernel
private theorem endpoint_11_32_w2 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 2 2 180637520629604287 = some 180637520629604287 := by decide +kernel
private theorem endpoint_11_32_p4 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 4 180637520629604287 = some 180637520629604287 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 2 2 180637520629604287 180637520629604287 180637520629604287 endpoint_11_32_w0 endpoint_11_32_w2
private theorem endpoint_11_32_w4 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 4 2 180637520629604287 = some 180637520629604287 := by decide +kernel
private theorem endpoint_11_32_p6 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 6 180637520629604287 = some 180637520629604287 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 4 2 180637520629604287 180637520629604287 180637520629604287 endpoint_11_32_p4 endpoint_11_32_w4
private theorem endpoint_11_32_w6 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 6 2 180637520629604287 = some 180637520629604287 := by decide +kernel
private theorem endpoint_11_32_p8 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 8 180637520629604287 = some 180637520629604287 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 6 2 180637520629604287 180637520629604287 180637520629604287 endpoint_11_32_p6 endpoint_11_32_w6
private theorem endpoint_11_32_w8 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 8 2 180637520629604287 = some 180637520629604287 := by decide +kernel
private theorem endpoint_11_32_p10 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 10 180637520629604287 = some 180637520629604287 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 8 2 180637520629604287 180637520629604287 180637520629604287 endpoint_11_32_p8 endpoint_11_32_w8
def endpoint_11_32 : CertifiedEndpoint :=
  ⟨⟨11, 32, 3916⟩, 180637520629604287, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_32_flag endpoint_11_32_sources 10 180637520629604287 180637520629604287 rfl endpoint_11_32_base endpoint_11_32_p10) (by decide)⟩
private def endpoint_11_33_flag : Flag := ⟨11, 33, 3892⟩
private def endpoint_11_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_33_base : receiptBase endpoint_11_33_flag endpoint_11_33_sources = some 184119471080432249 := by decide +kernel
private theorem endpoint_11_33_w0 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 2 184119471080432249 = some 184119471080432249 := by decide +kernel
private theorem endpoint_11_33_w2 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 2 2 184119471080432249 = some 184119471080432249 := by decide +kernel
private theorem endpoint_11_33_p4 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 4 184119471080432249 = some 184119471080432249 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 2 2 184119471080432249 184119471080432249 184119471080432249 endpoint_11_33_w0 endpoint_11_33_w2
private theorem endpoint_11_33_w4 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 4 2 184119471080432249 = some 184119471080432249 := by decide +kernel
private theorem endpoint_11_33_p6 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 6 184119471080432249 = some 184119471080432249 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 4 2 184119471080432249 184119471080432249 184119471080432249 endpoint_11_33_p4 endpoint_11_33_w4
private theorem endpoint_11_33_w6 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 6 2 184119471080432249 = some 184119471080432249 := by decide +kernel
private theorem endpoint_11_33_p8 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 8 184119471080432249 = some 184119471080432249 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 6 2 184119471080432249 184119471080432249 184119471080432249 endpoint_11_33_p6 endpoint_11_33_w6
private theorem endpoint_11_33_w8 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 8 2 184119471080432249 = some 184119471080432249 := by decide +kernel
private theorem endpoint_11_33_p10 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 10 184119471080432249 = some 184119471080432249 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 8 2 184119471080432249 184119471080432249 184119471080432249 endpoint_11_33_p8 endpoint_11_33_w8
def endpoint_11_33 : CertifiedEndpoint :=
  ⟨⟨11, 33, 3892⟩, 184119471080432249, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_33_flag endpoint_11_33_sources 10 184119471080432249 184119471080432249 rfl endpoint_11_33_base endpoint_11_33_p10) (by decide)⟩
private def endpoint_11_34_flag : Flag := ⟨11, 34, 3869⟩
private def endpoint_11_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_34_base : receiptBase endpoint_11_34_flag endpoint_11_34_sources = some 187592720325585539 := by decide +kernel
private theorem endpoint_11_34_w0 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 2 187592720325585539 = some 187592720325585539 := by decide +kernel
private theorem endpoint_11_34_w2 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 2 2 187592720325585539 = some 187592720325585539 := by decide +kernel
private theorem endpoint_11_34_p4 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 4 187592720325585539 = some 187592720325585539 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 2 2 187592720325585539 187592720325585539 187592720325585539 endpoint_11_34_w0 endpoint_11_34_w2
private theorem endpoint_11_34_w4 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 4 2 187592720325585539 = some 187592720325585539 := by decide +kernel
private theorem endpoint_11_34_p6 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 6 187592720325585539 = some 187592720325585539 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 4 2 187592720325585539 187592720325585539 187592720325585539 endpoint_11_34_p4 endpoint_11_34_w4
private theorem endpoint_11_34_w6 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 6 2 187592720325585539 = some 187592720325585539 := by decide +kernel
private theorem endpoint_11_34_p8 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 8 187592720325585539 = some 187592720325585539 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 6 2 187592720325585539 187592720325585539 187592720325585539 endpoint_11_34_p6 endpoint_11_34_w6
private theorem endpoint_11_34_w8 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 8 2 187592720325585539 = some 187592720325585539 := by decide +kernel
private theorem endpoint_11_34_p10 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 10 187592720325585539 = some 187592720325585539 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 8 2 187592720325585539 187592720325585539 187592720325585539 endpoint_11_34_p8 endpoint_11_34_w8
def endpoint_11_34 : CertifiedEndpoint :=
  ⟨⟨11, 34, 3869⟩, 187592720325585539, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_34_flag endpoint_11_34_sources 10 187592720325585539 187592720325585539 rfl endpoint_11_34_base endpoint_11_34_p10) (by decide)⟩
private def endpoint_11_35_flag : Flag := ⟨11, 35, 3845⟩
private def endpoint_11_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_35_base : receiptBase endpoint_11_35_flag endpoint_11_35_sources = some 190962874763959284 := by decide +kernel
private theorem endpoint_11_35_w0 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 2 190962874763959284 = some 190962874763959284 := by decide +kernel
private theorem endpoint_11_35_w2 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 2 2 190962874763959284 = some 190962874763959284 := by decide +kernel
private theorem endpoint_11_35_p4 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 4 190962874763959284 = some 190962874763959284 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 2 2 190962874763959284 190962874763959284 190962874763959284 endpoint_11_35_w0 endpoint_11_35_w2
private theorem endpoint_11_35_w4 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 4 2 190962874763959284 = some 190962874763959284 := by decide +kernel
private theorem endpoint_11_35_p6 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 6 190962874763959284 = some 190962874763959284 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 4 2 190962874763959284 190962874763959284 190962874763959284 endpoint_11_35_p4 endpoint_11_35_w4
private theorem endpoint_11_35_w6 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 6 2 190962874763959284 = some 190962874763959284 := by decide +kernel
private theorem endpoint_11_35_p8 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 8 190962874763959284 = some 190962874763959284 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 6 2 190962874763959284 190962874763959284 190962874763959284 endpoint_11_35_p6 endpoint_11_35_w6
private theorem endpoint_11_35_w8 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 8 2 190962874763959284 = some 190962874763959284 := by decide +kernel
private theorem endpoint_11_35_p10 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 10 190962874763959284 = some 190962874763959284 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 8 2 190962874763959284 190962874763959284 190962874763959284 endpoint_11_35_p8 endpoint_11_35_w8
def endpoint_11_35 : CertifiedEndpoint :=
  ⟨⟨11, 35, 3845⟩, 190962874763959284, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_35_flag endpoint_11_35_sources 10 190962874763959284 190962874763959284 rfl endpoint_11_35_base endpoint_11_35_p10) (by decide)⟩
private def endpoint_11_36_flag : Flag := ⟨11, 36, 3820⟩
private def endpoint_11_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_36_base : receiptBase endpoint_11_36_flag endpoint_11_36_sources = some 194226477065246962 := by decide +kernel
private theorem endpoint_11_36_w0 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 2 194226477065246962 = some 194226477065246962 := by decide +kernel
private theorem endpoint_11_36_w2 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 2 2 194226477065246962 = some 194226477065246962 := by decide +kernel
private theorem endpoint_11_36_p4 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 4 194226477065246962 = some 194226477065246962 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 2 2 194226477065246962 194226477065246962 194226477065246962 endpoint_11_36_w0 endpoint_11_36_w2
private theorem endpoint_11_36_w4 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 4 2 194226477065246962 = some 194226477065246962 := by decide +kernel
private theorem endpoint_11_36_p6 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 6 194226477065246962 = some 194226477065246962 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 4 2 194226477065246962 194226477065246962 194226477065246962 endpoint_11_36_p4 endpoint_11_36_w4
private theorem endpoint_11_36_w6 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 6 2 194226477065246962 = some 194226477065246962 := by decide +kernel
private theorem endpoint_11_36_p8 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 8 194226477065246962 = some 194226477065246962 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 6 2 194226477065246962 194226477065246962 194226477065246962 endpoint_11_36_p6 endpoint_11_36_w6
private theorem endpoint_11_36_w8 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 8 2 194226477065246962 = some 194226477065246962 := by decide +kernel
private theorem endpoint_11_36_p10 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 10 194226477065246962 = some 194226477065246962 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 8 2 194226477065246962 194226477065246962 194226477065246962 endpoint_11_36_p8 endpoint_11_36_w8
def endpoint_11_36 : CertifiedEndpoint :=
  ⟨⟨11, 36, 3820⟩, 194226477065246962, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_36_flag endpoint_11_36_sources 10 194226477065246962 194226477065246962 rfl endpoint_11_36_base endpoint_11_36_p10) (by decide)⟩
private def endpoint_11_37_flag : Flag := ⟨11, 37, 3795⟩
private def endpoint_11_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_37_base : receiptBase endpoint_11_37_flag endpoint_11_37_sources = some 197431300251718765 := by decide +kernel
private theorem endpoint_11_37_w0 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 2 197431300251718765 = some 197431300251718765 := by decide +kernel
private theorem endpoint_11_37_w2 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 2 2 197431300251718765 = some 197431300251718765 := by decide +kernel
private theorem endpoint_11_37_p4 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 4 197431300251718765 = some 197431300251718765 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 2 2 197431300251718765 197431300251718765 197431300251718765 endpoint_11_37_w0 endpoint_11_37_w2
private theorem endpoint_11_37_w4 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 4 2 197431300251718765 = some 197431300251718765 := by decide +kernel
private theorem endpoint_11_37_p6 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 6 197431300251718765 = some 197431300251718765 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 4 2 197431300251718765 197431300251718765 197431300251718765 endpoint_11_37_p4 endpoint_11_37_w4
private theorem endpoint_11_37_w6 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 6 2 197431300251718765 = some 197431300251718765 := by decide +kernel
private theorem endpoint_11_37_p8 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 8 197431300251718765 = some 197431300251718765 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 6 2 197431300251718765 197431300251718765 197431300251718765 endpoint_11_37_p6 endpoint_11_37_w6
private theorem endpoint_11_37_w8 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 8 2 197431300251718765 = some 197431300251718765 := by decide +kernel
private theorem endpoint_11_37_p10 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 10 197431300251718765 = some 197431300251718765 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 8 2 197431300251718765 197431300251718765 197431300251718765 endpoint_11_37_p8 endpoint_11_37_w8
def endpoint_11_37 : CertifiedEndpoint :=
  ⟨⟨11, 37, 3795⟩, 197431300251718765, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_37_flag endpoint_11_37_sources 10 197431300251718765 197431300251718765 rfl endpoint_11_37_base endpoint_11_37_p10) (by decide)⟩
private def endpoint_11_38_flag : Flag := ⟨11, 38, 3770⟩
private def endpoint_11_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_38_base : receiptBase endpoint_11_38_flag endpoint_11_38_sources = some 200577344323374691 := by decide +kernel
private theorem endpoint_11_38_w0 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 2 200577344323374691 = some 200577344323374691 := by decide +kernel
private theorem endpoint_11_38_w2 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 2 2 200577344323374691 = some 200577344323374691 := by decide +kernel
private theorem endpoint_11_38_p4 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 4 200577344323374691 = some 200577344323374691 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 2 2 200577344323374691 200577344323374691 200577344323374691 endpoint_11_38_w0 endpoint_11_38_w2
private theorem endpoint_11_38_w4 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 4 2 200577344323374691 = some 200577344323374691 := by decide +kernel
private theorem endpoint_11_38_p6 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 6 200577344323374691 = some 200577344323374691 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 4 2 200577344323374691 200577344323374691 200577344323374691 endpoint_11_38_p4 endpoint_11_38_w4
private theorem endpoint_11_38_w6 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 6 2 200577344323374691 = some 200577344323374691 := by decide +kernel
private theorem endpoint_11_38_p8 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 8 200577344323374691 = some 200577344323374691 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 6 2 200577344323374691 200577344323374691 200577344323374691 endpoint_11_38_p6 endpoint_11_38_w6
private theorem endpoint_11_38_w8 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 8 2 200577344323374691 = some 200577344323374691 := by decide +kernel
private theorem endpoint_11_38_p10 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 10 200577344323374691 = some 200577344323374691 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 8 2 200577344323374691 200577344323374691 200577344323374691 endpoint_11_38_p8 endpoint_11_38_w8
def endpoint_11_38 : CertifiedEndpoint :=
  ⟨⟨11, 38, 3770⟩, 200577344323374691, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_38_flag endpoint_11_38_sources 10 200577344323374691 200577344323374691 rfl endpoint_11_38_base endpoint_11_38_p10) (by decide)⟩
private def endpoint_11_39_flag : Flag := ⟨11, 39, 3745⟩
private def endpoint_11_39_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_39_base : receiptBase endpoint_11_39_flag endpoint_11_39_sources = some 203664609280214742 := by decide +kernel
private theorem endpoint_11_39_w0 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 2 203664609280214742 = some 203664609280214742 := by decide +kernel
private theorem endpoint_11_39_w2 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 2 2 203664609280214742 = some 203664609280214742 := by decide +kernel
private theorem endpoint_11_39_p4 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 4 203664609280214742 = some 203664609280214742 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 2 2 203664609280214742 203664609280214742 203664609280214742 endpoint_11_39_w0 endpoint_11_39_w2
private theorem endpoint_11_39_w4 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 4 2 203664609280214742 = some 203664609280214742 := by decide +kernel
private theorem endpoint_11_39_p6 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 6 203664609280214742 = some 203664609280214742 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 4 2 203664609280214742 203664609280214742 203664609280214742 endpoint_11_39_p4 endpoint_11_39_w4
private theorem endpoint_11_39_w6 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 6 2 203664609280214742 = some 203664609280214742 := by decide +kernel
private theorem endpoint_11_39_p8 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 8 203664609280214742 = some 203664609280214742 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 6 2 203664609280214742 203664609280214742 203664609280214742 endpoint_11_39_p6 endpoint_11_39_w6
private theorem endpoint_11_39_w8 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 8 2 203664609280214742 = some 203664609280214742 := by decide +kernel
private theorem endpoint_11_39_p10 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 10 203664609280214742 = some 203664609280214742 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 8 2 203664609280214742 203664609280214742 203664609280214742 endpoint_11_39_p8 endpoint_11_39_w8
def endpoint_11_39 : CertifiedEndpoint :=
  ⟨⟨11, 39, 3745⟩, 203664609280214742, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_39_flag endpoint_11_39_sources 10 203664609280214742 203664609280214742 rfl endpoint_11_39_base endpoint_11_39_p10) (by decide)⟩
private def endpoint_11_40_flag : Flag := ⟨11, 40, 3719⟩
private def endpoint_11_40_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_40_base : receiptBase endpoint_11_40_flag endpoint_11_40_sources = some 206638407439355683 := by decide +kernel
private theorem endpoint_11_40_w0 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 2 206638407439355683 = some 206638407439355683 := by decide +kernel
private theorem endpoint_11_40_w2 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 2 2 206638407439355683 = some 206638407439355683 := by decide +kernel
private theorem endpoint_11_40_p4 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 4 206638407439355683 = some 206638407439355683 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 2 2 206638407439355683 206638407439355683 206638407439355683 endpoint_11_40_w0 endpoint_11_40_w2
private theorem endpoint_11_40_w4 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 4 2 206638407439355683 = some 206638407439355683 := by decide +kernel
private theorem endpoint_11_40_p6 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 6 206638407439355683 = some 206638407439355683 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 4 2 206638407439355683 206638407439355683 206638407439355683 endpoint_11_40_p4 endpoint_11_40_w4
private theorem endpoint_11_40_w6 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 6 2 206638407439355683 = some 206638407439355683 := by decide +kernel
private theorem endpoint_11_40_p8 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 8 206638407439355683 = some 206638407439355683 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 6 2 206638407439355683 206638407439355683 206638407439355683 endpoint_11_40_p6 endpoint_11_40_w6
private theorem endpoint_11_40_w8 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 8 2 206638407439355683 = some 206638407439355683 := by decide +kernel
private theorem endpoint_11_40_p10 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 10 206638407439355683 = some 206638407439355683 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 8 2 206638407439355683 206638407439355683 206638407439355683 endpoint_11_40_p8 endpoint_11_40_w8
def endpoint_11_40 : CertifiedEndpoint :=
  ⟨⟨11, 40, 3719⟩, 206638407439355683, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_40_flag endpoint_11_40_sources 10 206638407439355683 206638407439355683 rfl endpoint_11_40_base endpoint_11_40_p10) (by decide)⟩
private def endpoint_11_41_flag : Flag := ⟨11, 41, 3693⟩
private def endpoint_11_41_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_41_base : receiptBase endpoint_11_41_flag endpoint_11_41_sources = some 209551121596809735 := by decide +kernel
private theorem endpoint_11_41_w0 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 2 209551121596809735 = some 209551121596809735 := by decide +kernel
private theorem endpoint_11_41_w2 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 2 2 209551121596809735 = some 209551121596809735 := by decide +kernel
private theorem endpoint_11_41_p4 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 4 209551121596809735 = some 209551121596809735 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 2 2 209551121596809735 209551121596809735 209551121596809735 endpoint_11_41_w0 endpoint_11_41_w2
private theorem endpoint_11_41_w4 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 4 2 209551121596809735 = some 209551121596809735 := by decide +kernel
private theorem endpoint_11_41_p6 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 6 209551121596809735 = some 209551121596809735 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 4 2 209551121596809735 209551121596809735 209551121596809735 endpoint_11_41_p4 endpoint_11_41_w4
private theorem endpoint_11_41_w6 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 6 2 209551121596809735 = some 209551121596809735 := by decide +kernel
private theorem endpoint_11_41_p8 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 8 209551121596809735 = some 209551121596809735 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 6 2 209551121596809735 209551121596809735 209551121596809735 endpoint_11_41_p6 endpoint_11_41_w6
private theorem endpoint_11_41_w8 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 8 2 209551121596809735 = some 209551121596809735 := by decide +kernel
private theorem endpoint_11_41_p10 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 10 209551121596809735 = some 209551121596809735 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 8 2 209551121596809735 209551121596809735 209551121596809735 endpoint_11_41_p8 endpoint_11_41_w8
def endpoint_11_41 : CertifiedEndpoint :=
  ⟨⟨11, 41, 3693⟩, 209551121596809735, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_41_flag endpoint_11_41_sources 10 209551121596809735 209551121596809735 rfl endpoint_11_41_base endpoint_11_41_p10) (by decide)⟩
private def endpoint_11_42_flag : Flag := ⟨11, 42, 3666⟩
private def endpoint_11_42_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_42_base : receiptBase endpoint_11_42_flag endpoint_11_42_sources = some 212345759182822650 := by decide +kernel
private theorem endpoint_11_42_w0 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 2 212345759182822650 = some 212345759182822650 := by decide +kernel
private theorem endpoint_11_42_w2 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 2 2 212345759182822650 = some 212345759182822650 := by decide +kernel
private theorem endpoint_11_42_p4 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 4 212345759182822650 = some 212345759182822650 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 2 2 212345759182822650 212345759182822650 212345759182822650 endpoint_11_42_w0 endpoint_11_42_w2
private theorem endpoint_11_42_w4 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 4 2 212345759182822650 = some 212345759182822650 := by decide +kernel
private theorem endpoint_11_42_p6 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 6 212345759182822650 = some 212345759182822650 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 4 2 212345759182822650 212345759182822650 212345759182822650 endpoint_11_42_p4 endpoint_11_42_w4
private theorem endpoint_11_42_w6 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 6 2 212345759182822650 = some 212345759182822650 := by decide +kernel
private theorem endpoint_11_42_p8 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 8 212345759182822650 = some 212345759182822650 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 6 2 212345759182822650 212345759182822650 212345759182822650 endpoint_11_42_p6 endpoint_11_42_w6
private theorem endpoint_11_42_w8 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 8 2 212345759182822650 = some 212345759182822650 := by decide +kernel
private theorem endpoint_11_42_p10 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 10 212345759182822650 = some 212345759182822650 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 8 2 212345759182822650 212345759182822650 212345759182822650 endpoint_11_42_p8 endpoint_11_42_w8
def endpoint_11_42 : CertifiedEndpoint :=
  ⟨⟨11, 42, 3666⟩, 212345759182822650, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_42_flag endpoint_11_42_sources 10 212345759182822650 212345759182822650 rfl endpoint_11_42_base endpoint_11_42_p10) (by decide)⟩
private def endpoint_11_43_flag : Flag := ⟨11, 43, 3639⟩
private def endpoint_11_43_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_43_base : receiptBase endpoint_11_43_flag endpoint_11_43_sources = some 215077007880277661 := by decide +kernel
private theorem endpoint_11_43_w0 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 2 215077007880277661 = some 215077007880277661 := by decide +kernel
private theorem endpoint_11_43_w2 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 2 2 215077007880277661 = some 215077007880277661 := by decide +kernel
private theorem endpoint_11_43_p4 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 4 215077007880277661 = some 215077007880277661 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 2 2 215077007880277661 215077007880277661 215077007880277661 endpoint_11_43_w0 endpoint_11_43_w2
private theorem endpoint_11_43_w4 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 4 2 215077007880277661 = some 215077007880277661 := by decide +kernel
private theorem endpoint_11_43_p6 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 6 215077007880277661 = some 215077007880277661 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 4 2 215077007880277661 215077007880277661 215077007880277661 endpoint_11_43_p4 endpoint_11_43_w4
private theorem endpoint_11_43_w6 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 6 2 215077007880277661 = some 215077007880277661 := by decide +kernel
private theorem endpoint_11_43_p8 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 8 215077007880277661 = some 215077007880277661 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 6 2 215077007880277661 215077007880277661 215077007880277661 endpoint_11_43_p6 endpoint_11_43_w6
private theorem endpoint_11_43_w8 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 8 2 215077007880277661 = some 215077007880277661 := by decide +kernel
private theorem endpoint_11_43_p10 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 10 215077007880277661 = some 215077007880277661 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 8 2 215077007880277661 215077007880277661 215077007880277661 endpoint_11_43_p8 endpoint_11_43_w8
def endpoint_11_43 : CertifiedEndpoint :=
  ⟨⟨11, 43, 3639⟩, 215077007880277661, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_43_flag endpoint_11_43_sources 10 215077007880277661 215077007880277661 rfl endpoint_11_43_base endpoint_11_43_p10) (by decide)⟩
private def endpoint_11_44_flag : Flag := ⟨11, 44, 3611⟩
private def endpoint_11_44_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_44_base : receiptBase endpoint_11_44_flag endpoint_11_44_sources = some 217685570232549507 := by decide +kernel
private theorem endpoint_11_44_w0 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 2 217685570232549507 = some 218068351159124808 := by decide +kernel
private theorem endpoint_11_44_w2 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 2 2 218068351159124808 = some 218068351159124808 := by decide +kernel
private theorem endpoint_11_44_p4 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 4 217685570232549507 = some 218068351159124808 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 2 2 217685570232549507 218068351159124808 218068351159124808 endpoint_11_44_w0 endpoint_11_44_w2
private theorem endpoint_11_44_w4 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 4 2 218068351159124808 = some 218068351159124808 := by decide +kernel
private theorem endpoint_11_44_p6 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 6 217685570232549507 = some 218068351159124808 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 4 2 217685570232549507 218068351159124808 218068351159124808 endpoint_11_44_p4 endpoint_11_44_w4
private theorem endpoint_11_44_w6 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 6 2 218068351159124808 = some 218068351159124808 := by decide +kernel
private theorem endpoint_11_44_p8 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 8 217685570232549507 = some 218068351159124808 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 6 2 217685570232549507 218068351159124808 218068351159124808 endpoint_11_44_p6 endpoint_11_44_w6
private theorem endpoint_11_44_w8 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 8 2 218068351159124808 = some 218068351159124808 := by decide +kernel
private theorem endpoint_11_44_p10 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 10 217685570232549507 = some 218068351159124808 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 8 2 217685570232549507 218068351159124808 218068351159124808 endpoint_11_44_p8 endpoint_11_44_w8
def endpoint_11_44 : CertifiedEndpoint :=
  ⟨⟨11, 44, 3611⟩, 218068351159124808, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_44_flag endpoint_11_44_sources 10 217685570232549507 218068351159124808 rfl endpoint_11_44_base endpoint_11_44_p10) (by decide)⟩
private def endpoint_11_45_flag : Flag := ⟨11, 45, 3583⟩
private def endpoint_11_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_45_base : receiptBase endpoint_11_45_flag endpoint_11_45_sources = some 220782281604394667 := by decide +kernel
private theorem endpoint_11_45_w0 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 2 220782281604394667 = some 220782281604394667 := by decide +kernel
private theorem endpoint_11_45_w2 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 2 2 220782281604394667 = some 220782281604394667 := by decide +kernel
private theorem endpoint_11_45_p4 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 4 220782281604394667 = some 220782281604394667 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 2 2 220782281604394667 220782281604394667 220782281604394667 endpoint_11_45_w0 endpoint_11_45_w2
private theorem endpoint_11_45_w4 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 4 2 220782281604394667 = some 220782281604394667 := by decide +kernel
private theorem endpoint_11_45_p6 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 6 220782281604394667 = some 220782281604394667 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 4 2 220782281604394667 220782281604394667 220782281604394667 endpoint_11_45_p4 endpoint_11_45_w4
private theorem endpoint_11_45_w6 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 6 2 220782281604394667 = some 220782281604394667 := by decide +kernel
private theorem endpoint_11_45_p8 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 8 220782281604394667 = some 220782281604394667 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 6 2 220782281604394667 220782281604394667 220782281604394667 endpoint_11_45_p6 endpoint_11_45_w6
private theorem endpoint_11_45_w8 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 8 2 220782281604394667 = some 220782281604394667 := by decide +kernel
private theorem endpoint_11_45_p10 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 10 220782281604394667 = some 220782281604394667 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 8 2 220782281604394667 220782281604394667 220782281604394667 endpoint_11_45_p8 endpoint_11_45_w8
def endpoint_11_45 : CertifiedEndpoint :=
  ⟨⟨11, 45, 3583⟩, 220782281604394667, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_45_flag endpoint_11_45_sources 10 220782281604394667 220782281604394667 rfl endpoint_11_45_base endpoint_11_45_p10) (by decide)⟩
private def endpoint_11_46_flag : Flag := ⟨11, 46, 3554⟩
private def endpoint_11_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_46_base : receiptBase endpoint_11_46_flag endpoint_11_46_sources = some 223166531841162319 := by decide +kernel
private theorem endpoint_11_46_w0 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 2 223166531841162319 = some 223166531841162319 := by decide +kernel
private theorem endpoint_11_46_w2 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 2 2 223166531841162319 = some 223166531841162319 := by decide +kernel
private theorem endpoint_11_46_p4 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 4 223166531841162319 = some 223166531841162319 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 2 2 223166531841162319 223166531841162319 223166531841162319 endpoint_11_46_w0 endpoint_11_46_w2
private theorem endpoint_11_46_w4 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 4 2 223166531841162319 = some 223166531841162319 := by decide +kernel
private theorem endpoint_11_46_p6 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 6 223166531841162319 = some 223166531841162319 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 4 2 223166531841162319 223166531841162319 223166531841162319 endpoint_11_46_p4 endpoint_11_46_w4
private theorem endpoint_11_46_w6 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 6 2 223166531841162319 = some 223166531841162319 := by decide +kernel
private theorem endpoint_11_46_p8 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 8 223166531841162319 = some 223166531841162319 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 6 2 223166531841162319 223166531841162319 223166531841162319 endpoint_11_46_p6 endpoint_11_46_w6
private theorem endpoint_11_46_w8 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 8 2 223166531841162319 = some 223166531841162319 := by decide +kernel
private theorem endpoint_11_46_p10 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 10 223166531841162319 = some 223166531841162319 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 8 2 223166531841162319 223166531841162319 223166531841162319 endpoint_11_46_p8 endpoint_11_46_w8
def endpoint_11_46 : CertifiedEndpoint :=
  ⟨⟨11, 46, 3554⟩, 223166531841162319, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_46_flag endpoint_11_46_sources 10 223166531841162319 223166531841162319 rfl endpoint_11_46_base endpoint_11_46_p10) (by decide)⟩
private def endpoint_11_47_flag : Flag := ⟨11, 47, 3525⟩
private def endpoint_11_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_47_base : receiptBase endpoint_11_47_flag endpoint_11_47_sources = some 225483053347120695 := by decide +kernel
private theorem endpoint_11_47_w0 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 2 225483053347120695 = some 225483053347120695 := by decide +kernel
private theorem endpoint_11_47_w2 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 2 2 225483053347120695 = some 225483053347120695 := by decide +kernel
private theorem endpoint_11_47_p4 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 4 225483053347120695 = some 225483053347120695 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 2 2 225483053347120695 225483053347120695 225483053347120695 endpoint_11_47_w0 endpoint_11_47_w2
private theorem endpoint_11_47_w4 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 4 2 225483053347120695 = some 225483053347120695 := by decide +kernel
private theorem endpoint_11_47_p6 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 6 225483053347120695 = some 225483053347120695 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 4 2 225483053347120695 225483053347120695 225483053347120695 endpoint_11_47_p4 endpoint_11_47_w4
private theorem endpoint_11_47_w6 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 6 2 225483053347120695 = some 225483053347120695 := by decide +kernel
private theorem endpoint_11_47_p8 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 8 225483053347120695 = some 225483053347120695 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 6 2 225483053347120695 225483053347120695 225483053347120695 endpoint_11_47_p6 endpoint_11_47_w6
private theorem endpoint_11_47_w8 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 8 2 225483053347120695 = some 225483053347120695 := by decide +kernel
private theorem endpoint_11_47_p10 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 10 225483053347120695 = some 225483053347120695 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 8 2 225483053347120695 225483053347120695 225483053347120695 endpoint_11_47_p8 endpoint_11_47_w8
def endpoint_11_47 : CertifiedEndpoint :=
  ⟨⟨11, 47, 3525⟩, 225483053347120695, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_47_flag endpoint_11_47_sources 10 225483053347120695 225483053347120695 rfl endpoint_11_47_base endpoint_11_47_p10) (by decide)⟩
private def endpoint_11_48_flag : Flag := ⟨11, 48, 3495⟩
private def endpoint_11_48_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_48_base : receiptBase endpoint_11_48_flag endpoint_11_48_sources = some 227667696017798791 := by decide +kernel
private theorem endpoint_11_48_w0 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 2 227667696017798791 = some 227667696017798791 := by decide +kernel
private theorem endpoint_11_48_w2 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 2 2 227667696017798791 = some 227667696017798791 := by decide +kernel
private theorem endpoint_11_48_p4 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 4 227667696017798791 = some 227667696017798791 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 2 2 227667696017798791 227667696017798791 227667696017798791 endpoint_11_48_w0 endpoint_11_48_w2
private theorem endpoint_11_48_w4 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 4 2 227667696017798791 = some 227667696017798791 := by decide +kernel
private theorem endpoint_11_48_p6 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 6 227667696017798791 = some 227667696017798791 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 4 2 227667696017798791 227667696017798791 227667696017798791 endpoint_11_48_p4 endpoint_11_48_w4
private theorem endpoint_11_48_w6 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 6 2 227667696017798791 = some 227667696017798791 := by decide +kernel
private theorem endpoint_11_48_p8 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 8 227667696017798791 = some 227667696017798791 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 6 2 227667696017798791 227667696017798791 227667696017798791 endpoint_11_48_p6 endpoint_11_48_w6
private theorem endpoint_11_48_w8 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 8 2 227667696017798791 = some 227667696017798791 := by decide +kernel
private theorem endpoint_11_48_p10 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 10 227667696017798791 = some 227667696017798791 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 8 2 227667696017798791 227667696017798791 227667696017798791 endpoint_11_48_p8 endpoint_11_48_w8
def endpoint_11_48 : CertifiedEndpoint :=
  ⟨⟨11, 48, 3495⟩, 227667696017798791, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_48_flag endpoint_11_48_sources 10 227667696017798791 227667696017798791 rfl endpoint_11_48_base endpoint_11_48_p10) (by decide)⟩
private def endpoint_11_49_flag : Flag := ⟨11, 49, 3465⟩
private def endpoint_11_49_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_49_base : receiptBase endpoint_11_49_flag endpoint_11_49_sources = some 229782314068487636 := by decide +kernel
private theorem endpoint_11_49_w0 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 2 229782314068487636 = some 230908760493026337 := by decide +kernel
private theorem endpoint_11_49_w2 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 2 2 230908760493026337 = some 230908760493026337 := by decide +kernel
private theorem endpoint_11_49_p4 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 4 229782314068487636 = some 230908760493026337 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 2 2 229782314068487636 230908760493026337 230908760493026337 endpoint_11_49_w0 endpoint_11_49_w2
private theorem endpoint_11_49_w4 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 4 2 230908760493026337 = some 230908760493026337 := by decide +kernel
private theorem endpoint_11_49_p6 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 6 229782314068487636 = some 230908760493026337 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 4 2 229782314068487636 230908760493026337 230908760493026337 endpoint_11_49_p4 endpoint_11_49_w4
private theorem endpoint_11_49_w6 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 6 2 230908760493026337 = some 230908760493026337 := by decide +kernel
private theorem endpoint_11_49_p8 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 8 229782314068487636 = some 230908760493026337 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 6 2 229782314068487636 230908760493026337 230908760493026337 endpoint_11_49_p6 endpoint_11_49_w6
private theorem endpoint_11_49_w8 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 8 2 230908760493026337 = some 230908760493026337 := by decide +kernel
private theorem endpoint_11_49_p10 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 10 229782314068487636 = some 230908760493026337 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 8 2 229782314068487636 230908760493026337 230908760493026337 endpoint_11_49_p8 endpoint_11_49_w8
def endpoint_11_49 : CertifiedEndpoint :=
  ⟨⟨11, 49, 3465⟩, 230908760493026337, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_49_flag endpoint_11_49_sources 10 229782314068487636 230908760493026337 rfl endpoint_11_49_base endpoint_11_49_p10) (by decide)⟩
private def endpoint_11_50_flag : Flag := ⟨11, 50, 3433⟩
private def endpoint_11_50_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_50_base : receiptBase endpoint_11_50_flag endpoint_11_50_sources = some 231694015511885268 := by decide +kernel
private theorem endpoint_11_50_w0 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 2 231694015511885268 = some 235176115007985510 := by decide +kernel
private theorem endpoint_11_50_w2 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 2 2 235176115007985510 = some 235176115007985510 := by decide +kernel
private theorem endpoint_11_50_p4 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 4 231694015511885268 = some 235176115007985510 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 2 2 231694015511885268 235176115007985510 235176115007985510 endpoint_11_50_w0 endpoint_11_50_w2
private theorem endpoint_11_50_w4 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 4 2 235176115007985510 = some 235176115007985510 := by decide +kernel
private theorem endpoint_11_50_p6 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 6 231694015511885268 = some 235176115007985510 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 4 2 231694015511885268 235176115007985510 235176115007985510 endpoint_11_50_p4 endpoint_11_50_w4
private theorem endpoint_11_50_w6 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 6 2 235176115007985510 = some 235176115007985510 := by decide +kernel
private theorem endpoint_11_50_p8 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 8 231694015511885268 = some 235176115007985510 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 6 2 231694015511885268 235176115007985510 235176115007985510 endpoint_11_50_p6 endpoint_11_50_w6
private theorem endpoint_11_50_w8 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 8 2 235176115007985510 = some 235176115007985510 := by decide +kernel
private theorem endpoint_11_50_p10 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 10 231694015511885268 = some 235176115007985510 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 8 2 231694015511885268 235176115007985510 235176115007985510 endpoint_11_50_p8 endpoint_11_50_w8
def endpoint_11_50 : CertifiedEndpoint :=
  ⟨⟨11, 50, 3433⟩, 235176115007985510, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_50_flag endpoint_11_50_sources 10 231694015511885268 235176115007985510 rfl endpoint_11_50_base endpoint_11_50_p10) (by decide)⟩
private def endpoint_11_51_flag : Flag := ⟨11, 51, 3402⟩
private def endpoint_11_51_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_11_51_base : receiptBase endpoint_11_51_flag endpoint_11_51_sources = some 234201885364062047 := by decide +kernel
private theorem endpoint_11_51_w0 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 2 234201885364062047 = some 234201885364062047 := by decide +kernel
private theorem endpoint_11_51_w2 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 2 2 234201885364062047 = some 234201885364062047 := by decide +kernel
private theorem endpoint_11_51_p4 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 4 234201885364062047 = some 234201885364062047 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 2 2 234201885364062047 234201885364062047 234201885364062047 endpoint_11_51_w0 endpoint_11_51_w2
private theorem endpoint_11_51_w4 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 4 2 234201885364062047 = some 234201885364062047 := by decide +kernel
private theorem endpoint_11_51_p6 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 6 234201885364062047 = some 234201885364062047 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 4 2 234201885364062047 234201885364062047 234201885364062047 endpoint_11_51_p4 endpoint_11_51_w4
private theorem endpoint_11_51_w6 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 6 2 234201885364062047 = some 234201885364062047 := by decide +kernel
private theorem endpoint_11_51_p8 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 8 234201885364062047 = some 234201885364062047 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 6 2 234201885364062047 234201885364062047 234201885364062047 endpoint_11_51_p6 endpoint_11_51_w6
private theorem endpoint_11_51_w8 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 8 2 234201885364062047 = some 234201885364062047 := by decide +kernel
private theorem endpoint_11_51_p10 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 10 234201885364062047 = some 234201885364062047 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 8 2 234201885364062047 234201885364062047 234201885364062047 endpoint_11_51_p8 endpoint_11_51_w8
def endpoint_11_51 : CertifiedEndpoint :=
  ⟨⟨11, 51, 3402⟩, 234201885364062047, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_11_51_flag endpoint_11_51_sources 10 234201885364062047 234201885364062047 rfl endpoint_11_51_base endpoint_11_51_p10) (by decide)⟩
private def endpoint_11_52_flag : Flag := ⟨11, 52, 3369⟩
private def endpoint_11_52_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_11_52_base : receiptBase endpoint_11_52_flag endpoint_11_52_sources = some 235905566463420103 := by decide +kernel
private theorem endpoint_11_52_w0 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 2 235905566463420103 = some 235905566463420103 := by decide +kernel
private theorem endpoint_11_52_w2 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 2 2 235905566463420103 = some 235905566463420103 := by decide +kernel
private theorem endpoint_11_52_p4 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 4 235905566463420103 = some 235905566463420103 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 2 2 235905566463420103 235905566463420103 235905566463420103 endpoint_11_52_w0 endpoint_11_52_w2
private theorem endpoint_11_52_w4 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 4 2 235905566463420103 = some 235905566463420103 := by decide +kernel
private theorem endpoint_11_52_p6 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 6 235905566463420103 = some 235905566463420103 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 4 2 235905566463420103 235905566463420103 235905566463420103 endpoint_11_52_p4 endpoint_11_52_w4
private theorem endpoint_11_52_w6 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 6 2 235905566463420103 = some 235905566463420103 := by decide +kernel
private theorem endpoint_11_52_p8 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 8 235905566463420103 = some 235905566463420103 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 6 2 235905566463420103 235905566463420103 235905566463420103 endpoint_11_52_p6 endpoint_11_52_w6
private theorem endpoint_11_52_w8 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 8 2 235905566463420103 = some 235905566463420103 := by decide +kernel
private theorem endpoint_11_52_p10 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 10 235905566463420103 = some 235905566463420103 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 8 2 235905566463420103 235905566463420103 235905566463420103 endpoint_11_52_p8 endpoint_11_52_w8
def endpoint_11_52 : CertifiedEndpoint :=
  ⟨⟨11, 52, 3369⟩, 235905566463420103, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_11_52_flag endpoint_11_52_sources 10 235905566463420103 235905566463420103 rfl endpoint_11_52_base endpoint_11_52_p10) (by decide)⟩
private def endpoint_11_53_flag : Flag := ⟨11, 53, 3336⟩
private def endpoint_11_53_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_11_53_base : receiptBase endpoint_11_53_flag endpoint_11_53_sources = some 237532029251221508 := by decide +kernel
private theorem endpoint_11_53_w0 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 2 237532029251221508 = some 239315209067524611 := by decide +kernel
private theorem endpoint_11_53_w2 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 2 2 239315209067524611 = some 239315209067524611 := by decide +kernel
private theorem endpoint_11_53_p4 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 4 237532029251221508 = some 239315209067524611 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 2 2 237532029251221508 239315209067524611 239315209067524611 endpoint_11_53_w0 endpoint_11_53_w2
private theorem endpoint_11_53_w4 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 4 2 239315209067524611 = some 239315209067524611 := by decide +kernel
private theorem endpoint_11_53_p6 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 6 237532029251221508 = some 239315209067524611 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 4 2 237532029251221508 239315209067524611 239315209067524611 endpoint_11_53_p4 endpoint_11_53_w4
private theorem endpoint_11_53_w6 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 6 2 239315209067524611 = some 239315209067524611 := by decide +kernel
private theorem endpoint_11_53_p8 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 8 237532029251221508 = some 239315209067524611 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 6 2 237532029251221508 239315209067524611 239315209067524611 endpoint_11_53_p6 endpoint_11_53_w6
private theorem endpoint_11_53_w8 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 8 2 239315209067524611 = some 239315209067524611 := by decide +kernel
private theorem endpoint_11_53_p10 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 10 237532029251221508 = some 239315209067524611 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 8 2 237532029251221508 239315209067524611 239315209067524611 endpoint_11_53_p8 endpoint_11_53_w8
def endpoint_11_53 : CertifiedEndpoint :=
  ⟨⟨11, 53, 3336⟩, 239315209067524611, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_11_53_flag endpoint_11_53_sources 10 237532029251221508 239315209067524611 rfl endpoint_11_53_base endpoint_11_53_p10) (by decide)⟩
private def endpoint_11_54_flag : Flag := ⟨11, 54, 3302⟩
private def endpoint_11_54_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_54_base : receiptBase endpoint_11_54_flag endpoint_11_54_sources = some 241607279156108207 := by decide +kernel
private theorem endpoint_11_54_w0 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 2 241607279156108207 = some 241607279156108207 := by decide +kernel
private theorem endpoint_11_54_w2 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 2 2 241607279156108207 = some 241607279156108207 := by decide +kernel
private theorem endpoint_11_54_p4 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 4 241607279156108207 = some 241607279156108207 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 2 2 241607279156108207 241607279156108207 241607279156108207 endpoint_11_54_w0 endpoint_11_54_w2
private theorem endpoint_11_54_w4 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 4 2 241607279156108207 = some 241607279156108207 := by decide +kernel
private theorem endpoint_11_54_p6 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 6 241607279156108207 = some 241607279156108207 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 4 2 241607279156108207 241607279156108207 241607279156108207 endpoint_11_54_p4 endpoint_11_54_w4
private theorem endpoint_11_54_w6 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 6 2 241607279156108207 = some 241607279156108207 := by decide +kernel
private theorem endpoint_11_54_p8 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 8 241607279156108207 = some 241607279156108207 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 6 2 241607279156108207 241607279156108207 241607279156108207 endpoint_11_54_p6 endpoint_11_54_w6
private theorem endpoint_11_54_w8 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 8 2 241607279156108207 = some 241607279156108207 := by decide +kernel
private theorem endpoint_11_54_p10 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 10 241607279156108207 = some 241607279156108207 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 8 2 241607279156108207 241607279156108207 241607279156108207 endpoint_11_54_p8 endpoint_11_54_w8
def endpoint_11_54 : CertifiedEndpoint :=
  ⟨⟨11, 54, 3302⟩, 241607279156108207, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_54_flag endpoint_11_54_sources 10 241607279156108207 241607279156108207 rfl endpoint_11_54_base endpoint_11_54_p10) (by decide)⟩
private def endpoint_11_55_flag : Flag := ⟨11, 55, 3266⟩
private def endpoint_11_55_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_55_base : receiptBase endpoint_11_55_flag endpoint_11_55_sources = some 242824678736362234 := by decide +kernel
private theorem endpoint_11_55_w0 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 2 242824678736362234 = some 242824678736362234 := by decide +kernel
private theorem endpoint_11_55_w2 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 2 2 242824678736362234 = some 242824678736362234 := by decide +kernel
private theorem endpoint_11_55_p4 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 4 242824678736362234 = some 242824678736362234 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 2 2 242824678736362234 242824678736362234 242824678736362234 endpoint_11_55_w0 endpoint_11_55_w2
private theorem endpoint_11_55_w4 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 4 2 242824678736362234 = some 242824678736362234 := by decide +kernel
private theorem endpoint_11_55_p6 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 6 242824678736362234 = some 242824678736362234 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 4 2 242824678736362234 242824678736362234 242824678736362234 endpoint_11_55_p4 endpoint_11_55_w4
private theorem endpoint_11_55_w6 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 6 2 242824678736362234 = some 242824678736362234 := by decide +kernel
private theorem endpoint_11_55_p8 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 8 242824678736362234 = some 242824678736362234 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 6 2 242824678736362234 242824678736362234 242824678736362234 endpoint_11_55_p6 endpoint_11_55_w6
private theorem endpoint_11_55_w8 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 8 2 242824678736362234 = some 242824678736362234 := by decide +kernel
private theorem endpoint_11_55_p10 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 10 242824678736362234 = some 242824678736362234 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 8 2 242824678736362234 242824678736362234 242824678736362234 endpoint_11_55_p8 endpoint_11_55_w8
def endpoint_11_55 : CertifiedEndpoint :=
  ⟨⟨11, 55, 3266⟩, 242824678736362234, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_55_flag endpoint_11_55_sources 10 242824678736362234 242824678736362234 rfl endpoint_11_55_base endpoint_11_55_p10) (by decide)⟩
private def endpoint_11_56_flag : Flag := ⟨11, 56, 3230⟩
private def endpoint_11_56_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_56_base : receiptBase endpoint_11_56_flag endpoint_11_56_sources = some 243957621696431285 := by decide +kernel
private theorem endpoint_11_56_w0 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 2 243957621696431285 = some 243957621696431285 := by decide +kernel
private theorem endpoint_11_56_w2 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 2 2 243957621696431285 = some 243957621696431285 := by decide +kernel
private theorem endpoint_11_56_p4 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 4 243957621696431285 = some 243957621696431285 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 2 2 243957621696431285 243957621696431285 243957621696431285 endpoint_11_56_w0 endpoint_11_56_w2
private theorem endpoint_11_56_w4 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 4 2 243957621696431285 = some 243957621696431285 := by decide +kernel
private theorem endpoint_11_56_p6 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 6 243957621696431285 = some 243957621696431285 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 4 2 243957621696431285 243957621696431285 243957621696431285 endpoint_11_56_p4 endpoint_11_56_w4
private theorem endpoint_11_56_w6 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 6 2 243957621696431285 = some 243957621696431285 := by decide +kernel
private theorem endpoint_11_56_p8 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 8 243957621696431285 = some 243957621696431285 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 6 2 243957621696431285 243957621696431285 243957621696431285 endpoint_11_56_p6 endpoint_11_56_w6
private theorem endpoint_11_56_w8 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 8 2 243957621696431285 = some 243957621696431285 := by decide +kernel
private theorem endpoint_11_56_p10 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 10 243957621696431285 = some 243957621696431285 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 8 2 243957621696431285 243957621696431285 243957621696431285 endpoint_11_56_p8 endpoint_11_56_w8
def endpoint_11_56 : CertifiedEndpoint :=
  ⟨⟨11, 56, 3230⟩, 243957621696431285, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_56_flag endpoint_11_56_sources 10 243957621696431285 243957621696431285 rfl endpoint_11_56_base endpoint_11_56_p10) (by decide)⟩
private def endpoint_11_57_flag : Flag := ⟨11, 57, 3193⟩
private def endpoint_11_57_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_57_base : receiptBase endpoint_11_57_flag endpoint_11_57_sources = some 244930399000306422 := by decide +kernel
private theorem endpoint_11_57_w0 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 2 244930399000306422 = some 244930399000306422 := by decide +kernel
private theorem endpoint_11_57_w2 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 2 2 244930399000306422 = some 244930399000306422 := by decide +kernel
private theorem endpoint_11_57_p4 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 4 244930399000306422 = some 244930399000306422 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 2 2 244930399000306422 244930399000306422 244930399000306422 endpoint_11_57_w0 endpoint_11_57_w2
private theorem endpoint_11_57_w4 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 4 2 244930399000306422 = some 244930399000306422 := by decide +kernel
private theorem endpoint_11_57_p6 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 6 244930399000306422 = some 244930399000306422 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 4 2 244930399000306422 244930399000306422 244930399000306422 endpoint_11_57_p4 endpoint_11_57_w4
private theorem endpoint_11_57_w6 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 6 2 244930399000306422 = some 244930399000306422 := by decide +kernel
private theorem endpoint_11_57_p8 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 8 244930399000306422 = some 244930399000306422 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 6 2 244930399000306422 244930399000306422 244930399000306422 endpoint_11_57_p6 endpoint_11_57_w6
private theorem endpoint_11_57_w8 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 8 2 244930399000306422 = some 244930399000306422 := by decide +kernel
private theorem endpoint_11_57_p10 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 10 244930399000306422 = some 244930399000306422 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 8 2 244930399000306422 244930399000306422 244930399000306422 endpoint_11_57_p8 endpoint_11_57_w8
def endpoint_11_57 : CertifiedEndpoint :=
  ⟨⟨11, 57, 3193⟩, 244930399000306422, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_57_flag endpoint_11_57_sources 10 244930399000306422 244930399000306422 rfl endpoint_11_57_base endpoint_11_57_p10) (by decide)⟩
private def endpoint_11_58_flag : Flag := ⟨11, 58, 3155⟩
private def endpoint_11_58_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_58_base : receiptBase endpoint_11_58_flag endpoint_11_58_sources = some 245739539827980042 := by decide +kernel
private theorem endpoint_11_58_w0 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 2 245739539827980042 = some 245954155847962778 := by decide +kernel
private theorem endpoint_11_58_w2 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 2 2 245954155847962778 = some 245954155847962778 := by decide +kernel
private theorem endpoint_11_58_p4 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 4 245739539827980042 = some 245954155847962778 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 2 2 245739539827980042 245954155847962778 245954155847962778 endpoint_11_58_w0 endpoint_11_58_w2
private theorem endpoint_11_58_w4 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 4 2 245954155847962778 = some 245954155847962778 := by decide +kernel
private theorem endpoint_11_58_p6 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 6 245739539827980042 = some 245954155847962778 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 4 2 245739539827980042 245954155847962778 245954155847962778 endpoint_11_58_p4 endpoint_11_58_w4
private theorem endpoint_11_58_w6 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 6 2 245954155847962778 = some 245954155847962778 := by decide +kernel
private theorem endpoint_11_58_p8 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 8 245739539827980042 = some 245954155847962778 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 6 2 245739539827980042 245954155847962778 245954155847962778 endpoint_11_58_p6 endpoint_11_58_w6
private theorem endpoint_11_58_w8 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 8 2 245954155847962778 = some 245954155847962778 := by decide +kernel
private theorem endpoint_11_58_p10 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 10 245739539827980042 = some 245954155847962778 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 8 2 245739539827980042 245954155847962778 245954155847962778 endpoint_11_58_p8 endpoint_11_58_w8
def endpoint_11_58 : CertifiedEndpoint :=
  ⟨⟨11, 58, 3155⟩, 245954155847962778, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_58_flag endpoint_11_58_sources 10 245739539827980042 245954155847962778 rfl endpoint_11_58_base endpoint_11_58_p10) (by decide)⟩
private def endpoint_11_59_flag : Flag := ⟨11, 59, 3115⟩
private def endpoint_11_59_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_59_base : receiptBase endpoint_11_59_flag endpoint_11_59_sources = some 246303550443430540 := by decide +kernel
private theorem endpoint_11_59_w0 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 2 246303550443430540 = some 248991305981239338 := by decide +kernel
private theorem endpoint_11_59_w2 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 2 2 248991305981239338 = some 248991305981239338 := by decide +kernel
private theorem endpoint_11_59_p4 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 4 246303550443430540 = some 248991305981239338 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 2 2 246303550443430540 248991305981239338 248991305981239338 endpoint_11_59_w0 endpoint_11_59_w2
private theorem endpoint_11_59_w4 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 4 2 248991305981239338 = some 248991305981239338 := by decide +kernel
private theorem endpoint_11_59_p6 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 6 246303550443430540 = some 248991305981239338 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 4 2 246303550443430540 248991305981239338 248991305981239338 endpoint_11_59_p4 endpoint_11_59_w4
private theorem endpoint_11_59_w6 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 6 2 248991305981239338 = some 248991305981239338 := by decide +kernel
private theorem endpoint_11_59_p8 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 8 246303550443430540 = some 248991305981239338 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 6 2 246303550443430540 248991305981239338 248991305981239338 endpoint_11_59_p6 endpoint_11_59_w6
private theorem endpoint_11_59_w8 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 8 2 248991305981239338 = some 248991305981239338 := by decide +kernel
private theorem endpoint_11_59_p10 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 10 246303550443430540 = some 248991305981239338 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 8 2 246303550443430540 248991305981239338 248991305981239338 endpoint_11_59_p8 endpoint_11_59_w8
def endpoint_11_59 : CertifiedEndpoint :=
  ⟨⟨11, 59, 3115⟩, 248991305981239338, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_59_flag endpoint_11_59_sources 10 246303550443430540 248991305981239338 rfl endpoint_11_59_base endpoint_11_59_p10) (by decide)⟩
private def endpoint_11_60_flag : Flag := ⟨11, 60, 3074⟩
private def endpoint_11_60_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_11_60_base : receiptBase endpoint_11_60_flag endpoint_11_60_sources = some 247826349917415147 := by decide +kernel
private theorem endpoint_11_60_w0 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 2 247826349917415147 = some 247826349917415147 := by decide +kernel
private theorem endpoint_11_60_w2 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 2 2 247826349917415147 = some 247826349917415147 := by decide +kernel
private theorem endpoint_11_60_p4 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 4 247826349917415147 = some 247826349917415147 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 2 2 247826349917415147 247826349917415147 247826349917415147 endpoint_11_60_w0 endpoint_11_60_w2
private theorem endpoint_11_60_w4 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 4 2 247826349917415147 = some 247826349917415147 := by decide +kernel
private theorem endpoint_11_60_p6 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 6 247826349917415147 = some 247826349917415147 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 4 2 247826349917415147 247826349917415147 247826349917415147 endpoint_11_60_p4 endpoint_11_60_w4
private theorem endpoint_11_60_w6 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 6 2 247826349917415147 = some 247826349917415147 := by decide +kernel
private theorem endpoint_11_60_p8 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 8 247826349917415147 = some 247826349917415147 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 6 2 247826349917415147 247826349917415147 247826349917415147 endpoint_11_60_p6 endpoint_11_60_w6
private theorem endpoint_11_60_w8 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 8 2 247826349917415147 = some 247826349917415147 := by decide +kernel
private theorem endpoint_11_60_p10 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 10 247826349917415147 = some 247826349917415147 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 8 2 247826349917415147 247826349917415147 247826349917415147 endpoint_11_60_p8 endpoint_11_60_w8
def endpoint_11_60 : CertifiedEndpoint :=
  ⟨⟨11, 60, 3074⟩, 247826349917415147, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_11_60_flag endpoint_11_60_sources 10 247826349917415147 247826349917415147 rfl endpoint_11_60_base endpoint_11_60_p10) (by decide)⟩
private def endpoint_11_61_flag : Flag := ⟨11, 61, 3032⟩
private def endpoint_11_61_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_11_61_base : receiptBase endpoint_11_61_flag endpoint_11_61_sources = some 248045355862313244 := by decide +kernel
private theorem endpoint_11_61_w0 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 2 248045355862313244 = some 248045355862313244 := by decide +kernel
private theorem endpoint_11_61_w2 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 2 2 248045355862313244 = some 248045355862313244 := by decide +kernel
private theorem endpoint_11_61_p4 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 4 248045355862313244 = some 248045355862313244 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 2 2 248045355862313244 248045355862313244 248045355862313244 endpoint_11_61_w0 endpoint_11_61_w2
private theorem endpoint_11_61_w4 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 4 2 248045355862313244 = some 248045355862313244 := by decide +kernel
private theorem endpoint_11_61_p6 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 6 248045355862313244 = some 248045355862313244 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 4 2 248045355862313244 248045355862313244 248045355862313244 endpoint_11_61_p4 endpoint_11_61_w4
private theorem endpoint_11_61_w6 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 6 2 248045355862313244 = some 248045355862313244 := by decide +kernel
private theorem endpoint_11_61_p8 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 8 248045355862313244 = some 248045355862313244 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 6 2 248045355862313244 248045355862313244 248045355862313244 endpoint_11_61_p6 endpoint_11_61_w6
private theorem endpoint_11_61_w8 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 8 2 248045355862313244 = some 248045355862313244 := by decide +kernel
private theorem endpoint_11_61_p10 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 10 248045355862313244 = some 248045355862313244 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 8 2 248045355862313244 248045355862313244 248045355862313244 endpoint_11_61_p8 endpoint_11_61_w8
def endpoint_11_61 : CertifiedEndpoint :=
  ⟨⟨11, 61, 3032⟩, 248045355862313244, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_11_61_flag endpoint_11_61_sources 10 248045355862313244 248045355862313244 rfl endpoint_11_61_base endpoint_11_61_p10) (by decide)⟩
private def endpoint_11_62_flag : Flag := ⟨11, 62, 2987⟩
private def endpoint_11_62_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_11_62_base : receiptBase endpoint_11_62_flag endpoint_11_62_sources = some 249117197431754252 := by decide +kernel
private theorem endpoint_11_62_w0 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 2 249117197431754252 = some 249117197431754252 := by decide +kernel
private theorem endpoint_11_62_w2 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 2 2 249117197431754252 = some 249117197431754252 := by decide +kernel
private theorem endpoint_11_62_p4 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 4 249117197431754252 = some 249117197431754252 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 2 2 249117197431754252 249117197431754252 249117197431754252 endpoint_11_62_w0 endpoint_11_62_w2
private theorem endpoint_11_62_w4 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 4 2 249117197431754252 = some 249117197431754252 := by decide +kernel
private theorem endpoint_11_62_p6 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 6 249117197431754252 = some 249117197431754252 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 4 2 249117197431754252 249117197431754252 249117197431754252 endpoint_11_62_p4 endpoint_11_62_w4
private theorem endpoint_11_62_w6 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 6 2 249117197431754252 = some 249117197431754252 := by decide +kernel
private theorem endpoint_11_62_p8 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 8 249117197431754252 = some 249117197431754252 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 6 2 249117197431754252 249117197431754252 249117197431754252 endpoint_11_62_p6 endpoint_11_62_w6
private theorem endpoint_11_62_w8 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 8 2 249117197431754252 = some 249117197431754252 := by decide +kernel
private theorem endpoint_11_62_p10 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 10 249117197431754252 = some 249117197431754252 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 8 2 249117197431754252 249117197431754252 249117197431754252 endpoint_11_62_p8 endpoint_11_62_w8
def endpoint_11_62 : CertifiedEndpoint :=
  ⟨⟨11, 62, 2987⟩, 249117197431754252, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_11_62_flag endpoint_11_62_sources 10 249117197431754252 249117197431754252 rfl endpoint_11_62_base endpoint_11_62_p10) (by decide)⟩
private def endpoint_11_63_flag : Flag := ⟨11, 63, 2941⟩
private def endpoint_11_63_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_11_63_base : receiptBase endpoint_11_63_flag endpoint_11_63_sources = some 248804056095855817 := by decide +kernel
private theorem endpoint_11_63_w0 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 2 248804056095855817 = some 248804056095855817 := by decide +kernel
private theorem endpoint_11_63_w2 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 2 2 248804056095855817 = some 248804056095855817 := by decide +kernel
private theorem endpoint_11_63_p4 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 4 248804056095855817 = some 248804056095855817 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 2 2 248804056095855817 248804056095855817 248804056095855817 endpoint_11_63_w0 endpoint_11_63_w2
private theorem endpoint_11_63_w4 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 4 2 248804056095855817 = some 248804056095855817 := by decide +kernel
private theorem endpoint_11_63_p6 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 6 248804056095855817 = some 248804056095855817 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 4 2 248804056095855817 248804056095855817 248804056095855817 endpoint_11_63_p4 endpoint_11_63_w4
private theorem endpoint_11_63_w6 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 6 2 248804056095855817 = some 248804056095855817 := by decide +kernel
private theorem endpoint_11_63_p8 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 8 248804056095855817 = some 248804056095855817 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 6 2 248804056095855817 248804056095855817 248804056095855817 endpoint_11_63_p6 endpoint_11_63_w6
private theorem endpoint_11_63_w8 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 8 2 248804056095855817 = some 248804056095855817 := by decide +kernel
private theorem endpoint_11_63_p10 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 10 248804056095855817 = some 248804056095855817 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 8 2 248804056095855817 248804056095855817 248804056095855817 endpoint_11_63_p8 endpoint_11_63_w8
def endpoint_11_63 : CertifiedEndpoint :=
  ⟨⟨11, 63, 2941⟩, 248804056095855817, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_11_63_flag endpoint_11_63_sources 10 248804056095855817 248804056095855817 rfl endpoint_11_63_base endpoint_11_63_p10) (by decide)⟩
private def endpoint_11_64_flag : Flag := ⟨11, 64, 2893⟩
private def endpoint_11_64_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_11_64_base : receiptBase endpoint_11_64_flag endpoint_11_64_sources = some 249461359710790637 := by decide +kernel
private theorem endpoint_11_64_w0 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 2 249461359710790637 = some 249461359710790637 := by decide +kernel
private theorem endpoint_11_64_w2 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 2 2 249461359710790637 = some 249461359710790637 := by decide +kernel
private theorem endpoint_11_64_p4 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 4 249461359710790637 = some 249461359710790637 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 2 2 249461359710790637 249461359710790637 249461359710790637 endpoint_11_64_w0 endpoint_11_64_w2
private theorem endpoint_11_64_w4 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 4 2 249461359710790637 = some 249461359710790637 := by decide +kernel
private theorem endpoint_11_64_p6 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 6 249461359710790637 = some 249461359710790637 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 4 2 249461359710790637 249461359710790637 249461359710790637 endpoint_11_64_p4 endpoint_11_64_w4
private theorem endpoint_11_64_w6 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 6 2 249461359710790637 = some 249461359710790637 := by decide +kernel
private theorem endpoint_11_64_p8 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 8 249461359710790637 = some 249461359710790637 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 6 2 249461359710790637 249461359710790637 249461359710790637 endpoint_11_64_p6 endpoint_11_64_w6
private theorem endpoint_11_64_w8 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 8 2 249461359710790637 = some 249461359710790637 := by decide +kernel
private theorem endpoint_11_64_p10 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 10 249461359710790637 = some 249461359710790637 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 8 2 249461359710790637 249461359710790637 249461359710790637 endpoint_11_64_p8 endpoint_11_64_w8
def endpoint_11_64 : CertifiedEndpoint :=
  ⟨⟨11, 64, 2893⟩, 249461359710790637, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_11_64_flag endpoint_11_64_sources 10 249461359710790637 249461359710790637 rfl endpoint_11_64_base endpoint_11_64_p10) (by decide)⟩
private def endpoint_11_65_flag : Flag := ⟨11, 65, 2842⟩
private def endpoint_11_65_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_11_65_base : receiptBase endpoint_11_65_flag endpoint_11_65_sources = some 249784183408963766 := by decide +kernel
private theorem endpoint_11_65_w0 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 2 249784183408963766 = some 249784183408963766 := by decide +kernel
private theorem endpoint_11_65_w2 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 2 2 249784183408963766 = some 249784183408963766 := by decide +kernel
private theorem endpoint_11_65_p4 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 4 249784183408963766 = some 249784183408963766 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 2 2 249784183408963766 249784183408963766 249784183408963766 endpoint_11_65_w0 endpoint_11_65_w2
private theorem endpoint_11_65_w4 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 4 2 249784183408963766 = some 249784183408963766 := by decide +kernel
private theorem endpoint_11_65_p6 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 6 249784183408963766 = some 249784183408963766 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 4 2 249784183408963766 249784183408963766 249784183408963766 endpoint_11_65_p4 endpoint_11_65_w4
private theorem endpoint_11_65_w6 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 6 2 249784183408963766 = some 249784183408963766 := by decide +kernel
private theorem endpoint_11_65_p8 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 8 249784183408963766 = some 249784183408963766 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 6 2 249784183408963766 249784183408963766 249784183408963766 endpoint_11_65_p6 endpoint_11_65_w6
private theorem endpoint_11_65_w8 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 8 2 249784183408963766 = some 249784183408963766 := by decide +kernel
private theorem endpoint_11_65_p10 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 10 249784183408963766 = some 249784183408963766 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 8 2 249784183408963766 249784183408963766 249784183408963766 endpoint_11_65_p8 endpoint_11_65_w8
def endpoint_11_65 : CertifiedEndpoint :=
  ⟨⟨11, 65, 2842⟩, 249784183408963766, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_11_65_flag endpoint_11_65_sources 10 249784183408963766 249784183408963766 rfl endpoint_11_65_base endpoint_11_65_p10) (by decide)⟩
private def endpoint_11_66_flag : Flag := ⟨11, 66, 2789⟩
private def endpoint_11_66_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_66_base : receiptBase endpoint_11_66_flag endpoint_11_66_sources = some 249689190847708344 := by decide +kernel
private theorem endpoint_11_66_w0 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 2 249689190847708344 = some 249689190847708344 := by decide +kernel
private theorem endpoint_11_66_w2 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 2 2 249689190847708344 = some 249689190847708344 := by decide +kernel
private theorem endpoint_11_66_p4 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 4 249689190847708344 = some 249689190847708344 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 2 2 249689190847708344 249689190847708344 249689190847708344 endpoint_11_66_w0 endpoint_11_66_w2
private theorem endpoint_11_66_w4 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 4 2 249689190847708344 = some 249689190847708344 := by decide +kernel
private theorem endpoint_11_66_p6 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 6 249689190847708344 = some 249689190847708344 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 4 2 249689190847708344 249689190847708344 249689190847708344 endpoint_11_66_p4 endpoint_11_66_w4
private theorem endpoint_11_66_w6 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 6 2 249689190847708344 = some 249689190847708344 := by decide +kernel
private theorem endpoint_11_66_p8 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 8 249689190847708344 = some 249689190847708344 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 6 2 249689190847708344 249689190847708344 249689190847708344 endpoint_11_66_p6 endpoint_11_66_w6
private theorem endpoint_11_66_w8 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 8 2 249689190847708344 = some 249689190847708344 := by decide +kernel
private theorem endpoint_11_66_p10 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 10 249689190847708344 = some 249689190847708344 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 8 2 249689190847708344 249689190847708344 249689190847708344 endpoint_11_66_p8 endpoint_11_66_w8
def endpoint_11_66 : CertifiedEndpoint :=
  ⟨⟨11, 66, 2789⟩, 249689190847708344, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_66_flag endpoint_11_66_sources 10 249689190847708344 249689190847708344 rfl endpoint_11_66_base endpoint_11_66_p10) (by decide)⟩
private def endpoint_11_67_flag : Flag := ⟨11, 67, 2733⟩
private def endpoint_11_67_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_67_base : receiptBase endpoint_11_67_flag endpoint_11_67_sources = some 248022523835865383 := by decide +kernel
private theorem endpoint_11_67_w0 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 2 248022523835865383 = some 248022523835865383 := by decide +kernel
private theorem endpoint_11_67_w2 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 2 2 248022523835865383 = some 248022523835865383 := by decide +kernel
private theorem endpoint_11_67_p4 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 4 248022523835865383 = some 248022523835865383 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 2 2 248022523835865383 248022523835865383 248022523835865383 endpoint_11_67_w0 endpoint_11_67_w2
private theorem endpoint_11_67_w4 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 4 2 248022523835865383 = some 248022523835865383 := by decide +kernel
private theorem endpoint_11_67_p6 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 6 248022523835865383 = some 248022523835865383 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 4 2 248022523835865383 248022523835865383 248022523835865383 endpoint_11_67_p4 endpoint_11_67_w4
private theorem endpoint_11_67_w6 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 6 2 248022523835865383 = some 248022523835865383 := by decide +kernel
private theorem endpoint_11_67_p8 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 8 248022523835865383 = some 248022523835865383 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 6 2 248022523835865383 248022523835865383 248022523835865383 endpoint_11_67_p6 endpoint_11_67_w6
private theorem endpoint_11_67_w8 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 8 2 248022523835865383 = some 248022523835865383 := by decide +kernel
private theorem endpoint_11_67_p10 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 10 248022523835865383 = some 248022523835865383 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 8 2 248022523835865383 248022523835865383 248022523835865383 endpoint_11_67_p8 endpoint_11_67_w8
def endpoint_11_67 : CertifiedEndpoint :=
  ⟨⟨11, 67, 2733⟩, 248022523835865383, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_67_flag endpoint_11_67_sources 10 248022523835865383 248022523835865383 rfl endpoint_11_67_base endpoint_11_67_p10) (by decide)⟩
private def endpoint_11_68_flag : Flag := ⟨11, 68, 2675⟩
private def endpoint_11_68_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_68_base : receiptBase endpoint_11_68_flag endpoint_11_68_sources = some 246038069469297952 := by decide +kernel
private theorem endpoint_11_68_w0 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 2 246038069469297952 = some 246038069469297952 := by decide +kernel
private theorem endpoint_11_68_w2 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 2 2 246038069469297952 = some 246038069469297952 := by decide +kernel
private theorem endpoint_11_68_p4 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 4 246038069469297952 = some 246038069469297952 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 2 2 246038069469297952 246038069469297952 246038069469297952 endpoint_11_68_w0 endpoint_11_68_w2
private theorem endpoint_11_68_w4 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 4 2 246038069469297952 = some 246038069469297952 := by decide +kernel
private theorem endpoint_11_68_p6 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 6 246038069469297952 = some 246038069469297952 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 4 2 246038069469297952 246038069469297952 246038069469297952 endpoint_11_68_p4 endpoint_11_68_w4
private theorem endpoint_11_68_w6 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 6 2 246038069469297952 = some 246038069469297952 := by decide +kernel
private theorem endpoint_11_68_p8 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 8 246038069469297952 = some 246038069469297952 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 6 2 246038069469297952 246038069469297952 246038069469297952 endpoint_11_68_p6 endpoint_11_68_w6
private theorem endpoint_11_68_w8 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 8 2 246038069469297952 = some 246038069469297952 := by decide +kernel
private theorem endpoint_11_68_p10 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 10 246038069469297952 = some 246038069469297952 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 8 2 246038069469297952 246038069469297952 246038069469297952 endpoint_11_68_p8 endpoint_11_68_w8
def endpoint_11_68 : CertifiedEndpoint :=
  ⟨⟨11, 68, 2675⟩, 246038069469297952, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_68_flag endpoint_11_68_sources 10 246038069469297952 246038069469297952 rfl endpoint_11_68_base endpoint_11_68_p10) (by decide)⟩
private def endpoint_11_69_flag : Flag := ⟨11, 69, 2615⟩
private def endpoint_11_69_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_69_base : receiptBase endpoint_11_69_flag endpoint_11_69_sources = some 243728616104347929 := by decide +kernel
private theorem endpoint_11_69_w0 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 2 243728616104347929 = some 243728616104347929 := by decide +kernel
private theorem endpoint_11_69_w2 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 2 2 243728616104347929 = some 243728616104347929 := by decide +kernel
private theorem endpoint_11_69_p4 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 4 243728616104347929 = some 243728616104347929 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 2 2 243728616104347929 243728616104347929 243728616104347929 endpoint_11_69_w0 endpoint_11_69_w2
private theorem endpoint_11_69_w4 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 4 2 243728616104347929 = some 243728616104347929 := by decide +kernel
private theorem endpoint_11_69_p6 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 6 243728616104347929 = some 243728616104347929 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 4 2 243728616104347929 243728616104347929 243728616104347929 endpoint_11_69_p4 endpoint_11_69_w4
private theorem endpoint_11_69_w6 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 6 2 243728616104347929 = some 243728616104347929 := by decide +kernel
private theorem endpoint_11_69_p8 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 8 243728616104347929 = some 243728616104347929 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 6 2 243728616104347929 243728616104347929 243728616104347929 endpoint_11_69_p6 endpoint_11_69_w6
private theorem endpoint_11_69_w8 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 8 2 243728616104347929 = some 243728616104347929 := by decide +kernel
private theorem endpoint_11_69_p10 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 10 243728616104347929 = some 243728616104347929 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 8 2 243728616104347929 243728616104347929 243728616104347929 endpoint_11_69_p8 endpoint_11_69_w8
def endpoint_11_69 : CertifiedEndpoint :=
  ⟨⟨11, 69, 2615⟩, 243728616104347929, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_69_flag endpoint_11_69_sources 10 243728616104347929 243728616104347929 rfl endpoint_11_69_base endpoint_11_69_p10) (by decide)⟩
private def endpoint_11_70_flag : Flag := ⟨11, 70, 2552⟩
private def endpoint_11_70_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_11_70_base : receiptBase endpoint_11_70_flag endpoint_11_70_sources = some 246260820648272382 := by decide +kernel
private theorem endpoint_11_70_w0 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 2 246260820648272382 = some 246260820648272382 := by decide +kernel
private theorem endpoint_11_70_w2 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 2 2 246260820648272382 = some 246260820648272382 := by decide +kernel
private theorem endpoint_11_70_p4 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 4 246260820648272382 = some 246260820648272382 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 2 2 246260820648272382 246260820648272382 246260820648272382 endpoint_11_70_w0 endpoint_11_70_w2
private theorem endpoint_11_70_w4 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 4 2 246260820648272382 = some 246260820648272382 := by decide +kernel
private theorem endpoint_11_70_p6 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 6 246260820648272382 = some 246260820648272382 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 4 2 246260820648272382 246260820648272382 246260820648272382 endpoint_11_70_p4 endpoint_11_70_w4
private theorem endpoint_11_70_w6 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 6 2 246260820648272382 = some 246260820648272382 := by decide +kernel
private theorem endpoint_11_70_p8 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 8 246260820648272382 = some 246260820648272382 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 6 2 246260820648272382 246260820648272382 246260820648272382 endpoint_11_70_p6 endpoint_11_70_w6
private theorem endpoint_11_70_w8 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 8 2 246260820648272382 = some 246260820648272382 := by decide +kernel
private theorem endpoint_11_70_p10 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 10 246260820648272382 = some 246260820648272382 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 8 2 246260820648272382 246260820648272382 246260820648272382 endpoint_11_70_p8 endpoint_11_70_w8
def endpoint_11_70 : CertifiedEndpoint :=
  ⟨⟨11, 70, 2552⟩, 246260820648272382, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_11_70_flag endpoint_11_70_sources 10 246260820648272382 246260820648272382 rfl endpoint_11_70_base endpoint_11_70_p10) (by decide)⟩
private def endpoint_11_71_flag : Flag := ⟨11, 71, 2487⟩
private def endpoint_11_71_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_11_71_base : receiptBase endpoint_11_71_flag endpoint_11_71_sources = some 243154853269313050 := by decide +kernel
private theorem endpoint_11_71_w0 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 2 243154853269313050 = some 243154853269313050 := by decide +kernel
private theorem endpoint_11_71_w2 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 2 2 243154853269313050 = some 243154853269313050 := by decide +kernel
private theorem endpoint_11_71_p4 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 4 243154853269313050 = some 243154853269313050 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 2 2 243154853269313050 243154853269313050 243154853269313050 endpoint_11_71_w0 endpoint_11_71_w2
private theorem endpoint_11_71_w4 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 4 2 243154853269313050 = some 243154853269313050 := by decide +kernel
private theorem endpoint_11_71_p6 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 6 243154853269313050 = some 243154853269313050 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 4 2 243154853269313050 243154853269313050 243154853269313050 endpoint_11_71_p4 endpoint_11_71_w4
private theorem endpoint_11_71_w6 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 6 2 243154853269313050 = some 243154853269313050 := by decide +kernel
private theorem endpoint_11_71_p8 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 8 243154853269313050 = some 243154853269313050 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 6 2 243154853269313050 243154853269313050 243154853269313050 endpoint_11_71_p6 endpoint_11_71_w6
private theorem endpoint_11_71_w8 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 8 2 243154853269313050 = some 243154853269313050 := by decide +kernel
private theorem endpoint_11_71_p10 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 10 243154853269313050 = some 243154853269313050 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 8 2 243154853269313050 243154853269313050 243154853269313050 endpoint_11_71_p8 endpoint_11_71_w8
def endpoint_11_71 : CertifiedEndpoint :=
  ⟨⟨11, 71, 2487⟩, 243154853269313050, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_11_71_flag endpoint_11_71_sources 10 243154853269313050 243154853269313050 rfl endpoint_11_71_base endpoint_11_71_p10) (by decide)⟩
private def endpoint_11_72_flag : Flag := ⟨11, 72, 2419⟩
private def endpoint_11_72_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_11_72_base : receiptBase endpoint_11_72_flag endpoint_11_72_sources = some 239600351995117807 := by decide +kernel
private theorem endpoint_11_72_w0 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 2 239600351995117807 = some 239600351995117807 := by decide +kernel
private theorem endpoint_11_72_w2 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 2 2 239600351995117807 = some 239600351995117807 := by decide +kernel
private theorem endpoint_11_72_p4 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 4 239600351995117807 = some 239600351995117807 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 2 2 239600351995117807 239600351995117807 239600351995117807 endpoint_11_72_w0 endpoint_11_72_w2
private theorem endpoint_11_72_w4 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 4 2 239600351995117807 = some 239600351995117807 := by decide +kernel
private theorem endpoint_11_72_p6 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 6 239600351995117807 = some 239600351995117807 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 4 2 239600351995117807 239600351995117807 239600351995117807 endpoint_11_72_p4 endpoint_11_72_w4
private theorem endpoint_11_72_w6 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 6 2 239600351995117807 = some 239600351995117807 := by decide +kernel
private theorem endpoint_11_72_p8 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 8 239600351995117807 = some 239600351995117807 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 6 2 239600351995117807 239600351995117807 239600351995117807 endpoint_11_72_p6 endpoint_11_72_w6
private theorem endpoint_11_72_w8 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 8 2 239600351995117807 = some 239600351995117807 := by decide +kernel
private theorem endpoint_11_72_p10 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 10 239600351995117807 = some 239600351995117807 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 8 2 239600351995117807 239600351995117807 239600351995117807 endpoint_11_72_p8 endpoint_11_72_w8
def endpoint_11_72 : CertifiedEndpoint :=
  ⟨⟨11, 72, 2419⟩, 239600351995117807, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_11_72_flag endpoint_11_72_sources 10 239600351995117807 239600351995117807 rfl endpoint_11_72_base endpoint_11_72_p10) (by decide)⟩
private def endpoint_11_73_flag : Flag := ⟨11, 73, 2348⟩
private def endpoint_11_73_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_11_73_base : receiptBase endpoint_11_73_flag endpoint_11_73_sources = some 237406430996815246 := by decide +kernel
private theorem endpoint_11_73_w0 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 2 237406430996815246 = some 237406430996815246 := by decide +kernel
private theorem endpoint_11_73_w2 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 2 2 237406430996815246 = some 237406430996815246 := by decide +kernel
private theorem endpoint_11_73_p4 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 4 237406430996815246 = some 237406430996815246 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 2 2 237406430996815246 237406430996815246 237406430996815246 endpoint_11_73_w0 endpoint_11_73_w2
private theorem endpoint_11_73_w4 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 4 2 237406430996815246 = some 237406430996815246 := by decide +kernel
private theorem endpoint_11_73_p6 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 6 237406430996815246 = some 237406430996815246 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 4 2 237406430996815246 237406430996815246 237406430996815246 endpoint_11_73_p4 endpoint_11_73_w4
private theorem endpoint_11_73_w6 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 6 2 237406430996815246 = some 237406430996815246 := by decide +kernel
private theorem endpoint_11_73_p8 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 8 237406430996815246 = some 237406430996815246 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 6 2 237406430996815246 237406430996815246 237406430996815246 endpoint_11_73_p6 endpoint_11_73_w6
private theorem endpoint_11_73_w8 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 8 2 237406430996815246 = some 237406430996815246 := by decide +kernel
private theorem endpoint_11_73_p10 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 10 237406430996815246 = some 237406430996815246 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 8 2 237406430996815246 237406430996815246 237406430996815246 endpoint_11_73_p8 endpoint_11_73_w8
def endpoint_11_73 : CertifiedEndpoint :=
  ⟨⟨11, 73, 2348⟩, 237406430996815246, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_11_73_flag endpoint_11_73_sources 10 237406430996815246 237406430996815246 rfl endpoint_11_73_base endpoint_11_73_p10) (by decide)⟩
private def endpoint_11_74_flag : Flag := ⟨11, 74, 2275⟩
private def endpoint_11_74_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_11_74_base : receiptBase endpoint_11_74_flag endpoint_11_74_sources = some 232908494460625716 := by decide +kernel
private theorem endpoint_11_74_w0 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 2 232908494460625716 = some 232908494460625716 := by decide +kernel
private theorem endpoint_11_74_w2 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 2 2 232908494460625716 = some 232908494460625716 := by decide +kernel
private theorem endpoint_11_74_p4 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 4 232908494460625716 = some 232908494460625716 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 2 2 232908494460625716 232908494460625716 232908494460625716 endpoint_11_74_w0 endpoint_11_74_w2
private theorem endpoint_11_74_w4 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 4 2 232908494460625716 = some 232908494460625716 := by decide +kernel
private theorem endpoint_11_74_p6 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 6 232908494460625716 = some 232908494460625716 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 4 2 232908494460625716 232908494460625716 232908494460625716 endpoint_11_74_p4 endpoint_11_74_w4
private theorem endpoint_11_74_w6 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 6 2 232908494460625716 = some 232908494460625716 := by decide +kernel
private theorem endpoint_11_74_p8 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 8 232908494460625716 = some 232908494460625716 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 6 2 232908494460625716 232908494460625716 232908494460625716 endpoint_11_74_p6 endpoint_11_74_w6
private theorem endpoint_11_74_w8 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 8 2 232908494460625716 = some 232908494460625716 := by decide +kernel
private theorem endpoint_11_74_p10 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 10 232908494460625716 = some 232908494460625716 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 8 2 232908494460625716 232908494460625716 232908494460625716 endpoint_11_74_p8 endpoint_11_74_w8
def endpoint_11_74 : CertifiedEndpoint :=
  ⟨⟨11, 74, 2275⟩, 232908494460625716, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_11_74_flag endpoint_11_74_sources 10 232908494460625716 232908494460625716 rfl endpoint_11_74_base endpoint_11_74_p10) (by decide)⟩
private def endpoint_11_75_flag : Flag := ⟨11, 75, 2200⟩
private def endpoint_11_75_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_11_75_base : receiptBase endpoint_11_75_flag endpoint_11_75_sources = some 229908990544664854 := by decide +kernel
private theorem endpoint_11_75_w0 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 2 229908990544664854 = some 229908990544664854 := by decide +kernel
private theorem endpoint_11_75_w2 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 2 2 229908990544664854 = some 229908990544664854 := by decide +kernel
private theorem endpoint_11_75_p4 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 4 229908990544664854 = some 229908990544664854 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 2 2 229908990544664854 229908990544664854 229908990544664854 endpoint_11_75_w0 endpoint_11_75_w2
private theorem endpoint_11_75_w4 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 4 2 229908990544664854 = some 229908990544664854 := by decide +kernel
private theorem endpoint_11_75_p6 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 6 229908990544664854 = some 229908990544664854 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 4 2 229908990544664854 229908990544664854 229908990544664854 endpoint_11_75_p4 endpoint_11_75_w4
private theorem endpoint_11_75_w6 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 6 2 229908990544664854 = some 229908990544664854 := by decide +kernel
private theorem endpoint_11_75_p8 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 8 229908990544664854 = some 229908990544664854 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 6 2 229908990544664854 229908990544664854 229908990544664854 endpoint_11_75_p6 endpoint_11_75_w6
private theorem endpoint_11_75_w8 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 8 2 229908990544664854 = some 229908990544664854 := by decide +kernel
private theorem endpoint_11_75_p10 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 10 229908990544664854 = some 229908990544664854 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 8 2 229908990544664854 229908990544664854 229908990544664854 endpoint_11_75_p8 endpoint_11_75_w8
def endpoint_11_75 : CertifiedEndpoint :=
  ⟨⟨11, 75, 2200⟩, 229908990544664854, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_11_75_flag endpoint_11_75_sources 10 229908990544664854 229908990544664854 rfl endpoint_11_75_base endpoint_11_75_p10) (by decide)⟩
private def endpoint_11_76_flag : Flag := ⟨11, 76, 2122⟩
private def endpoint_11_76_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_11_76_base : receiptBase endpoint_11_76_flag endpoint_11_76_sources = some 224482453578892022 := by decide +kernel
private theorem endpoint_11_76_w0 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 2 224482453578892022 = some 224482453578892022 := by decide +kernel
private theorem endpoint_11_76_w2 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 2 2 224482453578892022 = some 224482453578892022 := by decide +kernel
private theorem endpoint_11_76_p4 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 4 224482453578892022 = some 224482453578892022 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 2 2 224482453578892022 224482453578892022 224482453578892022 endpoint_11_76_w0 endpoint_11_76_w2
private theorem endpoint_11_76_w4 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 4 2 224482453578892022 = some 224482453578892022 := by decide +kernel
private theorem endpoint_11_76_p6 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 6 224482453578892022 = some 224482453578892022 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 4 2 224482453578892022 224482453578892022 224482453578892022 endpoint_11_76_p4 endpoint_11_76_w4
private theorem endpoint_11_76_w6 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 6 2 224482453578892022 = some 224482453578892022 := by decide +kernel
private theorem endpoint_11_76_p8 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 8 224482453578892022 = some 224482453578892022 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 6 2 224482453578892022 224482453578892022 224482453578892022 endpoint_11_76_p6 endpoint_11_76_w6
private theorem endpoint_11_76_w8 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 8 2 224482453578892022 = some 224482453578892022 := by decide +kernel
private theorem endpoint_11_76_p10 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 10 224482453578892022 = some 224482453578892022 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 8 2 224482453578892022 224482453578892022 224482453578892022 endpoint_11_76_p8 endpoint_11_76_w8
def endpoint_11_76 : CertifiedEndpoint :=
  ⟨⟨11, 76, 2122⟩, 224482453578892022, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_11_76_flag endpoint_11_76_sources 10 224482453578892022 224482453578892022 rfl endpoint_11_76_base endpoint_11_76_p10) (by decide)⟩
private def endpoint_11_77_flag : Flag := ⟨11, 77, 2041⟩
private def endpoint_11_77_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_11_77_base : receiptBase endpoint_11_77_flag endpoint_11_77_sources = some 220469276117165080 := by decide +kernel
private theorem endpoint_11_77_w0 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 2 220469276117165080 = some 220469276117165080 := by decide +kernel
private theorem endpoint_11_77_w2 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 2 2 220469276117165080 = some 220469276117165080 := by decide +kernel
private theorem endpoint_11_77_p4 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 4 220469276117165080 = some 220469276117165080 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 2 2 220469276117165080 220469276117165080 220469276117165080 endpoint_11_77_w0 endpoint_11_77_w2
private theorem endpoint_11_77_w4 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 4 2 220469276117165080 = some 220469276117165080 := by decide +kernel
private theorem endpoint_11_77_p6 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 6 220469276117165080 = some 220469276117165080 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 4 2 220469276117165080 220469276117165080 220469276117165080 endpoint_11_77_p4 endpoint_11_77_w4
private theorem endpoint_11_77_w6 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 6 2 220469276117165080 = some 220469276117165080 := by decide +kernel
private theorem endpoint_11_77_p8 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 8 220469276117165080 = some 220469276117165080 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 6 2 220469276117165080 220469276117165080 220469276117165080 endpoint_11_77_p6 endpoint_11_77_w6
private theorem endpoint_11_77_w8 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 8 2 220469276117165080 = some 220469276117165080 := by decide +kernel
private theorem endpoint_11_77_p10 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 10 220469276117165080 = some 220469276117165080 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 8 2 220469276117165080 220469276117165080 220469276117165080 endpoint_11_77_p8 endpoint_11_77_w8
def endpoint_11_77 : CertifiedEndpoint :=
  ⟨⟨11, 77, 2041⟩, 220469276117165080, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_11_77_flag endpoint_11_77_sources 10 220469276117165080 220469276117165080 rfl endpoint_11_77_base endpoint_11_77_p10) (by decide)⟩
private def endpoint_11_78_flag : Flag := ⟨11, 78, 1958⟩
private def endpoint_11_78_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_11_78_base : receiptBase endpoint_11_78_flag endpoint_11_78_sources = some 214028465069551436 := by decide +kernel
private theorem endpoint_11_78_w0 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 2 214028465069551436 = some 214028465069551436 := by decide +kernel
private theorem endpoint_11_78_w2 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 2 2 214028465069551436 = some 214028465069551436 := by decide +kernel
private theorem endpoint_11_78_p4 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 4 214028465069551436 = some 214028465069551436 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 2 2 214028465069551436 214028465069551436 214028465069551436 endpoint_11_78_w0 endpoint_11_78_w2
private theorem endpoint_11_78_w4 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 4 2 214028465069551436 = some 214028465069551436 := by decide +kernel
private theorem endpoint_11_78_p6 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 6 214028465069551436 = some 214028465069551436 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 4 2 214028465069551436 214028465069551436 214028465069551436 endpoint_11_78_p4 endpoint_11_78_w4
private theorem endpoint_11_78_w6 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 6 2 214028465069551436 = some 214028465069551436 := by decide +kernel
private theorem endpoint_11_78_p8 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 8 214028465069551436 = some 214028465069551436 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 6 2 214028465069551436 214028465069551436 214028465069551436 endpoint_11_78_p6 endpoint_11_78_w6
private theorem endpoint_11_78_w8 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 8 2 214028465069551436 = some 214028465069551436 := by decide +kernel
private theorem endpoint_11_78_p10 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 10 214028465069551436 = some 214028465069551436 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 8 2 214028465069551436 214028465069551436 214028465069551436 endpoint_11_78_p8 endpoint_11_78_w8
def endpoint_11_78 : CertifiedEndpoint :=
  ⟨⟨11, 78, 1958⟩, 214028465069551436, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_11_78_flag endpoint_11_78_sources 10 214028465069551436 214028465069551436 rfl endpoint_11_78_base endpoint_11_78_p10) (by decide)⟩
private def endpoint_11_79_flag : Flag := ⟨11, 79, 1872⟩
private def endpoint_11_79_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_11_79_base : receiptBase endpoint_11_79_flag endpoint_11_79_sources = some 207050231837827420 := by decide +kernel
private theorem endpoint_11_79_w0 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 2 207050231837827420 = some 207050231837827420 := by decide +kernel
private theorem endpoint_11_79_w2 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 2 2 207050231837827420 = some 207050231837827420 := by decide +kernel
private theorem endpoint_11_79_p4 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 4 207050231837827420 = some 207050231837827420 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 2 2 207050231837827420 207050231837827420 207050231837827420 endpoint_11_79_w0 endpoint_11_79_w2
private theorem endpoint_11_79_w4 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 4 2 207050231837827420 = some 207050231837827420 := by decide +kernel
private theorem endpoint_11_79_p6 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 6 207050231837827420 = some 207050231837827420 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 4 2 207050231837827420 207050231837827420 207050231837827420 endpoint_11_79_p4 endpoint_11_79_w4
private theorem endpoint_11_79_w6 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 6 2 207050231837827420 = some 207050231837827420 := by decide +kernel
private theorem endpoint_11_79_p8 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 8 207050231837827420 = some 207050231837827420 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 6 2 207050231837827420 207050231837827420 207050231837827420 endpoint_11_79_p6 endpoint_11_79_w6
private theorem endpoint_11_79_w8 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 8 2 207050231837827420 = some 207050231837827420 := by decide +kernel
private theorem endpoint_11_79_p10 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 10 207050231837827420 = some 207050231837827420 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 8 2 207050231837827420 207050231837827420 207050231837827420 endpoint_11_79_p8 endpoint_11_79_w8
def endpoint_11_79 : CertifiedEndpoint :=
  ⟨⟨11, 79, 1872⟩, 207050231837827420, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_11_79_flag endpoint_11_79_sources 10 207050231837827420 207050231837827420 rfl endpoint_11_79_base endpoint_11_79_p10) (by decide)⟩
private def endpoint_11_80_flag : Flag := ⟨11, 80, 1784⟩
private def endpoint_11_80_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_11_80_base : receiptBase endpoint_11_80_flag endpoint_11_80_sources = some 203337935250973023 := by decide +kernel
private theorem endpoint_11_80_w0 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 2 203337935250973023 = some 203337935250973023 := by decide +kernel
private theorem endpoint_11_80_w2 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 2 2 203337935250973023 = some 203337935250973023 := by decide +kernel
private theorem endpoint_11_80_p4 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 4 203337935250973023 = some 203337935250973023 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 2 2 203337935250973023 203337935250973023 203337935250973023 endpoint_11_80_w0 endpoint_11_80_w2
private theorem endpoint_11_80_w4 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 4 2 203337935250973023 = some 203337935250973023 := by decide +kernel
private theorem endpoint_11_80_p6 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 6 203337935250973023 = some 203337935250973023 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 4 2 203337935250973023 203337935250973023 203337935250973023 endpoint_11_80_p4 endpoint_11_80_w4
private theorem endpoint_11_80_w6 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 6 2 203337935250973023 = some 203337935250973023 := by decide +kernel
private theorem endpoint_11_80_p8 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 8 203337935250973023 = some 203337935250973023 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 6 2 203337935250973023 203337935250973023 203337935250973023 endpoint_11_80_p6 endpoint_11_80_w6
private theorem endpoint_11_80_w8 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 8 2 203337935250973023 = some 203337935250973023 := by decide +kernel
private theorem endpoint_11_80_p10 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 10 203337935250973023 = some 203337935250973023 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 8 2 203337935250973023 203337935250973023 203337935250973023 endpoint_11_80_p8 endpoint_11_80_w8
def endpoint_11_80 : CertifiedEndpoint :=
  ⟨⟨11, 80, 1784⟩, 203337935250973023, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_11_80_flag endpoint_11_80_sources 10 203337935250973023 203337935250973023 rfl endpoint_11_80_base endpoint_11_80_p10) (by decide)⟩
private def endpoint_11_81_flag : Flag := ⟨11, 81, 1693⟩
private def endpoint_11_81_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_11_81_base : receiptBase endpoint_11_81_flag endpoint_11_81_sources = some 195166890267422950 := by decide +kernel
private theorem endpoint_11_81_w0 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 2 195166890267422950 = some 195166890267422950 := by decide +kernel
private theorem endpoint_11_81_w2 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 2 2 195166890267422950 = some 195166890267422950 := by decide +kernel
private theorem endpoint_11_81_p4 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 4 195166890267422950 = some 195166890267422950 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 2 2 195166890267422950 195166890267422950 195166890267422950 endpoint_11_81_w0 endpoint_11_81_w2
private theorem endpoint_11_81_w4 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 4 2 195166890267422950 = some 195166890267422950 := by decide +kernel
private theorem endpoint_11_81_p6 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 6 195166890267422950 = some 195166890267422950 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 4 2 195166890267422950 195166890267422950 195166890267422950 endpoint_11_81_p4 endpoint_11_81_w4
private theorem endpoint_11_81_w6 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 6 2 195166890267422950 = some 195166890267422950 := by decide +kernel
private theorem endpoint_11_81_p8 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 8 195166890267422950 = some 195166890267422950 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 6 2 195166890267422950 195166890267422950 195166890267422950 endpoint_11_81_p6 endpoint_11_81_w6
private theorem endpoint_11_81_w8 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 8 2 195166890267422950 = some 195166890267422950 := by decide +kernel
private theorem endpoint_11_81_p10 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 10 195166890267422950 = some 195166890267422950 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 8 2 195166890267422950 195166890267422950 195166890267422950 endpoint_11_81_p8 endpoint_11_81_w8
def endpoint_11_81 : CertifiedEndpoint :=
  ⟨⟨11, 81, 1693⟩, 195166890267422950, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_11_81_flag endpoint_11_81_sources 10 195166890267422950 195166890267422950 rfl endpoint_11_81_base endpoint_11_81_p10) (by decide)⟩

def endpointBlock07 : List CertifiedEndpoint := [
  endpoint_10_38, endpoint_10_39, endpoint_10_40, endpoint_10_41, endpoint_10_42, endpoint_10_43, endpoint_10_44,
  endpoint_10_45, endpoint_10_46, endpoint_10_47, endpoint_10_48, endpoint_10_49, endpoint_10_50, endpoint_10_51,
  endpoint_10_52, endpoint_10_53, endpoint_10_54, endpoint_10_55, endpoint_10_56, endpoint_10_57, endpoint_10_58,
  endpoint_10_59, endpoint_10_60, endpoint_10_61, endpoint_10_62, endpoint_10_63, endpoint_10_64, endpoint_10_65,
  endpoint_10_66, endpoint_10_67, endpoint_10_68, endpoint_10_69, endpoint_10_70, endpoint_10_71, endpoint_10_72,
  endpoint_10_73, endpoint_10_74, endpoint_10_75, endpoint_10_76, endpoint_10_77, endpoint_10_78, endpoint_10_79,
  endpoint_10_80, endpoint_10_81, endpoint_10_82, endpoint_10_83, endpoint_10_84, endpoint_10_85, endpoint_10_86,
  endpoint_10_87, endpoint_10_88, endpoint_10_89, endpoint_10_90, endpoint_10_91, endpoint_10_92, endpoint_10_93,
  endpoint_10_94, endpoint_10_95, endpoint_10_96, endpoint_11_11, endpoint_11_12, endpoint_11_13, endpoint_11_14,
  endpoint_11_15, endpoint_11_16, endpoint_11_17, endpoint_11_18, endpoint_11_19, endpoint_11_20, endpoint_11_21,
  endpoint_11_22, endpoint_11_23, endpoint_11_24, endpoint_11_25, endpoint_11_26, endpoint_11_27, endpoint_11_28,
  endpoint_11_29, endpoint_11_30, endpoint_11_31, endpoint_11_32, endpoint_11_33, endpoint_11_34, endpoint_11_35,
  endpoint_11_36, endpoint_11_37, endpoint_11_38, endpoint_11_39, endpoint_11_40, endpoint_11_41, endpoint_11_42,
  endpoint_11_43, endpoint_11_44, endpoint_11_45, endpoint_11_46, endpoint_11_47, endpoint_11_48, endpoint_11_49,
  endpoint_11_50, endpoint_11_51, endpoint_11_52, endpoint_11_53, endpoint_11_54, endpoint_11_55, endpoint_11_56,
  endpoint_11_57, endpoint_11_58, endpoint_11_59, endpoint_11_60, endpoint_11_61, endpoint_11_62, endpoint_11_63,
  endpoint_11_64, endpoint_11_65, endpoint_11_66, endpoint_11_67, endpoint_11_68, endpoint_11_69, endpoint_11_70,
  endpoint_11_71, endpoint_11_72, endpoint_11_73, endpoint_11_74, endpoint_11_75, endpoint_11_76, endpoint_11_77,
  endpoint_11_78, endpoint_11_79, endpoint_11_80, endpoint_11_81
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
