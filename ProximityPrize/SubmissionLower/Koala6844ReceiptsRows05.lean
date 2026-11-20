import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_7_51_flag : Flag := ⟨7, 51, 3786⟩
private def endpoint_7_51_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_51_base : receiptBase endpoint_7_51_flag endpoint_7_51_sources = some 194015041973147334 := by decide +kernel
private theorem endpoint_7_51_w0 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 0 2 194015041973147334 = some 194015041973147334 := by decide +kernel
private theorem endpoint_7_51_w2 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 2 2 194015041973147334 = some 194015041973147334 := by decide +kernel
private theorem endpoint_7_51_p4 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 0 4 194015041973147334 = some 194015041973147334 :=
  join_receipt_window endpoint_7_51_flag endpoint_7_51_sources 0 2 2 194015041973147334 194015041973147334 194015041973147334 endpoint_7_51_w0 endpoint_7_51_w2
private theorem endpoint_7_51_w4 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 4 2 194015041973147334 = some 194015041973147334 := by decide +kernel
private theorem endpoint_7_51_p6 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 0 6 194015041973147334 = some 194015041973147334 :=
  join_receipt_window endpoint_7_51_flag endpoint_7_51_sources 0 4 2 194015041973147334 194015041973147334 194015041973147334 endpoint_7_51_p4 endpoint_7_51_w4
def endpoint_7_51 : CertifiedEndpoint :=
  ⟨⟨7, 51, 3786⟩, 194015041973147334, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_51_flag endpoint_7_51_sources 6 194015041973147334 194015041973147334 rfl endpoint_7_51_base endpoint_7_51_p6) (by decide)⟩
private def endpoint_7_52_flag : Flag := ⟨7, 52, 3756⟩
private def endpoint_7_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_52_base : receiptBase endpoint_7_52_flag endpoint_7_52_sources = some 197014822912038400 := by decide +kernel
private theorem endpoint_7_52_w0 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 0 2 197014822912038400 = some 197014822912038400 := by decide +kernel
private theorem endpoint_7_52_w2 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 2 2 197014822912038400 = some 197014822912038400 := by decide +kernel
private theorem endpoint_7_52_p4 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 0 4 197014822912038400 = some 197014822912038400 :=
  join_receipt_window endpoint_7_52_flag endpoint_7_52_sources 0 2 2 197014822912038400 197014822912038400 197014822912038400 endpoint_7_52_w0 endpoint_7_52_w2
private theorem endpoint_7_52_w4 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 4 2 197014822912038400 = some 197014822912038400 := by decide +kernel
private theorem endpoint_7_52_p6 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 0 6 197014822912038400 = some 197014822912038400 :=
  join_receipt_window endpoint_7_52_flag endpoint_7_52_sources 0 4 2 197014822912038400 197014822912038400 197014822912038400 endpoint_7_52_p4 endpoint_7_52_w4
def endpoint_7_52 : CertifiedEndpoint :=
  ⟨⟨7, 52, 3756⟩, 197014822912038400, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_52_flag endpoint_7_52_sources 6 197014822912038400 197014822912038400 rfl endpoint_7_52_base endpoint_7_52_p6) (by decide)⟩
private def endpoint_7_53_flag : Flag := ⟨7, 53, 3726⟩
private def endpoint_7_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_53_base : receiptBase endpoint_7_53_flag endpoint_7_53_sources = some 198739818450084635 := by decide +kernel
private theorem endpoint_7_53_w0 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 0 2 198739818450084635 = some 198739818450084635 := by decide +kernel
private theorem endpoint_7_53_w2 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 2 2 198739818450084635 = some 198739818450084635 := by decide +kernel
private theorem endpoint_7_53_p4 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 0 4 198739818450084635 = some 198739818450084635 :=
  join_receipt_window endpoint_7_53_flag endpoint_7_53_sources 0 2 2 198739818450084635 198739818450084635 198739818450084635 endpoint_7_53_w0 endpoint_7_53_w2
private theorem endpoint_7_53_w4 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 4 2 198739818450084635 = some 198739818450084635 := by decide +kernel
private theorem endpoint_7_53_p6 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 0 6 198739818450084635 = some 198739818450084635 :=
  join_receipt_window endpoint_7_53_flag endpoint_7_53_sources 0 4 2 198739818450084635 198739818450084635 198739818450084635 endpoint_7_53_p4 endpoint_7_53_w4
def endpoint_7_53 : CertifiedEndpoint :=
  ⟨⟨7, 53, 3726⟩, 198739818450084635, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_53_flag endpoint_7_53_sources 6 198739818450084635 198739818450084635 rfl endpoint_7_53_base endpoint_7_53_p6) (by decide)⟩
private def endpoint_7_54_flag : Flag := ⟨7, 54, 3696⟩
private def endpoint_7_54_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_54_base : receiptBase endpoint_7_54_flag endpoint_7_54_sources = some 200411557176317747 := by decide +kernel
private theorem endpoint_7_54_w0 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 0 2 200411557176317747 = some 200411557176317747 := by decide +kernel
private theorem endpoint_7_54_w2 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 2 2 200411557176317747 = some 200411557176317747 := by decide +kernel
private theorem endpoint_7_54_p4 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 0 4 200411557176317747 = some 200411557176317747 :=
  join_receipt_window endpoint_7_54_flag endpoint_7_54_sources 0 2 2 200411557176317747 200411557176317747 200411557176317747 endpoint_7_54_w0 endpoint_7_54_w2
private theorem endpoint_7_54_w4 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 4 2 200411557176317747 = some 200411557176317747 := by decide +kernel
private theorem endpoint_7_54_p6 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 0 6 200411557176317747 = some 200411557176317747 :=
  join_receipt_window endpoint_7_54_flag endpoint_7_54_sources 0 4 2 200411557176317747 200411557176317747 200411557176317747 endpoint_7_54_p4 endpoint_7_54_w4
def endpoint_7_54 : CertifiedEndpoint :=
  ⟨⟨7, 54, 3696⟩, 200411557176317747, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_54_flag endpoint_7_54_sources 6 200411557176317747 200411557176317747 rfl endpoint_7_54_base endpoint_7_54_p6) (by decide)⟩
private def endpoint_7_55_flag : Flag := ⟨7, 55, 3664⟩
private def endpoint_7_55_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_55_base : receiptBase endpoint_7_55_flag endpoint_7_55_sources = some 201921104823954525 := by decide +kernel
private theorem endpoint_7_55_w0 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 0 2 201921104823954525 = some 201921104823954525 := by decide +kernel
private theorem endpoint_7_55_w2 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 2 2 201921104823954525 = some 201921104823954525 := by decide +kernel
private theorem endpoint_7_55_p4 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 0 4 201921104823954525 = some 201921104823954525 :=
  join_receipt_window endpoint_7_55_flag endpoint_7_55_sources 0 2 2 201921104823954525 201921104823954525 201921104823954525 endpoint_7_55_w0 endpoint_7_55_w2
private theorem endpoint_7_55_w4 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 4 2 201921104823954525 = some 201921104823954525 := by decide +kernel
private theorem endpoint_7_55_p6 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 0 6 201921104823954525 = some 201921104823954525 :=
  join_receipt_window endpoint_7_55_flag endpoint_7_55_sources 0 4 2 201921104823954525 201921104823954525 201921104823954525 endpoint_7_55_p4 endpoint_7_55_w4
def endpoint_7_55 : CertifiedEndpoint :=
  ⟨⟨7, 55, 3664⟩, 201921104823954525, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_55_flag endpoint_7_55_sources 6 201921104823954525 201921104823954525 rfl endpoint_7_55_base endpoint_7_55_p6) (by decide)⟩
private def endpoint_7_56_flag : Flag := ⟨7, 56, 3632⟩
private def endpoint_7_56_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_56_base : receiptBase endpoint_7_56_flag endpoint_7_56_sources = some 203373903409823221 := by decide +kernel
private theorem endpoint_7_56_w0 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 0 2 203373903409823221 = some 203373903409823221 := by decide +kernel
private theorem endpoint_7_56_w2 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 2 2 203373903409823221 = some 203373903409823221 := by decide +kernel
private theorem endpoint_7_56_p4 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 0 4 203373903409823221 = some 203373903409823221 :=
  join_receipt_window endpoint_7_56_flag endpoint_7_56_sources 0 2 2 203373903409823221 203373903409823221 203373903409823221 endpoint_7_56_w0 endpoint_7_56_w2
private theorem endpoint_7_56_w4 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 4 2 203373903409823221 = some 203373903409823221 := by decide +kernel
private theorem endpoint_7_56_p6 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 0 6 203373903409823221 = some 203373903409823221 :=
  join_receipt_window endpoint_7_56_flag endpoint_7_56_sources 0 4 2 203373903409823221 203373903409823221 203373903409823221 endpoint_7_56_p4 endpoint_7_56_w4
def endpoint_7_56 : CertifiedEndpoint :=
  ⟨⟨7, 56, 3632⟩, 203373903409823221, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_56_flag endpoint_7_56_sources 6 203373903409823221 203373903409823221 rfl endpoint_7_56_base endpoint_7_56_p6) (by decide)⟩
private def endpoint_7_57_flag : Flag := ⟨7, 57, 3599⟩
private def endpoint_7_57_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_57_base : receiptBase endpoint_7_57_flag endpoint_7_57_sources = some 204713739675554751 := by decide +kernel
private theorem endpoint_7_57_w0 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 0 2 204713739675554751 = some 204713739675554751 := by decide +kernel
private theorem endpoint_7_57_w2 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 2 2 204713739675554751 = some 204713739675554751 := by decide +kernel
private theorem endpoint_7_57_p4 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 0 4 204713739675554751 = some 204713739675554751 :=
  join_receipt_window endpoint_7_57_flag endpoint_7_57_sources 0 2 2 204713739675554751 204713739675554751 204713739675554751 endpoint_7_57_w0 endpoint_7_57_w2
private theorem endpoint_7_57_w4 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 4 2 204713739675554751 = some 204713739675554751 := by decide +kernel
private theorem endpoint_7_57_p6 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 0 6 204713739675554751 = some 204713739675554751 :=
  join_receipt_window endpoint_7_57_flag endpoint_7_57_sources 0 4 2 204713739675554751 204713739675554751 204713739675554751 endpoint_7_57_p4 endpoint_7_57_w4
def endpoint_7_57 : CertifiedEndpoint :=
  ⟨⟨7, 57, 3599⟩, 204713739675554751, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_57_flag endpoint_7_57_sources 6 204713739675554751 204713739675554751 rfl endpoint_7_57_base endpoint_7_57_p6) (by decide)⟩
private def endpoint_7_58_flag : Flag := ⟨7, 58, 3566⟩
private def endpoint_7_58_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_58_base : receiptBase endpoint_7_58_flag endpoint_7_58_sources = some 206658106076608137 := by decide +kernel
private theorem endpoint_7_58_w0 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 0 2 206658106076608137 = some 206658106076608137 := by decide +kernel
private theorem endpoint_7_58_w2 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 2 2 206658106076608137 = some 206658106076608137 := by decide +kernel
private theorem endpoint_7_58_p4 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 0 4 206658106076608137 = some 206658106076608137 :=
  join_receipt_window endpoint_7_58_flag endpoint_7_58_sources 0 2 2 206658106076608137 206658106076608137 206658106076608137 endpoint_7_58_w0 endpoint_7_58_w2
private theorem endpoint_7_58_w4 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 4 2 206658106076608137 = some 206658106076608137 := by decide +kernel
private theorem endpoint_7_58_p6 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 0 6 206658106076608137 = some 206658106076608137 :=
  join_receipt_window endpoint_7_58_flag endpoint_7_58_sources 0 4 2 206658106076608137 206658106076608137 206658106076608137 endpoint_7_58_p4 endpoint_7_58_w4
def endpoint_7_58 : CertifiedEndpoint :=
  ⟨⟨7, 58, 3566⟩, 206658106076608137, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_58_flag endpoint_7_58_sources 6 206658106076608137 206658106076608137 rfl endpoint_7_58_base endpoint_7_58_p6) (by decide)⟩
private def endpoint_7_59_flag : Flag := ⟨7, 59, 3531⟩
private def endpoint_7_59_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_59_base : receiptBase endpoint_7_59_flag endpoint_7_59_sources = some 207758228135690764 := by decide +kernel
private theorem endpoint_7_59_w0 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 0 2 207758228135690764 = some 207758228135690764 := by decide +kernel
private theorem endpoint_7_59_w2 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 2 2 207758228135690764 = some 207758228135690764 := by decide +kernel
private theorem endpoint_7_59_p4 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 0 4 207758228135690764 = some 207758228135690764 :=
  join_receipt_window endpoint_7_59_flag endpoint_7_59_sources 0 2 2 207758228135690764 207758228135690764 207758228135690764 endpoint_7_59_w0 endpoint_7_59_w2
private theorem endpoint_7_59_w4 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 4 2 207758228135690764 = some 207758228135690764 := by decide +kernel
private theorem endpoint_7_59_p6 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 0 6 207758228135690764 = some 207758228135690764 :=
  join_receipt_window endpoint_7_59_flag endpoint_7_59_sources 0 4 2 207758228135690764 207758228135690764 207758228135690764 endpoint_7_59_p4 endpoint_7_59_w4
def endpoint_7_59 : CertifiedEndpoint :=
  ⟨⟨7, 59, 3531⟩, 207758228135690764, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_59_flag endpoint_7_59_sources 6 207758228135690764 207758228135690764 rfl endpoint_7_59_base endpoint_7_59_p6) (by decide)⟩
private def endpoint_7_60_flag : Flag := ⟨7, 60, 3495⟩
private def endpoint_7_60_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_60_base : receiptBase endpoint_7_60_flag endpoint_7_60_sources = some 208737341299206459 := by decide +kernel
private theorem endpoint_7_60_w0 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 0 2 208737341299206459 = some 208737341299206459 := by decide +kernel
private theorem endpoint_7_60_w2 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 2 2 208737341299206459 = some 208737341299206459 := by decide +kernel
private theorem endpoint_7_60_p4 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 0 4 208737341299206459 = some 208737341299206459 :=
  join_receipt_window endpoint_7_60_flag endpoint_7_60_sources 0 2 2 208737341299206459 208737341299206459 208737341299206459 endpoint_7_60_w0 endpoint_7_60_w2
private theorem endpoint_7_60_w4 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 4 2 208737341299206459 = some 208737341299206459 := by decide +kernel
private theorem endpoint_7_60_p6 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 0 6 208737341299206459 = some 208737341299206459 :=
  join_receipt_window endpoint_7_60_flag endpoint_7_60_sources 0 4 2 208737341299206459 208737341299206459 208737341299206459 endpoint_7_60_p4 endpoint_7_60_w4
def endpoint_7_60 : CertifiedEndpoint :=
  ⟨⟨7, 60, 3495⟩, 208737341299206459, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_60_flag endpoint_7_60_sources 6 208737341299206459 208737341299206459 rfl endpoint_7_60_base endpoint_7_60_p6) (by decide)⟩
private def endpoint_7_61_flag : Flag := ⟨7, 61, 3458⟩
private def endpoint_7_61_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_61_base : receiptBase endpoint_7_61_flag endpoint_7_61_sources = some 209592826379689003 := by decide +kernel
private theorem endpoint_7_61_w0 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 0 2 209592826379689003 = some 209592826379689003 := by decide +kernel
private theorem endpoint_7_61_w2 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 2 2 209592826379689003 = some 209592826379689003 := by decide +kernel
private theorem endpoint_7_61_p4 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 0 4 209592826379689003 = some 209592826379689003 :=
  join_receipt_window endpoint_7_61_flag endpoint_7_61_sources 0 2 2 209592826379689003 209592826379689003 209592826379689003 endpoint_7_61_w0 endpoint_7_61_w2
private theorem endpoint_7_61_w4 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 4 2 209592826379689003 = some 209592826379689003 := by decide +kernel
private theorem endpoint_7_61_p6 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 0 6 209592826379689003 = some 209592826379689003 :=
  join_receipt_window endpoint_7_61_flag endpoint_7_61_sources 0 4 2 209592826379689003 209592826379689003 209592826379689003 endpoint_7_61_p4 endpoint_7_61_w4
def endpoint_7_61 : CertifiedEndpoint :=
  ⟨⟨7, 61, 3458⟩, 209592826379689003, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_61_flag endpoint_7_61_sources 6 209592826379689003 209592826379689003 rfl endpoint_7_61_base endpoint_7_61_p6) (by decide)⟩
private def endpoint_7_62_flag : Flag := ⟨7, 62, 3420⟩
private def endpoint_7_62_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_62_base : receiptBase endpoint_7_62_flag endpoint_7_62_sources = some 210322064189672177 := by decide +kernel
private theorem endpoint_7_62_w0 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 0 2 210322064189672177 = some 210322064189672177 := by decide +kernel
private theorem endpoint_7_62_w2 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 2 2 210322064189672177 = some 210322064189672177 := by decide +kernel
private theorem endpoint_7_62_p4 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 0 4 210322064189672177 = some 210322064189672177 :=
  join_receipt_window endpoint_7_62_flag endpoint_7_62_sources 0 2 2 210322064189672177 210322064189672177 210322064189672177 endpoint_7_62_w0 endpoint_7_62_w2
private theorem endpoint_7_62_w4 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 4 2 210322064189672177 = some 210322064189672177 := by decide +kernel
private theorem endpoint_7_62_p6 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 0 6 210322064189672177 = some 210322064189672177 :=
  join_receipt_window endpoint_7_62_flag endpoint_7_62_sources 0 4 2 210322064189672177 210322064189672177 210322064189672177 endpoint_7_62_p4 endpoint_7_62_w4
def endpoint_7_62 : CertifiedEndpoint :=
  ⟨⟨7, 62, 3420⟩, 210322064189672177, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_62_flag endpoint_7_62_sources 6 210322064189672177 210322064189672177 rfl endpoint_7_62_base endpoint_7_62_p6) (by decide)⟩
private def endpoint_7_63_flag : Flag := ⟨7, 63, 3381⟩
private def endpoint_7_63_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_63_base : receiptBase endpoint_7_63_flag endpoint_7_63_sources = some 213135230041795469 := by decide +kernel
private theorem endpoint_7_63_w0 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 0 2 213135230041795469 = some 213135230041795469 := by decide +kernel
private theorem endpoint_7_63_w2 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 2 2 213135230041795469 = some 213135230041795469 := by decide +kernel
private theorem endpoint_7_63_p4 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 0 4 213135230041795469 = some 213135230041795469 :=
  join_receipt_window endpoint_7_63_flag endpoint_7_63_sources 0 2 2 213135230041795469 213135230041795469 213135230041795469 endpoint_7_63_w0 endpoint_7_63_w2
private theorem endpoint_7_63_w4 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 4 2 213135230041795469 = some 213135230041795469 := by decide +kernel
private theorem endpoint_7_63_p6 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 0 6 213135230041795469 = some 213135230041795469 :=
  join_receipt_window endpoint_7_63_flag endpoint_7_63_sources 0 4 2 213135230041795469 213135230041795469 213135230041795469 endpoint_7_63_p4 endpoint_7_63_w4
def endpoint_7_63 : CertifiedEndpoint :=
  ⟨⟨7, 63, 3381⟩, 213135230041795469, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_63_flag endpoint_7_63_sources 6 213135230041795469 213135230041795469 rfl endpoint_7_63_base endpoint_7_63_p6) (by decide)⟩
private def endpoint_7_64_flag : Flag := ⟨7, 64, 3340⟩
private def endpoint_7_64_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_64_base : receiptBase endpoint_7_64_flag endpoint_7_64_sources = some 213528592360802511 := by decide +kernel
private theorem endpoint_7_64_w0 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 0 2 213528592360802511 = some 213528592360802511 := by decide +kernel
private theorem endpoint_7_64_w2 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 2 2 213528592360802511 = some 213528592360802511 := by decide +kernel
private theorem endpoint_7_64_p4 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 0 4 213528592360802511 = some 213528592360802511 :=
  join_receipt_window endpoint_7_64_flag endpoint_7_64_sources 0 2 2 213528592360802511 213528592360802511 213528592360802511 endpoint_7_64_w0 endpoint_7_64_w2
private theorem endpoint_7_64_w4 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 4 2 213528592360802511 = some 213528592360802511 := by decide +kernel
private theorem endpoint_7_64_p6 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 0 6 213528592360802511 = some 213528592360802511 :=
  join_receipt_window endpoint_7_64_flag endpoint_7_64_sources 0 4 2 213528592360802511 213528592360802511 213528592360802511 endpoint_7_64_p4 endpoint_7_64_w4
def endpoint_7_64 : CertifiedEndpoint :=
  ⟨⟨7, 64, 3340⟩, 213528592360802511, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_64_flag endpoint_7_64_sources 6 213528592360802511 213528592360802511 rfl endpoint_7_64_base endpoint_7_64_p6) (by decide)⟩
private def endpoint_7_65_flag : Flag := ⟨7, 65, 3297⟩
private def endpoint_7_65_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_65_base : receiptBase endpoint_7_65_flag endpoint_7_65_sources = some 213720298497896121 := by decide +kernel
private theorem endpoint_7_65_w0 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 0 2 213720298497896121 = some 213720298497896121 := by decide +kernel
private theorem endpoint_7_65_w2 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 2 2 213720298497896121 = some 213720298497896121 := by decide +kernel
private theorem endpoint_7_65_p4 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 0 4 213720298497896121 = some 213720298497896121 :=
  join_receipt_window endpoint_7_65_flag endpoint_7_65_sources 0 2 2 213720298497896121 213720298497896121 213720298497896121 endpoint_7_65_w0 endpoint_7_65_w2
private theorem endpoint_7_65_w4 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 4 2 213720298497896121 = some 213720298497896121 := by decide +kernel
private theorem endpoint_7_65_p6 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 0 6 213720298497896121 = some 213720298497896121 :=
  join_receipt_window endpoint_7_65_flag endpoint_7_65_sources 0 4 2 213720298497896121 213720298497896121 213720298497896121 endpoint_7_65_p4 endpoint_7_65_w4
def endpoint_7_65 : CertifiedEndpoint :=
  ⟨⟨7, 65, 3297⟩, 213720298497896121, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_65_flag endpoint_7_65_sources 6 213720298497896121 213720298497896121 rfl endpoint_7_65_base endpoint_7_65_p6) (by decide)⟩
private def endpoint_7_66_flag : Flag := ⟨7, 66, 3253⟩
private def endpoint_7_66_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_66_base : receiptBase endpoint_7_66_flag endpoint_7_66_sources = some 213770160851623220 := by decide +kernel
private theorem endpoint_7_66_w0 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 0 2 213770160851623220 = some 213770160851623220 := by decide +kernel
private theorem endpoint_7_66_w2 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 2 2 213770160851623220 = some 213770160851623220 := by decide +kernel
private theorem endpoint_7_66_p4 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 0 4 213770160851623220 = some 213770160851623220 :=
  join_receipt_window endpoint_7_66_flag endpoint_7_66_sources 0 2 2 213770160851623220 213770160851623220 213770160851623220 endpoint_7_66_w0 endpoint_7_66_w2
private theorem endpoint_7_66_w4 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 4 2 213770160851623220 = some 213770160851623220 := by decide +kernel
private theorem endpoint_7_66_p6 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 0 6 213770160851623220 = some 213770160851623220 :=
  join_receipt_window endpoint_7_66_flag endpoint_7_66_sources 0 4 2 213770160851623220 213770160851623220 213770160851623220 endpoint_7_66_p4 endpoint_7_66_w4
def endpoint_7_66 : CertifiedEndpoint :=
  ⟨⟨7, 66, 3253⟩, 213770160851623220, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_66_flag endpoint_7_66_sources 6 213770160851623220 213770160851623220 rfl endpoint_7_66_base endpoint_7_66_p6) (by decide)⟩
private def endpoint_7_67_flag : Flag := ⟨7, 67, 3206⟩
private def endpoint_7_67_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_7_67_base : receiptBase endpoint_7_67_flag endpoint_7_67_sources = some 215089483191358111 := by decide +kernel
private theorem endpoint_7_67_w0 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 0 2 215089483191358111 = some 215089483191358111 := by decide +kernel
private theorem endpoint_7_67_w2 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 2 2 215089483191358111 = some 215089483191358111 := by decide +kernel
private theorem endpoint_7_67_p4 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 0 4 215089483191358111 = some 215089483191358111 :=
  join_receipt_window endpoint_7_67_flag endpoint_7_67_sources 0 2 2 215089483191358111 215089483191358111 215089483191358111 endpoint_7_67_w0 endpoint_7_67_w2
private theorem endpoint_7_67_w4 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 4 2 215089483191358111 = some 215089483191358111 := by decide +kernel
private theorem endpoint_7_67_p6 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 0 6 215089483191358111 = some 215089483191358111 :=
  join_receipt_window endpoint_7_67_flag endpoint_7_67_sources 0 4 2 215089483191358111 215089483191358111 215089483191358111 endpoint_7_67_p4 endpoint_7_67_w4
def endpoint_7_67 : CertifiedEndpoint :=
  ⟨⟨7, 67, 3206⟩, 215089483191358111, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_7_67_flag endpoint_7_67_sources 6 215089483191358111 215089483191358111 rfl endpoint_7_67_base endpoint_7_67_p6) (by decide)⟩
private def endpoint_7_68_flag : Flag := ⟨7, 68, 3157⟩
private def endpoint_7_68_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_7_68_base : receiptBase endpoint_7_68_flag endpoint_7_68_sources = some 214644239620751475 := by decide +kernel
private theorem endpoint_7_68_w0 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 0 2 214644239620751475 = some 214644239620751475 := by decide +kernel
private theorem endpoint_7_68_w2 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 2 2 214644239620751475 = some 214644239620751475 := by decide +kernel
private theorem endpoint_7_68_p4 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 0 4 214644239620751475 = some 214644239620751475 :=
  join_receipt_window endpoint_7_68_flag endpoint_7_68_sources 0 2 2 214644239620751475 214644239620751475 214644239620751475 endpoint_7_68_w0 endpoint_7_68_w2
private theorem endpoint_7_68_w4 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 4 2 214644239620751475 = some 214644239620751475 := by decide +kernel
private theorem endpoint_7_68_p6 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 0 6 214644239620751475 = some 214644239620751475 :=
  join_receipt_window endpoint_7_68_flag endpoint_7_68_sources 0 4 2 214644239620751475 214644239620751475 214644239620751475 endpoint_7_68_p4 endpoint_7_68_w4
def endpoint_7_68 : CertifiedEndpoint :=
  ⟨⟨7, 68, 3157⟩, 214644239620751475, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_7_68_flag endpoint_7_68_sources 6 214644239620751475 214644239620751475 rfl endpoint_7_68_base endpoint_7_68_p6) (by decide)⟩
private def endpoint_7_69_flag : Flag := ⟨7, 69, 3106⟩
private def endpoint_7_69_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_7_69_base : receiptBase endpoint_7_69_flag endpoint_7_69_sources = some 213974169860739231 := by decide +kernel
private theorem endpoint_7_69_w0 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 0 2 213974169860739231 = some 213974169860739231 := by decide +kernel
private theorem endpoint_7_69_w2 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 2 2 213974169860739231 = some 213974169860739231 := by decide +kernel
private theorem endpoint_7_69_p4 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 0 4 213974169860739231 = some 213974169860739231 :=
  join_receipt_window endpoint_7_69_flag endpoint_7_69_sources 0 2 2 213974169860739231 213974169860739231 213974169860739231 endpoint_7_69_w0 endpoint_7_69_w2
private theorem endpoint_7_69_w4 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 4 2 213974169860739231 = some 213974169860739231 := by decide +kernel
private theorem endpoint_7_69_p6 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 0 6 213974169860739231 = some 213974169860739231 :=
  join_receipt_window endpoint_7_69_flag endpoint_7_69_sources 0 4 2 213974169860739231 213974169860739231 213974169860739231 endpoint_7_69_p4 endpoint_7_69_w4
def endpoint_7_69 : CertifiedEndpoint :=
  ⟨⟨7, 69, 3106⟩, 213974169860739231, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_7_69_flag endpoint_7_69_sources 6 213974169860739231 213974169860739231 rfl endpoint_7_69_base endpoint_7_69_p6) (by decide)⟩
private def endpoint_7_70_flag : Flag := ⟨7, 70, 3051⟩
private def endpoint_7_70_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_7_70_base : receiptBase endpoint_7_70_flag endpoint_7_70_sources = some 214518036554656783 := by decide +kernel
private theorem endpoint_7_70_w0 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 0 2 214518036554656783 = some 214518036554656783 := by decide +kernel
private theorem endpoint_7_70_w2 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 2 2 214518036554656783 = some 214518036554656783 := by decide +kernel
private theorem endpoint_7_70_p4 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 0 4 214518036554656783 = some 214518036554656783 :=
  join_receipt_window endpoint_7_70_flag endpoint_7_70_sources 0 2 2 214518036554656783 214518036554656783 214518036554656783 endpoint_7_70_w0 endpoint_7_70_w2
private theorem endpoint_7_70_w4 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 4 2 214518036554656783 = some 214518036554656783 := by decide +kernel
private theorem endpoint_7_70_p6 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 0 6 214518036554656783 = some 214518036554656783 :=
  join_receipt_window endpoint_7_70_flag endpoint_7_70_sources 0 4 2 214518036554656783 214518036554656783 214518036554656783 endpoint_7_70_p4 endpoint_7_70_w4
def endpoint_7_70 : CertifiedEndpoint :=
  ⟨⟨7, 70, 3051⟩, 214518036554656783, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_7_70_flag endpoint_7_70_sources 6 214518036554656783 214518036554656783 rfl endpoint_7_70_base endpoint_7_70_p6) (by decide)⟩
private def endpoint_7_71_flag : Flag := ⟨7, 71, 2995⟩
private def endpoint_7_71_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_7_71_base : receiptBase endpoint_7_71_flag endpoint_7_71_sources = some 214916570743062430 := by decide +kernel
private theorem endpoint_7_71_w0 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 0 2 214916570743062430 = some 214916570743062430 := by decide +kernel
private theorem endpoint_7_71_w2 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 2 2 214916570743062430 = some 214916570743062430 := by decide +kernel
private theorem endpoint_7_71_p4 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 0 4 214916570743062430 = some 214916570743062430 :=
  join_receipt_window endpoint_7_71_flag endpoint_7_71_sources 0 2 2 214916570743062430 214916570743062430 214916570743062430 endpoint_7_71_w0 endpoint_7_71_w2
private theorem endpoint_7_71_w4 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 4 2 214916570743062430 = some 214916570743062430 := by decide +kernel
private theorem endpoint_7_71_p6 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 0 6 214916570743062430 = some 214916570743062430 :=
  join_receipt_window endpoint_7_71_flag endpoint_7_71_sources 0 4 2 214916570743062430 214916570743062430 214916570743062430 endpoint_7_71_p4 endpoint_7_71_w4
def endpoint_7_71 : CertifiedEndpoint :=
  ⟨⟨7, 71, 2995⟩, 214916570743062430, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_7_71_flag endpoint_7_71_sources 6 214916570743062430 214916570743062430 rfl endpoint_7_71_base endpoint_7_71_p6) (by decide)⟩
private def endpoint_7_72_flag : Flag := ⟨7, 72, 2935⟩
private def endpoint_7_72_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_7_72_base : receiptBase endpoint_7_72_flag endpoint_7_72_sources = some 213304029578577143 := by decide +kernel
private theorem endpoint_7_72_w0 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 0 2 213304029578577143 = some 213304029578577143 := by decide +kernel
private theorem endpoint_7_72_w2 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 2 2 213304029578577143 = some 213304029578577143 := by decide +kernel
private theorem endpoint_7_72_p4 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 0 4 213304029578577143 = some 213304029578577143 :=
  join_receipt_window endpoint_7_72_flag endpoint_7_72_sources 0 2 2 213304029578577143 213304029578577143 213304029578577143 endpoint_7_72_w0 endpoint_7_72_w2
private theorem endpoint_7_72_w4 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 4 2 213304029578577143 = some 213304029578577143 := by decide +kernel
private theorem endpoint_7_72_p6 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 0 6 213304029578577143 = some 213304029578577143 :=
  join_receipt_window endpoint_7_72_flag endpoint_7_72_sources 0 4 2 213304029578577143 213304029578577143 213304029578577143 endpoint_7_72_p4 endpoint_7_72_w4
def endpoint_7_72 : CertifiedEndpoint :=
  ⟨⟨7, 72, 2935⟩, 213304029578577143, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_7_72_flag endpoint_7_72_sources 6 213304029578577143 213304029578577143 rfl endpoint_7_72_base endpoint_7_72_p6) (by decide)⟩
private def endpoint_7_73_flag : Flag := ⟨7, 73, 2873⟩
private def endpoint_7_73_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_7_73_base : receiptBase endpoint_7_73_flag endpoint_7_73_sources = some 214590649003142781 := by decide +kernel
private theorem endpoint_7_73_w0 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 0 2 214590649003142781 = some 214590649003142781 := by decide +kernel
private theorem endpoint_7_73_w2 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 2 2 214590649003142781 = some 214590649003142781 := by decide +kernel
private theorem endpoint_7_73_p4 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 0 4 214590649003142781 = some 214590649003142781 :=
  join_receipt_window endpoint_7_73_flag endpoint_7_73_sources 0 2 2 214590649003142781 214590649003142781 214590649003142781 endpoint_7_73_w0 endpoint_7_73_w2
private theorem endpoint_7_73_w4 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 4 2 214590649003142781 = some 214590649003142781 := by decide +kernel
private theorem endpoint_7_73_p6 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 0 6 214590649003142781 = some 214590649003142781 :=
  join_receipt_window endpoint_7_73_flag endpoint_7_73_sources 0 4 2 214590649003142781 214590649003142781 214590649003142781 endpoint_7_73_p4 endpoint_7_73_w4
def endpoint_7_73 : CertifiedEndpoint :=
  ⟨⟨7, 73, 2873⟩, 214590649003142781, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_7_73_flag endpoint_7_73_sources 6 214590649003142781 214590649003142781 rfl endpoint_7_73_base endpoint_7_73_p6) (by decide)⟩
private def endpoint_7_74_flag : Flag := ⟨7, 74, 2809⟩
private def endpoint_7_74_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_7_74_base : receiptBase endpoint_7_74_flag endpoint_7_74_sources = some 212431153706674398 := by decide +kernel
private theorem endpoint_7_74_w0 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 0 2 212431153706674398 = some 212431153706674398 := by decide +kernel
private theorem endpoint_7_74_w2 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 2 2 212431153706674398 = some 212431153706674398 := by decide +kernel
private theorem endpoint_7_74_p4 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 0 4 212431153706674398 = some 212431153706674398 :=
  join_receipt_window endpoint_7_74_flag endpoint_7_74_sources 0 2 2 212431153706674398 212431153706674398 212431153706674398 endpoint_7_74_w0 endpoint_7_74_w2
private theorem endpoint_7_74_w4 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 4 2 212431153706674398 = some 212431153706674398 := by decide +kernel
private theorem endpoint_7_74_p6 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 0 6 212431153706674398 = some 212431153706674398 :=
  join_receipt_window endpoint_7_74_flag endpoint_7_74_sources 0 4 2 212431153706674398 212431153706674398 212431153706674398 endpoint_7_74_p4 endpoint_7_74_w4
def endpoint_7_74 : CertifiedEndpoint :=
  ⟨⟨7, 74, 2809⟩, 212431153706674398, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_7_74_flag endpoint_7_74_sources 6 212431153706674398 212431153706674398 rfl endpoint_7_74_base endpoint_7_74_p6) (by decide)⟩
private def endpoint_7_75_flag : Flag := ⟨7, 75, 2741⟩
private def endpoint_7_75_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_7_75_base : receiptBase endpoint_7_75_flag endpoint_7_75_sources = some 209847720115821453 := by decide +kernel
private theorem endpoint_7_75_w0 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 0 2 209847720115821453 = some 209847720115821453 := by decide +kernel
private theorem endpoint_7_75_w2 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 2 2 209847720115821453 = some 209847720115821453 := by decide +kernel
private theorem endpoint_7_75_p4 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 0 4 209847720115821453 = some 209847720115821453 :=
  join_receipt_window endpoint_7_75_flag endpoint_7_75_sources 0 2 2 209847720115821453 209847720115821453 209847720115821453 endpoint_7_75_w0 endpoint_7_75_w2
private theorem endpoint_7_75_w4 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 4 2 209847720115821453 = some 209847720115821453 := by decide +kernel
private theorem endpoint_7_75_p6 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 0 6 209847720115821453 = some 209847720115821453 :=
  join_receipt_window endpoint_7_75_flag endpoint_7_75_sources 0 4 2 209847720115821453 209847720115821453 209847720115821453 endpoint_7_75_p4 endpoint_7_75_w4
def endpoint_7_75 : CertifiedEndpoint :=
  ⟨⟨7, 75, 2741⟩, 209847720115821453, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_7_75_flag endpoint_7_75_sources 6 209847720115821453 209847720115821453 rfl endpoint_7_75_base endpoint_7_75_p6) (by decide)⟩
private def endpoint_7_76_flag : Flag := ⟨7, 76, 2671⟩
private def endpoint_7_76_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_7_76_base : receiptBase endpoint_7_76_flag endpoint_7_76_sources = some 210777774300904946 := by decide +kernel
private theorem endpoint_7_76_w0 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 0 2 210777774300904946 = some 210777774300904946 := by decide +kernel
private theorem endpoint_7_76_w2 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 2 2 210777774300904946 = some 210777774300904946 := by decide +kernel
private theorem endpoint_7_76_p4 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 0 4 210777774300904946 = some 210777774300904946 :=
  join_receipt_window endpoint_7_76_flag endpoint_7_76_sources 0 2 2 210777774300904946 210777774300904946 210777774300904946 endpoint_7_76_w0 endpoint_7_76_w2
private theorem endpoint_7_76_w4 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 4 2 210777774300904946 = some 210777774300904946 := by decide +kernel
private theorem endpoint_7_76_p6 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 0 6 210777774300904946 = some 210777774300904946 :=
  join_receipt_window endpoint_7_76_flag endpoint_7_76_sources 0 4 2 210777774300904946 210777774300904946 210777774300904946 endpoint_7_76_p4 endpoint_7_76_w4
def endpoint_7_76 : CertifiedEndpoint :=
  ⟨⟨7, 76, 2671⟩, 210777774300904946, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_7_76_flag endpoint_7_76_sources 6 210777774300904946 210777774300904946 rfl endpoint_7_76_base endpoint_7_76_p6) (by decide)⟩
private def endpoint_7_77_flag : Flag := ⟨7, 77, 2599⟩
private def endpoint_7_77_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_7_77_base : receiptBase endpoint_7_77_flag endpoint_7_77_sources = some 207601305047314353 := by decide +kernel
private theorem endpoint_7_77_w0 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 0 2 207601305047314353 = some 207601305047314353 := by decide +kernel
private theorem endpoint_7_77_w2 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 2 2 207601305047314353 = some 207601305047314353 := by decide +kernel
private theorem endpoint_7_77_p4 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 0 4 207601305047314353 = some 207601305047314353 :=
  join_receipt_window endpoint_7_77_flag endpoint_7_77_sources 0 2 2 207601305047314353 207601305047314353 207601305047314353 endpoint_7_77_w0 endpoint_7_77_w2
private theorem endpoint_7_77_w4 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 4 2 207601305047314353 = some 207601305047314353 := by decide +kernel
private theorem endpoint_7_77_p6 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 0 6 207601305047314353 = some 207601305047314353 :=
  join_receipt_window endpoint_7_77_flag endpoint_7_77_sources 0 4 2 207601305047314353 207601305047314353 207601305047314353 endpoint_7_77_p4 endpoint_7_77_w4
def endpoint_7_77 : CertifiedEndpoint :=
  ⟨⟨7, 77, 2599⟩, 207601305047314353, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_7_77_flag endpoint_7_77_sources 6 207601305047314353 207601305047314353 rfl endpoint_7_77_base endpoint_7_77_p6) (by decide)⟩
private def endpoint_7_78_flag : Flag := ⟨7, 78, 2523⟩
private def endpoint_7_78_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_7_78_base : receiptBase endpoint_7_78_flag endpoint_7_78_sources = some 203971505064910653 := by decide +kernel
private theorem endpoint_7_78_w0 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 0 2 203971505064910653 = some 203971505064910653 := by decide +kernel
private theorem endpoint_7_78_w2 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 2 2 203971505064910653 = some 203971505064910653 := by decide +kernel
private theorem endpoint_7_78_p4 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 0 4 203971505064910653 = some 203971505064910653 :=
  join_receipt_window endpoint_7_78_flag endpoint_7_78_sources 0 2 2 203971505064910653 203971505064910653 203971505064910653 endpoint_7_78_w0 endpoint_7_78_w2
private theorem endpoint_7_78_w4 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 4 2 203971505064910653 = some 203971505064910653 := by decide +kernel
private theorem endpoint_7_78_p6 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 0 6 203971505064910653 = some 203971505064910653 :=
  join_receipt_window endpoint_7_78_flag endpoint_7_78_sources 0 4 2 203971505064910653 203971505064910653 203971505064910653 endpoint_7_78_p4 endpoint_7_78_w4
def endpoint_7_78 : CertifiedEndpoint :=
  ⟨⟨7, 78, 2523⟩, 203971505064910653, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_7_78_flag endpoint_7_78_sources 6 203971505064910653 203971505064910653 rfl endpoint_7_78_base endpoint_7_78_p6) (by decide)⟩
private def endpoint_7_79_flag : Flag := ⟨7, 79, 2445⟩
private def endpoint_7_79_sources : Sources := ⟨contact11, contact11, contact13⟩
private theorem endpoint_7_79_base : receiptBase endpoint_7_79_flag endpoint_7_79_sources = some 200085079416511351 := by decide +kernel
private theorem endpoint_7_79_w0 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 0 2 200085079416511351 = some 200085079416511351 := by decide +kernel
private theorem endpoint_7_79_w2 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 2 2 200085079416511351 = some 200085079416511351 := by decide +kernel
private theorem endpoint_7_79_p4 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 0 4 200085079416511351 = some 200085079416511351 :=
  join_receipt_window endpoint_7_79_flag endpoint_7_79_sources 0 2 2 200085079416511351 200085079416511351 200085079416511351 endpoint_7_79_w0 endpoint_7_79_w2
private theorem endpoint_7_79_w4 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 4 2 200085079416511351 = some 200085079416511351 := by decide +kernel
private theorem endpoint_7_79_p6 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 0 6 200085079416511351 = some 200085079416511351 :=
  join_receipt_window endpoint_7_79_flag endpoint_7_79_sources 0 4 2 200085079416511351 200085079416511351 200085079416511351 endpoint_7_79_p4 endpoint_7_79_w4
def endpoint_7_79 : CertifiedEndpoint :=
  ⟨⟨7, 79, 2445⟩, 200085079416511351, .terminal ⟨contact11, contact11, contact13⟩ (finish_receipt_window endpoint_7_79_flag endpoint_7_79_sources 6 200085079416511351 200085079416511351 rfl endpoint_7_79_base endpoint_7_79_p6) (by decide)⟩
private def endpoint_7_80_flag : Flag := ⟨7, 80, 2365⟩
private def endpoint_7_80_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_7_80_base : receiptBase endpoint_7_80_flag endpoint_7_80_sources = some 198043885724593257 := by decide +kernel
private theorem endpoint_7_80_w0 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 0 2 198043885724593257 = some 198043885724593257 := by decide +kernel
private theorem endpoint_7_80_w2 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 2 2 198043885724593257 = some 198043885724593257 := by decide +kernel
private theorem endpoint_7_80_p4 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 0 4 198043885724593257 = some 198043885724593257 :=
  join_receipt_window endpoint_7_80_flag endpoint_7_80_sources 0 2 2 198043885724593257 198043885724593257 198043885724593257 endpoint_7_80_w0 endpoint_7_80_w2
private theorem endpoint_7_80_w4 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 4 2 198043885724593257 = some 198043885724593257 := by decide +kernel
private theorem endpoint_7_80_p6 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 0 6 198043885724593257 = some 198043885724593257 :=
  join_receipt_window endpoint_7_80_flag endpoint_7_80_sources 0 4 2 198043885724593257 198043885724593257 198043885724593257 endpoint_7_80_p4 endpoint_7_80_w4
def endpoint_7_80 : CertifiedEndpoint :=
  ⟨⟨7, 80, 2365⟩, 198043885724593257, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_7_80_flag endpoint_7_80_sources 6 198043885724593257 198043885724593257 rfl endpoint_7_80_base endpoint_7_80_p6) (by decide)⟩
private def endpoint_7_81_flag : Flag := ⟨7, 81, 2281⟩
private def endpoint_7_81_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_7_81_base : receiptBase endpoint_7_81_flag endpoint_7_81_sources = some 193209330301484798 := by decide +kernel
private theorem endpoint_7_81_w0 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 0 2 193209330301484798 = some 193209330301484798 := by decide +kernel
private theorem endpoint_7_81_w2 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 2 2 193209330301484798 = some 193209330301484798 := by decide +kernel
private theorem endpoint_7_81_p4 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 0 4 193209330301484798 = some 193209330301484798 :=
  join_receipt_window endpoint_7_81_flag endpoint_7_81_sources 0 2 2 193209330301484798 193209330301484798 193209330301484798 endpoint_7_81_w0 endpoint_7_81_w2
private theorem endpoint_7_81_w4 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 4 2 193209330301484798 = some 193209330301484798 := by decide +kernel
private theorem endpoint_7_81_p6 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 0 6 193209330301484798 = some 193209330301484798 :=
  join_receipt_window endpoint_7_81_flag endpoint_7_81_sources 0 4 2 193209330301484798 193209330301484798 193209330301484798 endpoint_7_81_p4 endpoint_7_81_w4
def endpoint_7_81 : CertifiedEndpoint :=
  ⟨⟨7, 81, 2281⟩, 193209330301484798, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_7_81_flag endpoint_7_81_sources 6 193209330301484798 193209330301484798 rfl endpoint_7_81_base endpoint_7_81_p6) (by decide)⟩
private def endpoint_7_82_flag : Flag := ⟨7, 82, 2195⟩
private def endpoint_7_82_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_7_82_base : receiptBase endpoint_7_82_flag endpoint_7_82_sources = some 188045176455504298 := by decide +kernel
private theorem endpoint_7_82_w0 : receiptWindow endpoint_7_82_flag endpoint_7_82_sources 0 2 188045176455504298 = some 188045176455504298 := by decide +kernel
private theorem endpoint_7_82_w2 : receiptWindow endpoint_7_82_flag endpoint_7_82_sources 2 2 188045176455504298 = some 188045176455504298 := by decide +kernel
private theorem endpoint_7_82_p4 : receiptWindow endpoint_7_82_flag endpoint_7_82_sources 0 4 188045176455504298 = some 188045176455504298 :=
  join_receipt_window endpoint_7_82_flag endpoint_7_82_sources 0 2 2 188045176455504298 188045176455504298 188045176455504298 endpoint_7_82_w0 endpoint_7_82_w2
private theorem endpoint_7_82_w4 : receiptWindow endpoint_7_82_flag endpoint_7_82_sources 4 2 188045176455504298 = some 188045176455504298 := by decide +kernel
private theorem endpoint_7_82_p6 : receiptWindow endpoint_7_82_flag endpoint_7_82_sources 0 6 188045176455504298 = some 188045176455504298 :=
  join_receipt_window endpoint_7_82_flag endpoint_7_82_sources 0 4 2 188045176455504298 188045176455504298 188045176455504298 endpoint_7_82_p4 endpoint_7_82_w4
def endpoint_7_82 : CertifiedEndpoint :=
  ⟨⟨7, 82, 2195⟩, 188045176455504298, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_7_82_flag endpoint_7_82_sources 6 188045176455504298 188045176455504298 rfl endpoint_7_82_base endpoint_7_82_p6) (by decide)⟩
private def endpoint_7_83_flag : Flag := ⟨7, 83, 2107⟩
private def endpoint_7_83_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_7_83_base : receiptBase endpoint_7_83_flag endpoint_7_83_sources = some 182545754136727754 := by decide +kernel
private theorem endpoint_7_83_w0 : receiptWindow endpoint_7_83_flag endpoint_7_83_sources 0 2 182545754136727754 = some 182545754136727754 := by decide +kernel
private theorem endpoint_7_83_w2 : receiptWindow endpoint_7_83_flag endpoint_7_83_sources 2 2 182545754136727754 = some 182545754136727754 := by decide +kernel
private theorem endpoint_7_83_p4 : receiptWindow endpoint_7_83_flag endpoint_7_83_sources 0 4 182545754136727754 = some 182545754136727754 :=
  join_receipt_window endpoint_7_83_flag endpoint_7_83_sources 0 2 2 182545754136727754 182545754136727754 182545754136727754 endpoint_7_83_w0 endpoint_7_83_w2
private theorem endpoint_7_83_w4 : receiptWindow endpoint_7_83_flag endpoint_7_83_sources 4 2 182545754136727754 = some 182545754136727754 := by decide +kernel
private theorem endpoint_7_83_p6 : receiptWindow endpoint_7_83_flag endpoint_7_83_sources 0 6 182545754136727754 = some 182545754136727754 :=
  join_receipt_window endpoint_7_83_flag endpoint_7_83_sources 0 4 2 182545754136727754 182545754136727754 182545754136727754 endpoint_7_83_p4 endpoint_7_83_w4
def endpoint_7_83 : CertifiedEndpoint :=
  ⟨⟨7, 83, 2107⟩, 182545754136727754, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_7_83_flag endpoint_7_83_sources 6 182545754136727754 182545754136727754 rfl endpoint_7_83_base endpoint_7_83_p6) (by decide)⟩
private def endpoint_7_84_flag : Flag := ⟨7, 84, 2015⟩
private def endpoint_7_84_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_7_84_base : receiptBase endpoint_7_84_flag endpoint_7_84_sources = some 176531721245269223 := by decide +kernel
private theorem endpoint_7_84_w0 : receiptWindow endpoint_7_84_flag endpoint_7_84_sources 0 2 176531721245269223 = some 176531721245269223 := by decide +kernel
private theorem endpoint_7_84_w2 : receiptWindow endpoint_7_84_flag endpoint_7_84_sources 2 2 176531721245269223 = some 176531721245269223 := by decide +kernel
private theorem endpoint_7_84_p4 : receiptWindow endpoint_7_84_flag endpoint_7_84_sources 0 4 176531721245269223 = some 176531721245269223 :=
  join_receipt_window endpoint_7_84_flag endpoint_7_84_sources 0 2 2 176531721245269223 176531721245269223 176531721245269223 endpoint_7_84_w0 endpoint_7_84_w2
private theorem endpoint_7_84_w4 : receiptWindow endpoint_7_84_flag endpoint_7_84_sources 4 2 176531721245269223 = some 176531721245269223 := by decide +kernel
private theorem endpoint_7_84_p6 : receiptWindow endpoint_7_84_flag endpoint_7_84_sources 0 6 176531721245269223 = some 176531721245269223 :=
  join_receipt_window endpoint_7_84_flag endpoint_7_84_sources 0 4 2 176531721245269223 176531721245269223 176531721245269223 endpoint_7_84_p4 endpoint_7_84_w4
def endpoint_7_84 : CertifiedEndpoint :=
  ⟨⟨7, 84, 2015⟩, 176531721245269223, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_7_84_flag endpoint_7_84_sources 6 176531721245269223 176531721245269223 rfl endpoint_7_84_base endpoint_7_84_p6) (by decide)⟩
def endpoint_7_85 : CertifiedEndpoint :=
  ⟨⟨7, 85, 1921⟩, 255931438374023614, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_86 : CertifiedEndpoint :=
  ⟨⟨7, 86, 1825⟩, 245767137670229301, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_87 : CertifiedEndpoint :=
  ⟨⟨7, 87, 1725⟩, 234718875757401310, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_88 : CertifiedEndpoint :=
  ⟨⟨7, 88, 1623⟩, 223049322380707659, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_89 : CertifiedEndpoint :=
  ⟨⟨7, 89, 1518⟩, 210605254957033497, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_90 : CertifiedEndpoint :=
  ⟨⟨7, 90, 1411⟩, 197516324688921999, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_91 : CertifiedEndpoint :=
  ⟨⟨7, 91, 1301⟩, 183625941653176646, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_92 : CertifiedEndpoint :=
  ⟨⟨7, 92, 1188⟩, 168918952819429932, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_93 : CertifiedEndpoint :=
  ⟨⟨7, 93, 1073⟩, 153530060400347534, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_94 : CertifiedEndpoint :=
  ⟨⟨7, 94, 954⟩, 137146084549536414, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_95 : CertifiedEndpoint :=
  ⟨⟨7, 95, 834⟩, 120206488975851117, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_96 : CertifiedEndpoint :=
  ⟨⟨7, 96, 710⟩, 102241503909702086, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_97 : CertifiedEndpoint :=
  ⟨⟨7, 97, 584⟩, 83544105156992351, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_98 : CertifiedEndpoint :=
  ⟨⟨7, 98, 455⟩, 63945917104239555, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_99 : CertifiedEndpoint :=
  ⟨⟨7, 99, 323⟩, 43431786721076192, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_100 : CertifiedEndpoint :=
  ⟨⟨7, 100, 189⟩, 22148201910453777, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_8 : CertifiedEndpoint :=
  ⟨⟨8, 8, 4653⟩, 43826797904242701, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_9 : CertifiedEndpoint :=
  ⟨⟨8, 9, 4635⟩, 46557273286324974, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_10 : CertifiedEndpoint :=
  ⟨⟨8, 10, 4617⟩, 49265173737549795, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_11 : CertifiedEndpoint :=
  ⟨⟨8, 11, 4599⟩, 57980818952144352, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_12 : CertifiedEndpoint :=
  ⟨⟨8, 12, 4581⟩, 66624633315045727, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_13 : CertifiedEndpoint :=
  ⟨⟨8, 13, 4563⟩, 75196616826253920, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_14 : CertifiedEndpoint :=
  ⟨⟨8, 14, 4544⟩, 83678317817036084, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_15 : CertifiedEndpoint :=
  ⟨⟨8, 15, 4526⟩, 92104698250487827, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_16 : CertifiedEndpoint :=
  ⟨⟨8, 16, 4507⟩, 100436913414773369, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_17 : CertifiedEndpoint :=
  ⟨⟨8, 17, 4488⟩, 108693414978625557, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_18 : CertifiedEndpoint :=
  ⟨⟨8, 18, 4469⟩, 116874202942044391, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_19 : CertifiedEndpoint :=
  ⟨⟨8, 19, 4450⟩, 124979277305029871, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_20 : CertifiedEndpoint :=
  ⟨⟨8, 20, 4430⟩, 132978538152628634, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_21 : CertifiedEndpoint :=
  ⟨⟨8, 21, 4411⟩, 140930243940377320, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_22 : CertifiedEndpoint :=
  ⟨⟨8, 22, 4391⟩, 148772253463999117, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_23 : CertifiedEndpoint :=
  ⟨⟨8, 23, 4371⟩, 156534666638447388, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_24 : CertifiedEndpoint :=
  ⟨⟨8, 24, 4351⟩, 164217483463722133, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_25 : CertifiedEndpoint :=
  ⟨⟨8, 25, 4330⟩, 171780897153019559, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_26 : CertifiedEndpoint :=
  ⟨⟨8, 26, 4310⟩, 179302579905577166, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_27 : CertifiedEndpoint :=
  ⟨⟨8, 27, 4289⟩, 186700976773417282, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_28 : CertifiedEndpoint :=
  ⟨⟨8, 28, 4268⟩, 194015894543343700, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_29 : CertifiedEndpoint :=
  ⟨⟨8, 29, 4246⟩, 201199760931072283, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_30 : CertifiedEndpoint :=
  ⟨⟨8, 30, 4225⟩, 208345779130801219, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_31 : CertifiedEndpoint :=
  ⟨⟨8, 31, 4203⟩, 215356863199592148, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_32 : CertifiedEndpoint :=
  ⟨⟨8, 32, 4181⟩, 222280585421729207, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_33 : CertifiedEndpoint :=
  ⟨⟨8, 33, 4159⟩, 229116945797212396, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_34 : CertifiedEndpoint :=
  ⟨⟨8, 34, 4136⟩, 235808665169907148, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_35 : CertifiedEndpoint :=
  ⟨⟨8, 35, 4114⟩, 242468360477712511, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_36 : CertifiedEndpoint :=
  ⟨⟨8, 36, 4090⟩, 248918370129114526, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_37 : CertifiedEndpoint :=
  ⟨⟨8, 37, 4067⟩, 255336355715627152, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_38 : CertifiedEndpoint :=
  ⟨⟨8, 38, 4043⟩, 261598052053130825, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_8_39_flag : Flag := ⟨8, 39, 4019⟩
private def endpoint_8_39_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_39_base : receiptBase endpoint_8_39_flag endpoint_8_39_sources = some 177633902462699836 := by decide +kernel
private theorem endpoint_8_39_w0 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 2 177633902462699836 = some 177633902462699836 := by decide +kernel
private theorem endpoint_8_39_w2 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 2 2 177633902462699836 = some 177633902462699836 := by decide +kernel
private theorem endpoint_8_39_p4 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 4 177633902462699836 = some 177633902462699836 :=
  join_receipt_window endpoint_8_39_flag endpoint_8_39_sources 0 2 2 177633902462699836 177633902462699836 177633902462699836 endpoint_8_39_w0 endpoint_8_39_w2
private theorem endpoint_8_39_w4 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 4 2 177633902462699836 = some 177633902462699836 := by decide +kernel
private theorem endpoint_8_39_p6 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 6 177633902462699836 = some 177633902462699836 :=
  join_receipt_window endpoint_8_39_flag endpoint_8_39_sources 0 4 2 177633902462699836 177633902462699836 177633902462699836 endpoint_8_39_p4 endpoint_8_39_w4
private theorem endpoint_8_39_w6 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 6 1 177633902462699836 = some 177633902462699836 := by decide +kernel
private theorem endpoint_8_39_p7 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 7 177633902462699836 = some 177633902462699836 :=
  join_receipt_window endpoint_8_39_flag endpoint_8_39_sources 0 6 1 177633902462699836 177633902462699836 177633902462699836 endpoint_8_39_p6 endpoint_8_39_w6
def endpoint_8_39 : CertifiedEndpoint :=
  ⟨⟨8, 39, 4019⟩, 177633902462699836, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_39_flag endpoint_8_39_sources 7 177633902462699836 177633902462699836 rfl endpoint_8_39_base endpoint_8_39_p7) (by decide)⟩
private def endpoint_8_40_flag : Flag := ⟨8, 40, 3995⟩
private def endpoint_8_40_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_40_base : receiptBase endpoint_8_40_flag endpoint_8_40_sources = some 180378435713888507 := by decide +kernel
private theorem endpoint_8_40_w0 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 2 180378435713888507 = some 180378435713888507 := by decide +kernel
private theorem endpoint_8_40_w2 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 2 2 180378435713888507 = some 180378435713888507 := by decide +kernel
private theorem endpoint_8_40_p4 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 4 180378435713888507 = some 180378435713888507 :=
  join_receipt_window endpoint_8_40_flag endpoint_8_40_sources 0 2 2 180378435713888507 180378435713888507 180378435713888507 endpoint_8_40_w0 endpoint_8_40_w2
private theorem endpoint_8_40_w4 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 4 2 180378435713888507 = some 180378435713888507 := by decide +kernel
private theorem endpoint_8_40_p6 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 6 180378435713888507 = some 180378435713888507 :=
  join_receipt_window endpoint_8_40_flag endpoint_8_40_sources 0 4 2 180378435713888507 180378435713888507 180378435713888507 endpoint_8_40_p4 endpoint_8_40_w4
private theorem endpoint_8_40_w6 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 6 1 180378435713888507 = some 180378435713888507 := by decide +kernel
private theorem endpoint_8_40_p7 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 7 180378435713888507 = some 180378435713888507 :=
  join_receipt_window endpoint_8_40_flag endpoint_8_40_sources 0 6 1 180378435713888507 180378435713888507 180378435713888507 endpoint_8_40_p6 endpoint_8_40_w6
def endpoint_8_40 : CertifiedEndpoint :=
  ⟨⟨8, 40, 3995⟩, 180378435713888507, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_40_flag endpoint_8_40_sources 7 180378435713888507 180378435713888507 rfl endpoint_8_40_base endpoint_8_40_p7) (by decide)⟩
private def endpoint_8_41_flag : Flag := ⟨8, 41, 3970⟩
private def endpoint_8_41_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_41_base : receiptBase endpoint_8_41_flag endpoint_8_41_sources = some 183031856204034499 := by decide +kernel
private theorem endpoint_8_41_w0 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 2 183031856204034499 = some 183031856204034499 := by decide +kernel
private theorem endpoint_8_41_w2 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 2 2 183031856204034499 = some 183031856204034499 := by decide +kernel
private theorem endpoint_8_41_p4 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 4 183031856204034499 = some 183031856204034499 :=
  join_receipt_window endpoint_8_41_flag endpoint_8_41_sources 0 2 2 183031856204034499 183031856204034499 183031856204034499 endpoint_8_41_w0 endpoint_8_41_w2
private theorem endpoint_8_41_w4 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 4 2 183031856204034499 = some 183031856204034499 := by decide +kernel
private theorem endpoint_8_41_p6 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 6 183031856204034499 = some 183031856204034499 :=
  join_receipt_window endpoint_8_41_flag endpoint_8_41_sources 0 4 2 183031856204034499 183031856204034499 183031856204034499 endpoint_8_41_p4 endpoint_8_41_w4
private theorem endpoint_8_41_w6 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 6 1 183031856204034499 = some 183031856204034499 := by decide +kernel
private theorem endpoint_8_41_p7 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 7 183031856204034499 = some 183031856204034499 :=
  join_receipt_window endpoint_8_41_flag endpoint_8_41_sources 0 6 1 183031856204034499 183031856204034499 183031856204034499 endpoint_8_41_p6 endpoint_8_41_w6
def endpoint_8_41 : CertifiedEndpoint :=
  ⟨⟨8, 41, 3970⟩, 183031856204034499, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_41_flag endpoint_8_41_sources 7 183031856204034499 183031856204034499 rfl endpoint_8_41_base endpoint_8_41_p7) (by decide)⟩
private def endpoint_8_42_flag : Flag := ⟨8, 42, 3945⟩
private def endpoint_8_42_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_42_base : receiptBase endpoint_8_42_flag endpoint_8_42_sources = some 185637704875113054 := by decide +kernel
private theorem endpoint_8_42_w0 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 2 185637704875113054 = some 185637704875113054 := by decide +kernel
private theorem endpoint_8_42_w2 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 2 2 185637704875113054 = some 185637704875113054 := by decide +kernel
private theorem endpoint_8_42_p4 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 4 185637704875113054 = some 185637704875113054 :=
  join_receipt_window endpoint_8_42_flag endpoint_8_42_sources 0 2 2 185637704875113054 185637704875113054 185637704875113054 endpoint_8_42_w0 endpoint_8_42_w2
private theorem endpoint_8_42_w4 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 4 2 185637704875113054 = some 185637704875113054 := by decide +kernel
private theorem endpoint_8_42_p6 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 6 185637704875113054 = some 185637704875113054 :=
  join_receipt_window endpoint_8_42_flag endpoint_8_42_sources 0 4 2 185637704875113054 185637704875113054 185637704875113054 endpoint_8_42_p4 endpoint_8_42_w4
private theorem endpoint_8_42_w6 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 6 1 185637704875113054 = some 185637704875113054 := by decide +kernel
private theorem endpoint_8_42_p7 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 7 185637704875113054 = some 185637704875113054 :=
  join_receipt_window endpoint_8_42_flag endpoint_8_42_sources 0 6 1 185637704875113054 185637704875113054 185637704875113054 endpoint_8_42_p6 endpoint_8_42_w6
def endpoint_8_42 : CertifiedEndpoint :=
  ⟨⟨8, 42, 3945⟩, 185637704875113054, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_42_flag endpoint_8_42_sources 7 185637704875113054 185637704875113054 rfl endpoint_8_42_base endpoint_8_42_p7) (by decide)⟩
private def endpoint_8_43_flag : Flag := ⟨8, 43, 3919⟩
private def endpoint_8_43_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_43_base : receiptBase endpoint_8_43_flag endpoint_8_43_sources = some 188148709662084818 := by decide +kernel
private theorem endpoint_8_43_w0 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 2 188148709662084818 = some 188148709662084818 := by decide +kernel
private theorem endpoint_8_43_w2 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 2 2 188148709662084818 = some 188148709662084818 := by decide +kernel
private theorem endpoint_8_43_p4 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 4 188148709662084818 = some 188148709662084818 :=
  join_receipt_window endpoint_8_43_flag endpoint_8_43_sources 0 2 2 188148709662084818 188148709662084818 188148709662084818 endpoint_8_43_w0 endpoint_8_43_w2
private theorem endpoint_8_43_w4 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 4 2 188148709662084818 = some 188148709662084818 := by decide +kernel
private theorem endpoint_8_43_p6 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 6 188148709662084818 = some 188148709662084818 :=
  join_receipt_window endpoint_8_43_flag endpoint_8_43_sources 0 4 2 188148709662084818 188148709662084818 188148709662084818 endpoint_8_43_p4 endpoint_8_43_w4
private theorem endpoint_8_43_w6 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 6 1 188148709662084818 = some 188148709662084818 := by decide +kernel
private theorem endpoint_8_43_p7 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 7 188148709662084818 = some 188148709662084818 :=
  join_receipt_window endpoint_8_43_flag endpoint_8_43_sources 0 6 1 188148709662084818 188148709662084818 188148709662084818 endpoint_8_43_p6 endpoint_8_43_w6
def endpoint_8_43 : CertifiedEndpoint :=
  ⟨⟨8, 43, 3919⟩, 188148709662084818, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_43_flag endpoint_8_43_sources 7 188148709662084818 188148709662084818 rfl endpoint_8_43_base endpoint_8_43_p7) (by decide)⟩
private def endpoint_8_44_flag : Flag := ⟨8, 44, 3894⟩
private def endpoint_8_44_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_44_base : receiptBase endpoint_8_44_flag endpoint_8_44_sources = some 190658481914262472 := by decide +kernel
private theorem endpoint_8_44_w0 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 2 190658481914262472 = some 190658481914262472 := by decide +kernel
private theorem endpoint_8_44_w2 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 2 2 190658481914262472 = some 190658481914262472 := by decide +kernel
private theorem endpoint_8_44_p4 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 4 190658481914262472 = some 190658481914262472 :=
  join_receipt_window endpoint_8_44_flag endpoint_8_44_sources 0 2 2 190658481914262472 190658481914262472 190658481914262472 endpoint_8_44_w0 endpoint_8_44_w2
private theorem endpoint_8_44_w4 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 4 2 190658481914262472 = some 190658481914262472 := by decide +kernel
private theorem endpoint_8_44_p6 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 6 190658481914262472 = some 190658481914262472 :=
  join_receipt_window endpoint_8_44_flag endpoint_8_44_sources 0 4 2 190658481914262472 190658481914262472 190658481914262472 endpoint_8_44_p4 endpoint_8_44_w4
private theorem endpoint_8_44_w6 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 6 1 190658481914262472 = some 190658481914262472 := by decide +kernel
private theorem endpoint_8_44_p7 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 7 190658481914262472 = some 190658481914262472 :=
  join_receipt_window endpoint_8_44_flag endpoint_8_44_sources 0 6 1 190658481914262472 190658481914262472 190658481914262472 endpoint_8_44_p6 endpoint_8_44_w6
def endpoint_8_44 : CertifiedEndpoint :=
  ⟨⟨8, 44, 3894⟩, 190658481914262472, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_44_flag endpoint_8_44_sources 7 190658481914262472 190658481914262472 rfl endpoint_8_44_base endpoint_8_44_p7) (by decide)⟩
private def endpoint_8_45_flag : Flag := ⟨8, 45, 3867⟩
private def endpoint_8_45_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_45_base : receiptBase endpoint_8_45_flag endpoint_8_45_sources = some 193022407094229866 := by decide +kernel
private theorem endpoint_8_45_w0 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 2 193022407094229866 = some 193022407094229866 := by decide +kernel
private theorem endpoint_8_45_w2 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 2 2 193022407094229866 = some 193022407094229866 := by decide +kernel
private theorem endpoint_8_45_p4 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 4 193022407094229866 = some 193022407094229866 :=
  join_receipt_window endpoint_8_45_flag endpoint_8_45_sources 0 2 2 193022407094229866 193022407094229866 193022407094229866 endpoint_8_45_w0 endpoint_8_45_w2
private theorem endpoint_8_45_w4 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 4 2 193022407094229866 = some 193022407094229866 := by decide +kernel
private theorem endpoint_8_45_p6 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 6 193022407094229866 = some 193022407094229866 :=
  join_receipt_window endpoint_8_45_flag endpoint_8_45_sources 0 4 2 193022407094229866 193022407094229866 193022407094229866 endpoint_8_45_p4 endpoint_8_45_w4
private theorem endpoint_8_45_w6 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 6 1 193022407094229866 = some 193022407094229866 := by decide +kernel
private theorem endpoint_8_45_p7 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 7 193022407094229866 = some 193022407094229866 :=
  join_receipt_window endpoint_8_45_flag endpoint_8_45_sources 0 6 1 193022407094229866 193022407094229866 193022407094229866 endpoint_8_45_p6 endpoint_8_45_w6
def endpoint_8_45 : CertifiedEndpoint :=
  ⟨⟨8, 45, 3867⟩, 193022407094229866, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_45_flag endpoint_8_45_sources 7 193022407094229866 193022407094229866 rfl endpoint_8_45_base endpoint_8_45_p7) (by decide)⟩
private def endpoint_8_46_flag : Flag := ⟨8, 46, 3840⟩
private def endpoint_8_46_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_46_base : receiptBase endpoint_8_46_flag endpoint_8_46_sources = some 195335029332065712 := by decide +kernel
private theorem endpoint_8_46_w0 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 2 195335029332065712 = some 195335029332065712 := by decide +kernel
private theorem endpoint_8_46_w2 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 2 2 195335029332065712 = some 195335029332065712 := by decide +kernel
private theorem endpoint_8_46_p4 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 4 195335029332065712 = some 195335029332065712 :=
  join_receipt_window endpoint_8_46_flag endpoint_8_46_sources 0 2 2 195335029332065712 195335029332065712 195335029332065712 endpoint_8_46_w0 endpoint_8_46_w2
private theorem endpoint_8_46_w4 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 4 2 195335029332065712 = some 195335029332065712 := by decide +kernel
private theorem endpoint_8_46_p6 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 6 195335029332065712 = some 195335029332065712 :=
  join_receipt_window endpoint_8_46_flag endpoint_8_46_sources 0 4 2 195335029332065712 195335029332065712 195335029332065712 endpoint_8_46_p4 endpoint_8_46_w4
private theorem endpoint_8_46_w6 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 6 1 195335029332065712 = some 195335029332065712 := by decide +kernel
private theorem endpoint_8_46_p7 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 7 195335029332065712 = some 195335029332065712 :=
  join_receipt_window endpoint_8_46_flag endpoint_8_46_sources 0 6 1 195335029332065712 195335029332065712 195335029332065712 endpoint_8_46_p6 endpoint_8_46_w6
def endpoint_8_46 : CertifiedEndpoint :=
  ⟨⟨8, 46, 3840⟩, 195335029332065712, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_46_flag endpoint_8_46_sources 7 195335029332065712 195335029332065712 rfl endpoint_8_46_base endpoint_8_46_p7) (by decide)⟩
private def endpoint_8_47_flag : Flag := ⟨8, 47, 3813⟩
private def endpoint_8_47_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_47_base : receiptBase endpoint_8_47_flag endpoint_8_47_sources = some 197596348627770008 := by decide +kernel
private theorem endpoint_8_47_w0 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 2 197596348627770008 = some 197596348627770008 := by decide +kernel
private theorem endpoint_8_47_w2 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 2 2 197596348627770008 = some 197596348627770008 := by decide +kernel
private theorem endpoint_8_47_p4 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 4 197596348627770008 = some 197596348627770008 :=
  join_receipt_window endpoint_8_47_flag endpoint_8_47_sources 0 2 2 197596348627770008 197596348627770008 197596348627770008 endpoint_8_47_w0 endpoint_8_47_w2
private theorem endpoint_8_47_w4 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 4 2 197596348627770008 = some 197596348627770008 := by decide +kernel
private theorem endpoint_8_47_p6 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 6 197596348627770008 = some 197596348627770008 :=
  join_receipt_window endpoint_8_47_flag endpoint_8_47_sources 0 4 2 197596348627770008 197596348627770008 197596348627770008 endpoint_8_47_p4 endpoint_8_47_w4
private theorem endpoint_8_47_w6 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 6 1 197596348627770008 = some 197596348627770008 := by decide +kernel
private theorem endpoint_8_47_p7 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 7 197596348627770008 = some 197596348627770008 :=
  join_receipt_window endpoint_8_47_flag endpoint_8_47_sources 0 6 1 197596348627770008 197596348627770008 197596348627770008 endpoint_8_47_p6 endpoint_8_47_w6
def endpoint_8_47 : CertifiedEndpoint :=
  ⟨⟨8, 47, 3813⟩, 197596348627770008, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_47_flag endpoint_8_47_sources 7 197596348627770008 197596348627770008 rfl endpoint_8_47_base endpoint_8_47_p7) (by decide)⟩
private def endpoint_8_48_flag : Flag := ⟨8, 48, 3786⟩
private def endpoint_8_48_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_48_base : receiptBase endpoint_8_48_flag endpoint_8_48_sources = some 199806364981342755 := by decide +kernel
private theorem endpoint_8_48_w0 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 2 199806364981342755 = some 199806364981342755 := by decide +kernel
private theorem endpoint_8_48_w2 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 2 2 199806364981342755 = some 199806364981342755 := by decide +kernel
private theorem endpoint_8_48_p4 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 4 199806364981342755 = some 199806364981342755 :=
  join_receipt_window endpoint_8_48_flag endpoint_8_48_sources 0 2 2 199806364981342755 199806364981342755 199806364981342755 endpoint_8_48_w0 endpoint_8_48_w2
private theorem endpoint_8_48_w4 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 4 2 199806364981342755 = some 199806364981342755 := by decide +kernel
private theorem endpoint_8_48_p6 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 6 199806364981342755 = some 199806364981342755 :=
  join_receipt_window endpoint_8_48_flag endpoint_8_48_sources 0 4 2 199806364981342755 199806364981342755 199806364981342755 endpoint_8_48_p4 endpoint_8_48_w4
private theorem endpoint_8_48_w6 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 6 1 199806364981342755 = some 199806364981342755 := by decide +kernel
private theorem endpoint_8_48_p7 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 7 199806364981342755 = some 199806364981342755 :=
  join_receipt_window endpoint_8_48_flag endpoint_8_48_sources 0 6 1 199806364981342755 199806364981342755 199806364981342755 endpoint_8_48_p6 endpoint_8_48_w6
def endpoint_8_48 : CertifiedEndpoint :=
  ⟨⟨8, 48, 3786⟩, 199806364981342755, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_48_flag endpoint_8_48_sources 7 199806364981342755 199806364981342755 rfl endpoint_8_48_base endpoint_8_48_p7) (by decide)⟩
private def endpoint_8_49_flag : Flag := ⟨8, 49, 3757⟩
private def endpoint_8_49_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_49_base : receiptBase endpoint_8_49_flag endpoint_8_49_sources = some 201859340893512905 := by decide +kernel
private theorem endpoint_8_49_w0 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 2 201859340893512905 = some 201859340893512905 := by decide +kernel
private theorem endpoint_8_49_w2 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 2 2 201859340893512905 = some 201859340893512905 := by decide +kernel
private theorem endpoint_8_49_p4 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 4 201859340893512905 = some 201859340893512905 :=
  join_receipt_window endpoint_8_49_flag endpoint_8_49_sources 0 2 2 201859340893512905 201859340893512905 201859340893512905 endpoint_8_49_w0 endpoint_8_49_w2
private theorem endpoint_8_49_w4 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 4 2 201859340893512905 = some 201859340893512905 := by decide +kernel
private theorem endpoint_8_49_p6 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 6 201859340893512905 = some 201859340893512905 :=
  join_receipt_window endpoint_8_49_flag endpoint_8_49_sources 0 4 2 201859340893512905 201859340893512905 201859340893512905 endpoint_8_49_p4 endpoint_8_49_w4
private theorem endpoint_8_49_w6 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 6 1 201859340893512905 = some 201859340893512905 := by decide +kernel
private theorem endpoint_8_49_p7 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 7 201859340893512905 = some 201859340893512905 :=
  join_receipt_window endpoint_8_49_flag endpoint_8_49_sources 0 6 1 201859340893512905 201859340893512905 201859340893512905 endpoint_8_49_p6 endpoint_8_49_w6
def endpoint_8_49 : CertifiedEndpoint :=
  ⟨⟨8, 49, 3757⟩, 201859340893512905, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_49_flag endpoint_8_49_sources 7 201859340893512905 201859340893512905 rfl endpoint_8_49_base endpoint_8_49_p7) (by decide)⟩
private def endpoint_8_50_flag : Flag := ⟨8, 50, 3728⟩
private def endpoint_8_50_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_50_base : receiptBase endpoint_8_50_flag endpoint_8_50_sources = some 203857282740487393 := by decide +kernel
private theorem endpoint_8_50_w0 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 2 203857282740487393 = some 203857282740487393 := by decide +kernel
private theorem endpoint_8_50_w2 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 2 2 203857282740487393 = some 203857282740487393 := by decide +kernel
private theorem endpoint_8_50_p4 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 4 203857282740487393 = some 203857282740487393 :=
  join_receipt_window endpoint_8_50_flag endpoint_8_50_sources 0 2 2 203857282740487393 203857282740487393 203857282740487393 endpoint_8_50_w0 endpoint_8_50_w2
private theorem endpoint_8_50_w4 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 4 2 203857282740487393 = some 203857282740487393 := by decide +kernel
private theorem endpoint_8_50_p6 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 6 203857282740487393 = some 203857282740487393 :=
  join_receipt_window endpoint_8_50_flag endpoint_8_50_sources 0 4 2 203857282740487393 203857282740487393 203857282740487393 endpoint_8_50_p4 endpoint_8_50_w4
private theorem endpoint_8_50_w6 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 6 1 203857282740487393 = some 203857282740487393 := by decide +kernel
private theorem endpoint_8_50_p7 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 7 203857282740487393 = some 203857282740487393 :=
  join_receipt_window endpoint_8_50_flag endpoint_8_50_sources 0 6 1 203857282740487393 203857282740487393 203857282740487393 endpoint_8_50_p6 endpoint_8_50_w6
def endpoint_8_50 : CertifiedEndpoint :=
  ⟨⟨8, 50, 3728⟩, 203857282740487393, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_50_flag endpoint_8_50_sources 7 203857282740487393 203857282740487393 rfl endpoint_8_50_base endpoint_8_50_p7) (by decide)⟩
private def endpoint_8_51_flag : Flag := ⟨8, 51, 3699⟩
private def endpoint_8_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_51_base : receiptBase endpoint_8_51_flag endpoint_8_51_sources = some 206920097267287013 := by decide +kernel
private theorem endpoint_8_51_w0 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 2 206920097267287013 = some 206920097267287013 := by decide +kernel
private theorem endpoint_8_51_w2 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 2 2 206920097267287013 = some 206920097267287013 := by decide +kernel
private theorem endpoint_8_51_p4 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 4 206920097267287013 = some 206920097267287013 :=
  join_receipt_window endpoint_8_51_flag endpoint_8_51_sources 0 2 2 206920097267287013 206920097267287013 206920097267287013 endpoint_8_51_w0 endpoint_8_51_w2
private theorem endpoint_8_51_w4 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 4 2 206920097267287013 = some 206920097267287013 := by decide +kernel
private theorem endpoint_8_51_p6 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 6 206920097267287013 = some 206920097267287013 :=
  join_receipt_window endpoint_8_51_flag endpoint_8_51_sources 0 4 2 206920097267287013 206920097267287013 206920097267287013 endpoint_8_51_p4 endpoint_8_51_w4
private theorem endpoint_8_51_w6 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 6 1 206920097267287013 = some 206920097267287013 := by decide +kernel
private theorem endpoint_8_51_p7 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 7 206920097267287013 = some 206920097267287013 :=
  join_receipt_window endpoint_8_51_flag endpoint_8_51_sources 0 6 1 206920097267287013 206920097267287013 206920097267287013 endpoint_8_51_p6 endpoint_8_51_w6
def endpoint_8_51 : CertifiedEndpoint :=
  ⟨⟨8, 51, 3699⟩, 206920097267287013, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_51_flag endpoint_8_51_sources 7 206920097267287013 206920097267287013 rfl endpoint_8_51_base endpoint_8_51_p7) (by decide)⟩
private def endpoint_8_52_flag : Flag := ⟨8, 52, 3669⟩
private def endpoint_8_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_52_base : receiptBase endpoint_8_52_flag endpoint_8_52_sources = some 208754236753696595 := by decide +kernel
private theorem endpoint_8_52_w0 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 2 208754236753696595 = some 208754236753696595 := by decide +kernel
private theorem endpoint_8_52_w2 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 2 2 208754236753696595 = some 208754236753696595 := by decide +kernel
private theorem endpoint_8_52_p4 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 4 208754236753696595 = some 208754236753696595 :=
  join_receipt_window endpoint_8_52_flag endpoint_8_52_sources 0 2 2 208754236753696595 208754236753696595 208754236753696595 endpoint_8_52_w0 endpoint_8_52_w2
private theorem endpoint_8_52_w4 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 4 2 208754236753696595 = some 208754236753696595 := by decide +kernel
private theorem endpoint_8_52_p6 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 6 208754236753696595 = some 208754236753696595 :=
  join_receipt_window endpoint_8_52_flag endpoint_8_52_sources 0 4 2 208754236753696595 208754236753696595 208754236753696595 endpoint_8_52_p4 endpoint_8_52_w4
private theorem endpoint_8_52_w6 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 6 1 208754236753696595 = some 208754236753696595 := by decide +kernel
private theorem endpoint_8_52_p7 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 7 208754236753696595 = some 208754236753696595 :=
  join_receipt_window endpoint_8_52_flag endpoint_8_52_sources 0 6 1 208754236753696595 208754236753696595 208754236753696595 endpoint_8_52_p6 endpoint_8_52_w6
def endpoint_8_52 : CertifiedEndpoint :=
  ⟨⟨8, 52, 3669⟩, 208754236753696595, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_52_flag endpoint_8_52_sources 7 208754236753696595 208754236753696595 rfl endpoint_8_52_base endpoint_8_52_p7) (by decide)⟩
private def endpoint_8_53_flag : Flag := ⟨8, 53, 3639⟩
private def endpoint_8_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_53_base : receiptBase endpoint_8_53_flag endpoint_8_53_sources = some 210530927476249023 := by decide +kernel
private theorem endpoint_8_53_w0 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 2 210530927476249023 = some 210530927476249023 := by decide +kernel
private theorem endpoint_8_53_w2 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 2 2 210530927476249023 = some 210530927476249023 := by decide +kernel
private theorem endpoint_8_53_p4 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 4 210530927476249023 = some 210530927476249023 :=
  join_receipt_window endpoint_8_53_flag endpoint_8_53_sources 0 2 2 210530927476249023 210530927476249023 210530927476249023 endpoint_8_53_w0 endpoint_8_53_w2
private theorem endpoint_8_53_w4 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 4 2 210530927476249023 = some 210530927476249023 := by decide +kernel
private theorem endpoint_8_53_p6 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 6 210530927476249023 = some 210530927476249023 :=
  join_receipt_window endpoint_8_53_flag endpoint_8_53_sources 0 4 2 210530927476249023 210530927476249023 210530927476249023 endpoint_8_53_p4 endpoint_8_53_w4
private theorem endpoint_8_53_w6 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 6 1 210530927476249023 = some 210530927476249023 := by decide +kernel
private theorem endpoint_8_53_p7 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 7 210530927476249023 = some 210530927476249023 :=
  join_receipt_window endpoint_8_53_flag endpoint_8_53_sources 0 6 1 210530927476249023 210530927476249023 210530927476249023 endpoint_8_53_p6 endpoint_8_53_w6
def endpoint_8_53 : CertifiedEndpoint :=
  ⟨⟨8, 53, 3639⟩, 210530927476249023, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_53_flag endpoint_8_53_sources 7 210530927476249023 210530927476249023 rfl endpoint_8_53_base endpoint_8_53_p7) (by decide)⟩
private def endpoint_8_54_flag : Flag := ⟨8, 54, 3607⟩
private def endpoint_8_54_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_54_base : receiptBase endpoint_8_54_flag endpoint_8_54_sources = some 212134053281008595 := by decide +kernel
private theorem endpoint_8_54_w0 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 2 212134053281008595 = some 212134053281008595 := by decide +kernel
private theorem endpoint_8_54_w2 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 2 2 212134053281008595 = some 212134053281008595 := by decide +kernel
private theorem endpoint_8_54_p4 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 4 212134053281008595 = some 212134053281008595 :=
  join_receipt_window endpoint_8_54_flag endpoint_8_54_sources 0 2 2 212134053281008595 212134053281008595 212134053281008595 endpoint_8_54_w0 endpoint_8_54_w2
private theorem endpoint_8_54_w4 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 4 2 212134053281008595 = some 212134053281008595 := by decide +kernel
private theorem endpoint_8_54_p6 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 6 212134053281008595 = some 212134053281008595 :=
  join_receipt_window endpoint_8_54_flag endpoint_8_54_sources 0 4 2 212134053281008595 212134053281008595 212134053281008595 endpoint_8_54_p4 endpoint_8_54_w4
private theorem endpoint_8_54_w6 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 6 1 212134053281008595 = some 212134053281008595 := by decide +kernel
private theorem endpoint_8_54_p7 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 7 212134053281008595 = some 212134053281008595 :=
  join_receipt_window endpoint_8_54_flag endpoint_8_54_sources 0 6 1 212134053281008595 212134053281008595 212134053281008595 endpoint_8_54_p6 endpoint_8_54_w6
def endpoint_8_54 : CertifiedEndpoint :=
  ⟨⟨8, 54, 3607⟩, 212134053281008595, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_54_flag endpoint_8_54_sources 7 212134053281008595 212134053281008595 rfl endpoint_8_54_base endpoint_8_54_p7) (by decide)⟩
private def endpoint_8_55_flag : Flag := ⟨8, 55, 3575⟩
private def endpoint_8_55_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_55_base : receiptBase endpoint_8_55_flag endpoint_8_55_sources = some 213675963189854805 := by decide +kernel
private theorem endpoint_8_55_w0 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 2 213675963189854805 = some 213675963189854805 := by decide +kernel
private theorem endpoint_8_55_w2 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 2 2 213675963189854805 = some 213675963189854805 := by decide +kernel
private theorem endpoint_8_55_p4 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 4 213675963189854805 = some 213675963189854805 :=
  join_receipt_window endpoint_8_55_flag endpoint_8_55_sources 0 2 2 213675963189854805 213675963189854805 213675963189854805 endpoint_8_55_w0 endpoint_8_55_w2
private theorem endpoint_8_55_w4 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 4 2 213675963189854805 = some 213675963189854805 := by decide +kernel
private theorem endpoint_8_55_p6 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 6 213675963189854805 = some 213675963189854805 :=
  join_receipt_window endpoint_8_55_flag endpoint_8_55_sources 0 4 2 213675963189854805 213675963189854805 213675963189854805 endpoint_8_55_p4 endpoint_8_55_w4
private theorem endpoint_8_55_w6 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 6 1 213675963189854805 = some 213675963189854805 := by decide +kernel
private theorem endpoint_8_55_p7 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 7 213675963189854805 = some 213675963189854805 :=
  join_receipt_window endpoint_8_55_flag endpoint_8_55_sources 0 6 1 213675963189854805 213675963189854805 213675963189854805 endpoint_8_55_p6 endpoint_8_55_w6
def endpoint_8_55 : CertifiedEndpoint :=
  ⟨⟨8, 55, 3575⟩, 213675963189854805, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_55_flag endpoint_8_55_sources 7 213675963189854805 213675963189854805 rfl endpoint_8_55_base endpoint_8_55_p7) (by decide)⟩
private def endpoint_8_56_flag : Flag := ⟨8, 56, 3542⟩
private def endpoint_8_56_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_56_base : receiptBase endpoint_8_56_flag endpoint_8_56_sources = some 215849708957421035 := by decide +kernel
private theorem endpoint_8_56_w0 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 2 215849708957421035 = some 215849708957421035 := by decide +kernel
private theorem endpoint_8_56_w2 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 2 2 215849708957421035 = some 215849708957421035 := by decide +kernel
private theorem endpoint_8_56_p4 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 4 215849708957421035 = some 215849708957421035 :=
  join_receipt_window endpoint_8_56_flag endpoint_8_56_sources 0 2 2 215849708957421035 215849708957421035 215849708957421035 endpoint_8_56_w0 endpoint_8_56_w2
private theorem endpoint_8_56_w4 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 4 2 215849708957421035 = some 215849708957421035 := by decide +kernel
private theorem endpoint_8_56_p6 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 6 215849708957421035 = some 215849708957421035 :=
  join_receipt_window endpoint_8_56_flag endpoint_8_56_sources 0 4 2 215849708957421035 215849708957421035 215849708957421035 endpoint_8_56_p4 endpoint_8_56_w4
private theorem endpoint_8_56_w6 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 6 1 215849708957421035 = some 215849708957421035 := by decide +kernel
private theorem endpoint_8_56_p7 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 7 215849708957421035 = some 215849708957421035 :=
  join_receipt_window endpoint_8_56_flag endpoint_8_56_sources 0 6 1 215849708957421035 215849708957421035 215849708957421035 endpoint_8_56_p6 endpoint_8_56_w6
def endpoint_8_56 : CertifiedEndpoint :=
  ⟨⟨8, 56, 3542⟩, 215849708957421035, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_56_flag endpoint_8_56_sources 7 215849708957421035 215849708957421035 rfl endpoint_8_56_base endpoint_8_56_p7) (by decide)⟩
private def endpoint_8_57_flag : Flag := ⟨8, 57, 3509⟩
private def endpoint_8_57_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_57_base : receiptBase endpoint_8_57_flag endpoint_8_57_sources = some 217200016658753919 := by decide +kernel
private theorem endpoint_8_57_w0 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 2 217200016658753919 = some 217200016658753919 := by decide +kernel
private theorem endpoint_8_57_w2 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 2 2 217200016658753919 = some 217200016658753919 := by decide +kernel
private theorem endpoint_8_57_p4 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 4 217200016658753919 = some 217200016658753919 :=
  join_receipt_window endpoint_8_57_flag endpoint_8_57_sources 0 2 2 217200016658753919 217200016658753919 217200016658753919 endpoint_8_57_w0 endpoint_8_57_w2
private theorem endpoint_8_57_w4 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 4 2 217200016658753919 = some 217200016658753919 := by decide +kernel
private theorem endpoint_8_57_p6 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 6 217200016658753919 = some 217200016658753919 :=
  join_receipt_window endpoint_8_57_flag endpoint_8_57_sources 0 4 2 217200016658753919 217200016658753919 217200016658753919 endpoint_8_57_p4 endpoint_8_57_w4
private theorem endpoint_8_57_w6 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 6 1 217200016658753919 = some 217200016658753919 := by decide +kernel
private theorem endpoint_8_57_p7 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 7 217200016658753919 = some 217200016658753919 :=
  join_receipt_window endpoint_8_57_flag endpoint_8_57_sources 0 6 1 217200016658753919 217200016658753919 217200016658753919 endpoint_8_57_p6 endpoint_8_57_w6
def endpoint_8_57 : CertifiedEndpoint :=
  ⟨⟨8, 57, 3509⟩, 217200016658753919, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_57_flag endpoint_8_57_sources 7 217200016658753919 217200016658753919 rfl endpoint_8_57_base endpoint_8_57_p7) (by decide)⟩
private def endpoint_8_58_flag : Flag := ⟨8, 58, 3474⟩
private def endpoint_8_58_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_58_base : receiptBase endpoint_8_58_flag endpoint_8_58_sources = some 218363142449660836 := by decide +kernel
private theorem endpoint_8_58_w0 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 2 218363142449660836 = some 218363142449660836 := by decide +kernel
private theorem endpoint_8_58_w2 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 2 2 218363142449660836 = some 218363142449660836 := by decide +kernel
private theorem endpoint_8_58_p4 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 4 218363142449660836 = some 218363142449660836 :=
  join_receipt_window endpoint_8_58_flag endpoint_8_58_sources 0 2 2 218363142449660836 218363142449660836 218363142449660836 endpoint_8_58_w0 endpoint_8_58_w2
private theorem endpoint_8_58_w4 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 4 2 218363142449660836 = some 218363142449660836 := by decide +kernel
private theorem endpoint_8_58_p6 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 6 218363142449660836 = some 218363142449660836 :=
  join_receipt_window endpoint_8_58_flag endpoint_8_58_sources 0 4 2 218363142449660836 218363142449660836 218363142449660836 endpoint_8_58_p4 endpoint_8_58_w4
private theorem endpoint_8_58_w6 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 6 1 218363142449660836 = some 218363142449660836 := by decide +kernel
private theorem endpoint_8_58_p7 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 7 218363142449660836 = some 218363142449660836 :=
  join_receipt_window endpoint_8_58_flag endpoint_8_58_sources 0 6 1 218363142449660836 218363142449660836 218363142449660836 endpoint_8_58_p6 endpoint_8_58_w6
def endpoint_8_58 : CertifiedEndpoint :=
  ⟨⟨8, 58, 3474⟩, 218363142449660836, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_58_flag endpoint_8_58_sources 7 218363142449660836 218363142449660836 rfl endpoint_8_58_base endpoint_8_58_p7) (by decide)⟩
private def endpoint_8_59_flag : Flag := ⟨8, 59, 3438⟩
private def endpoint_8_59_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_59_base : receiptBase endpoint_8_59_flag endpoint_8_59_sources = some 219396418639313778 := by decide +kernel
private theorem endpoint_8_59_w0 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 2 219396418639313778 = some 219396418639313778 := by decide +kernel
private theorem endpoint_8_59_w2 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 2 2 219396418639313778 = some 219396418639313778 := by decide +kernel
private theorem endpoint_8_59_p4 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 4 219396418639313778 = some 219396418639313778 :=
  join_receipt_window endpoint_8_59_flag endpoint_8_59_sources 0 2 2 219396418639313778 219396418639313778 219396418639313778 endpoint_8_59_w0 endpoint_8_59_w2
private theorem endpoint_8_59_w4 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 4 2 219396418639313778 = some 219396418639313778 := by decide +kernel
private theorem endpoint_8_59_p6 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 6 219396418639313778 = some 219396418639313778 :=
  join_receipt_window endpoint_8_59_flag endpoint_8_59_sources 0 4 2 219396418639313778 219396418639313778 219396418639313778 endpoint_8_59_p4 endpoint_8_59_w4
private theorem endpoint_8_59_w6 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 6 1 219396418639313778 = some 219396418639313778 := by decide +kernel
private theorem endpoint_8_59_p7 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 7 219396418639313778 = some 219396418639313778 :=
  join_receipt_window endpoint_8_59_flag endpoint_8_59_sources 0 6 1 219396418639313778 219396418639313778 219396418639313778 endpoint_8_59_p6 endpoint_8_59_w6
def endpoint_8_59 : CertifiedEndpoint :=
  ⟨⟨8, 59, 3438⟩, 219396418639313778, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_59_flag endpoint_8_59_sources 7 219396418639313778 219396418639313778 rfl endpoint_8_59_base endpoint_8_59_p7) (by decide)⟩
private def endpoint_8_60_flag : Flag := ⟨8, 60, 3401⟩
private def endpoint_8_60_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_60_base : receiptBase endpoint_8_60_flag endpoint_8_60_sources = some 220297019878670591 := by decide +kernel
private theorem endpoint_8_60_w0 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 2 220297019878670591 = some 220297019878670591 := by decide +kernel
private theorem endpoint_8_60_w2 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 2 2 220297019878670591 = some 220297019878670591 := by decide +kernel
private theorem endpoint_8_60_p4 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 4 220297019878670591 = some 220297019878670591 :=
  join_receipt_window endpoint_8_60_flag endpoint_8_60_sources 0 2 2 220297019878670591 220297019878670591 220297019878670591 endpoint_8_60_w0 endpoint_8_60_w2
private theorem endpoint_8_60_w4 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 4 2 220297019878670591 = some 220297019878670591 := by decide +kernel
private theorem endpoint_8_60_p6 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 6 220297019878670591 = some 220297019878670591 :=
  join_receipt_window endpoint_8_60_flag endpoint_8_60_sources 0 4 2 220297019878670591 220297019878670591 220297019878670591 endpoint_8_60_p4 endpoint_8_60_w4
private theorem endpoint_8_60_w6 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 6 1 220297019878670591 = some 220297019878670591 := by decide +kernel
private theorem endpoint_8_60_p7 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 7 220297019878670591 = some 220297019878670591 :=
  join_receipt_window endpoint_8_60_flag endpoint_8_60_sources 0 6 1 220297019878670591 220297019878670591 220297019878670591 endpoint_8_60_p6 endpoint_8_60_w6
def endpoint_8_60 : CertifiedEndpoint :=
  ⟨⟨8, 60, 3401⟩, 220297019878670591, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_60_flag endpoint_8_60_sources 7 220297019878670591 220297019878670591 rfl endpoint_8_60_base endpoint_8_60_p7) (by decide)⟩
private def endpoint_8_61_flag : Flag := ⟨8, 61, 3364⟩
private def endpoint_8_61_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_61_base : receiptBase endpoint_8_61_flag endpoint_8_61_sources = some 223349519353233339 := by decide +kernel
private theorem endpoint_8_61_w0 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 2 223349519353233339 = some 223349519353233339 := by decide +kernel
private theorem endpoint_8_61_w2 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 2 2 223349519353233339 = some 223349519353233339 := by decide +kernel
private theorem endpoint_8_61_p4 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 4 223349519353233339 = some 223349519353233339 :=
  join_receipt_window endpoint_8_61_flag endpoint_8_61_sources 0 2 2 223349519353233339 223349519353233339 223349519353233339 endpoint_8_61_w0 endpoint_8_61_w2
private theorem endpoint_8_61_w4 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 4 2 223349519353233339 = some 223349519353233339 := by decide +kernel
private theorem endpoint_8_61_p6 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 6 223349519353233339 = some 223349519353233339 :=
  join_receipt_window endpoint_8_61_flag endpoint_8_61_sources 0 4 2 223349519353233339 223349519353233339 223349519353233339 endpoint_8_61_p4 endpoint_8_61_w4
private theorem endpoint_8_61_w6 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 6 1 223349519353233339 = some 223349519353233339 := by decide +kernel
private theorem endpoint_8_61_p7 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 7 223349519353233339 = some 223349519353233339 :=
  join_receipt_window endpoint_8_61_flag endpoint_8_61_sources 0 6 1 223349519353233339 223349519353233339 223349519353233339 endpoint_8_61_p6 endpoint_8_61_w6
def endpoint_8_61 : CertifiedEndpoint :=
  ⟨⟨8, 61, 3364⟩, 223349519353233339, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_61_flag endpoint_8_61_sources 7 223349519353233339 223349519353233339 rfl endpoint_8_61_base endpoint_8_61_p7) (by decide)⟩
private def endpoint_8_62_flag : Flag := ⟨8, 62, 3324⟩
private def endpoint_8_62_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_62_base : receiptBase endpoint_8_62_flag endpoint_8_62_sources = some 223896800520188741 := by decide +kernel
private theorem endpoint_8_62_w0 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 2 223896800520188741 = some 223896800520188741 := by decide +kernel
private theorem endpoint_8_62_w2 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 2 2 223896800520188741 = some 223896800520188741 := by decide +kernel
private theorem endpoint_8_62_p4 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 4 223896800520188741 = some 223896800520188741 :=
  join_receipt_window endpoint_8_62_flag endpoint_8_62_sources 0 2 2 223896800520188741 223896800520188741 223896800520188741 endpoint_8_62_w0 endpoint_8_62_w2
private theorem endpoint_8_62_w4 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 4 2 223896800520188741 = some 223896800520188741 := by decide +kernel
private theorem endpoint_8_62_p6 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 6 223896800520188741 = some 223896800520188741 :=
  join_receipt_window endpoint_8_62_flag endpoint_8_62_sources 0 4 2 223896800520188741 223896800520188741 223896800520188741 endpoint_8_62_p4 endpoint_8_62_w4
private theorem endpoint_8_62_w6 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 6 1 223896800520188741 = some 223896800520188741 := by decide +kernel
private theorem endpoint_8_62_p7 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 7 223896800520188741 = some 223896800520188741 :=
  join_receipt_window endpoint_8_62_flag endpoint_8_62_sources 0 6 1 223896800520188741 223896800520188741 223896800520188741 endpoint_8_62_p6 endpoint_8_62_w6
def endpoint_8_62 : CertifiedEndpoint :=
  ⟨⟨8, 62, 3324⟩, 223896800520188741, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_62_flag endpoint_8_62_sources 7 223896800520188741 223896800520188741 rfl endpoint_8_62_base endpoint_8_62_p7) (by decide)⟩
private def endpoint_8_63_flag : Flag := ⟨8, 63, 3284⟩
private def endpoint_8_63_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_63_base : receiptBase endpoint_8_63_flag endpoint_8_63_sources = some 224367068634589712 := by decide +kernel
private theorem endpoint_8_63_w0 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 2 224367068634589712 = some 224367068634589712 := by decide +kernel
private theorem endpoint_8_63_w2 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 2 2 224367068634589712 = some 224367068634589712 := by decide +kernel
private theorem endpoint_8_63_p4 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 4 224367068634589712 = some 224367068634589712 :=
  join_receipt_window endpoint_8_63_flag endpoint_8_63_sources 0 2 2 224367068634589712 224367068634589712 224367068634589712 endpoint_8_63_w0 endpoint_8_63_w2
private theorem endpoint_8_63_w4 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 4 2 224367068634589712 = some 224367068634589712 := by decide +kernel
private theorem endpoint_8_63_p6 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 6 224367068634589712 = some 224367068634589712 :=
  join_receipt_window endpoint_8_63_flag endpoint_8_63_sources 0 4 2 224367068634589712 224367068634589712 224367068634589712 endpoint_8_63_p4 endpoint_8_63_w4
private theorem endpoint_8_63_w6 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 6 1 224367068634589712 = some 224367068634589712 := by decide +kernel
private theorem endpoint_8_63_p7 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 7 224367068634589712 = some 224367068634589712 :=
  join_receipt_window endpoint_8_63_flag endpoint_8_63_sources 0 6 1 224367068634589712 224367068634589712 224367068634589712 endpoint_8_63_p6 endpoint_8_63_w6
def endpoint_8_63 : CertifiedEndpoint :=
  ⟨⟨8, 63, 3284⟩, 224367068634589712, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_63_flag endpoint_8_63_sources 7 224367068634589712 224367068634589712 rfl endpoint_8_63_base endpoint_8_63_p7) (by decide)⟩
private def endpoint_8_64_flag : Flag := ⟨8, 64, 3241⟩
private def endpoint_8_64_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_64_base : receiptBase endpoint_8_64_flag endpoint_8_64_sources = some 224554642324210196 := by decide +kernel
private theorem endpoint_8_64_w0 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 2 224554642324210196 = some 224554642324210196 := by decide +kernel
private theorem endpoint_8_64_w2 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 2 2 224554642324210196 = some 224554642324210196 := by decide +kernel
private theorem endpoint_8_64_p4 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 4 224554642324210196 = some 224554642324210196 :=
  join_receipt_window endpoint_8_64_flag endpoint_8_64_sources 0 2 2 224554642324210196 224554642324210196 224554642324210196 endpoint_8_64_w0 endpoint_8_64_w2
private theorem endpoint_8_64_w4 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 4 2 224554642324210196 = some 224554642324210196 := by decide +kernel
private theorem endpoint_8_64_p6 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 6 224554642324210196 = some 224554642324210196 :=
  join_receipt_window endpoint_8_64_flag endpoint_8_64_sources 0 4 2 224554642324210196 224554642324210196 224554642324210196 endpoint_8_64_p4 endpoint_8_64_w4
private theorem endpoint_8_64_w6 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 6 1 224554642324210196 = some 224554642324210196 := by decide +kernel
private theorem endpoint_8_64_p7 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 7 224554642324210196 = some 224554642324210196 :=
  join_receipt_window endpoint_8_64_flag endpoint_8_64_sources 0 6 1 224554642324210196 224554642324210196 224554642324210196 endpoint_8_64_p6 endpoint_8_64_w6
def endpoint_8_64 : CertifiedEndpoint :=
  ⟨⟨8, 64, 3241⟩, 224554642324210196, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_64_flag endpoint_8_64_sources 7 224554642324210196 224554642324210196 rfl endpoint_8_64_base endpoint_8_64_p7) (by decide)⟩
private def endpoint_8_65_flag : Flag := ⟨8, 65, 3197⟩
private def endpoint_8_65_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_8_65_base : receiptBase endpoint_8_65_flag endpoint_8_65_sources = some 226032833720007814 := by decide +kernel
private theorem endpoint_8_65_w0 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 2 226032833720007814 = some 226032833720007814 := by decide +kernel
private theorem endpoint_8_65_w2 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 2 2 226032833720007814 = some 226032833720007814 := by decide +kernel
private theorem endpoint_8_65_p4 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 4 226032833720007814 = some 226032833720007814 :=
  join_receipt_window endpoint_8_65_flag endpoint_8_65_sources 0 2 2 226032833720007814 226032833720007814 226032833720007814 endpoint_8_65_w0 endpoint_8_65_w2
private theorem endpoint_8_65_w4 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 4 2 226032833720007814 = some 226032833720007814 := by decide +kernel
private theorem endpoint_8_65_p6 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 6 226032833720007814 = some 226032833720007814 :=
  join_receipt_window endpoint_8_65_flag endpoint_8_65_sources 0 4 2 226032833720007814 226032833720007814 226032833720007814 endpoint_8_65_p4 endpoint_8_65_w4
private theorem endpoint_8_65_w6 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 6 1 226032833720007814 = some 226032833720007814 := by decide +kernel
private theorem endpoint_8_65_p7 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 7 226032833720007814 = some 226032833720007814 :=
  join_receipt_window endpoint_8_65_flag endpoint_8_65_sources 0 6 1 226032833720007814 226032833720007814 226032833720007814 endpoint_8_65_p6 endpoint_8_65_w6
def endpoint_8_65 : CertifiedEndpoint :=
  ⟨⟨8, 65, 3197⟩, 226032833720007814, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_8_65_flag endpoint_8_65_sources 7 226032833720007814 226032833720007814 rfl endpoint_8_65_base endpoint_8_65_p7) (by decide)⟩
private def endpoint_8_66_flag : Flag := ⟨8, 66, 3151⟩
private def endpoint_8_66_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_8_66_base : receiptBase endpoint_8_66_flag endpoint_8_66_sources = some 225843968825326983 := by decide +kernel
private theorem endpoint_8_66_w0 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 2 225843968825326983 = some 225843968825326983 := by decide +kernel
private theorem endpoint_8_66_w2 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 2 2 225843968825326983 = some 225843968825326983 := by decide +kernel
private theorem endpoint_8_66_p4 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 4 225843968825326983 = some 225843968825326983 :=
  join_receipt_window endpoint_8_66_flag endpoint_8_66_sources 0 2 2 225843968825326983 225843968825326983 225843968825326983 endpoint_8_66_w0 endpoint_8_66_w2
private theorem endpoint_8_66_w4 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 4 2 225843968825326983 = some 225843968825326983 := by decide +kernel
private theorem endpoint_8_66_p6 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 6 225843968825326983 = some 225843968825326983 :=
  join_receipt_window endpoint_8_66_flag endpoint_8_66_sources 0 4 2 225843968825326983 225843968825326983 225843968825326983 endpoint_8_66_p4 endpoint_8_66_w4
private theorem endpoint_8_66_w6 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 6 1 225843968825326983 = some 225843968825326983 := by decide +kernel
private theorem endpoint_8_66_p7 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 7 225843968825326983 = some 225843968825326983 :=
  join_receipt_window endpoint_8_66_flag endpoint_8_66_sources 0 6 1 225843968825326983 225843968825326983 225843968825326983 endpoint_8_66_p6 endpoint_8_66_w6
def endpoint_8_66 : CertifiedEndpoint :=
  ⟨⟨8, 66, 3151⟩, 225843968825326983, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_8_66_flag endpoint_8_66_sources 7 225843968825326983 225843968825326983 rfl endpoint_8_66_base endpoint_8_66_p7) (by decide)⟩
private def endpoint_8_67_flag : Flag := ⟨8, 67, 3102⟩
private def endpoint_8_67_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_8_67_base : receiptBase endpoint_8_67_flag endpoint_8_67_sources = some 225350022779137482 := by decide +kernel
private theorem endpoint_8_67_w0 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 2 225350022779137482 = some 225350022779137482 := by decide +kernel
private theorem endpoint_8_67_w2 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 2 2 225350022779137482 = some 225350022779137482 := by decide +kernel
private theorem endpoint_8_67_p4 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 4 225350022779137482 = some 225350022779137482 :=
  join_receipt_window endpoint_8_67_flag endpoint_8_67_sources 0 2 2 225350022779137482 225350022779137482 225350022779137482 endpoint_8_67_w0 endpoint_8_67_w2
private theorem endpoint_8_67_w4 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 4 2 225350022779137482 = some 225350022779137482 := by decide +kernel
private theorem endpoint_8_67_p6 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 6 225350022779137482 = some 225350022779137482 :=
  join_receipt_window endpoint_8_67_flag endpoint_8_67_sources 0 4 2 225350022779137482 225350022779137482 225350022779137482 endpoint_8_67_p4 endpoint_8_67_w4
private theorem endpoint_8_67_w6 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 6 1 225350022779137482 = some 225350022779137482 := by decide +kernel
private theorem endpoint_8_67_p7 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 7 225350022779137482 = some 225350022779137482 :=
  join_receipt_window endpoint_8_67_flag endpoint_8_67_sources 0 6 1 225350022779137482 225350022779137482 225350022779137482 endpoint_8_67_p6 endpoint_8_67_w6
def endpoint_8_67 : CertifiedEndpoint :=
  ⟨⟨8, 67, 3102⟩, 225350022779137482, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_8_67_flag endpoint_8_67_sources 7 225350022779137482 225350022779137482 rfl endpoint_8_67_base endpoint_8_67_p7) (by decide)⟩
private def endpoint_8_68_flag : Flag := ⟨8, 68, 3051⟩
private def endpoint_8_68_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_8_68_base : receiptBase endpoint_8_68_flag endpoint_8_68_sources = some 226106524834944464 := by decide +kernel
private theorem endpoint_8_68_w0 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 2 226106524834944464 = some 226106524834944464 := by decide +kernel
private theorem endpoint_8_68_w2 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 2 2 226106524834944464 = some 226106524834944464 := by decide +kernel
private theorem endpoint_8_68_p4 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 4 226106524834944464 = some 226106524834944464 :=
  join_receipt_window endpoint_8_68_flag endpoint_8_68_sources 0 2 2 226106524834944464 226106524834944464 226106524834944464 endpoint_8_68_w0 endpoint_8_68_w2
private theorem endpoint_8_68_w4 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 4 2 226106524834944464 = some 226106524834944464 := by decide +kernel
private theorem endpoint_8_68_p6 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 6 226106524834944464 = some 226106524834944464 :=
  join_receipt_window endpoint_8_68_flag endpoint_8_68_sources 0 4 2 226106524834944464 226106524834944464 226106524834944464 endpoint_8_68_p4 endpoint_8_68_w4
private theorem endpoint_8_68_w6 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 6 1 226106524834944464 = some 226106524834944464 := by decide +kernel
private theorem endpoint_8_68_p7 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 7 226106524834944464 = some 226106524834944464 :=
  join_receipt_window endpoint_8_68_flag endpoint_8_68_sources 0 6 1 226106524834944464 226106524834944464 226106524834944464 endpoint_8_68_p6 endpoint_8_68_w6
def endpoint_8_68 : CertifiedEndpoint :=
  ⟨⟨8, 68, 3051⟩, 226106524834944464, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_8_68_flag endpoint_8_68_sources 7 226106524834944464 226106524834944464 rfl endpoint_8_68_base endpoint_8_68_p7) (by decide)⟩
private def endpoint_8_69_flag : Flag := ⟨8, 69, 2998⟩
private def endpoint_8_69_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_8_69_base : receiptBase endpoint_8_69_flag endpoint_8_69_sources = some 225120976737691194 := by decide +kernel
private theorem endpoint_8_69_w0 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 2 225120976737691194 = some 225120976737691194 := by decide +kernel
private theorem endpoint_8_69_w2 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 2 2 225120976737691194 = some 225120976737691194 := by decide +kernel
private theorem endpoint_8_69_p4 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 4 225120976737691194 = some 225120976737691194 :=
  join_receipt_window endpoint_8_69_flag endpoint_8_69_sources 0 2 2 225120976737691194 225120976737691194 225120976737691194 endpoint_8_69_w0 endpoint_8_69_w2
private theorem endpoint_8_69_w4 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 4 2 225120976737691194 = some 225120976737691194 := by decide +kernel
private theorem endpoint_8_69_p6 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 6 225120976737691194 = some 225120976737691194 :=
  join_receipt_window endpoint_8_69_flag endpoint_8_69_sources 0 4 2 225120976737691194 225120976737691194 225120976737691194 endpoint_8_69_p4 endpoint_8_69_w4
private theorem endpoint_8_69_w6 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 6 1 225120976737691194 = some 225120976737691194 := by decide +kernel
private theorem endpoint_8_69_p7 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 7 225120976737691194 = some 225120976737691194 :=
  join_receipt_window endpoint_8_69_flag endpoint_8_69_sources 0 6 1 225120976737691194 225120976737691194 225120976737691194 endpoint_8_69_p6 endpoint_8_69_w6
def endpoint_8_69 : CertifiedEndpoint :=
  ⟨⟨8, 69, 2998⟩, 225120976737691194, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_8_69_flag endpoint_8_69_sources 7 225120976737691194 225120976737691194 rfl endpoint_8_69_base endpoint_8_69_p7) (by decide)⟩
private def endpoint_8_70_flag : Flag := ⟨8, 70, 2941⟩
private def endpoint_8_70_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_8_70_base : receiptBase endpoint_8_70_flag endpoint_8_70_sources = some 225251864893542690 := by decide +kernel
private theorem endpoint_8_70_w0 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 2 225251864893542690 = some 225251864893542690 := by decide +kernel
private theorem endpoint_8_70_w2 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 2 2 225251864893542690 = some 225251864893542690 := by decide +kernel
private theorem endpoint_8_70_p4 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 4 225251864893542690 = some 225251864893542690 :=
  join_receipt_window endpoint_8_70_flag endpoint_8_70_sources 0 2 2 225251864893542690 225251864893542690 225251864893542690 endpoint_8_70_w0 endpoint_8_70_w2
private theorem endpoint_8_70_w4 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 4 2 225251864893542690 = some 225251864893542690 := by decide +kernel
private theorem endpoint_8_70_p6 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 6 225251864893542690 = some 225251864893542690 :=
  join_receipt_window endpoint_8_70_flag endpoint_8_70_sources 0 4 2 225251864893542690 225251864893542690 225251864893542690 endpoint_8_70_p4 endpoint_8_70_w4
private theorem endpoint_8_70_w6 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 6 1 225251864893542690 = some 225251864893542690 := by decide +kernel
private theorem endpoint_8_70_p7 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 7 225251864893542690 = some 225251864893542690 :=
  join_receipt_window endpoint_8_70_flag endpoint_8_70_sources 0 6 1 225251864893542690 225251864893542690 225251864893542690 endpoint_8_70_p6 endpoint_8_70_w6
def endpoint_8_70 : CertifiedEndpoint :=
  ⟨⟨8, 70, 2941⟩, 225251864893542690, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_8_70_flag endpoint_8_70_sources 7 225251864893542690 225251864893542690 rfl endpoint_8_70_base endpoint_8_70_p7) (by decide)⟩
private def endpoint_8_71_flag : Flag := ⟨8, 71, 2882⟩
private def endpoint_8_71_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_8_71_base : receiptBase endpoint_8_71_flag endpoint_8_71_sources = some 225134559436119359 := by decide +kernel
private theorem endpoint_8_71_w0 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 2 225134559436119359 = some 225134559436119359 := by decide +kernel
private theorem endpoint_8_71_w2 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 2 2 225134559436119359 = some 225134559436119359 := by decide +kernel
private theorem endpoint_8_71_p4 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 4 225134559436119359 = some 225134559436119359 :=
  join_receipt_window endpoint_8_71_flag endpoint_8_71_sources 0 2 2 225134559436119359 225134559436119359 225134559436119359 endpoint_8_71_w0 endpoint_8_71_w2
private theorem endpoint_8_71_w4 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 4 2 225134559436119359 = some 225134559436119359 := by decide +kernel
private theorem endpoint_8_71_p6 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 6 225134559436119359 = some 225134559436119359 :=
  join_receipt_window endpoint_8_71_flag endpoint_8_71_sources 0 4 2 225134559436119359 225134559436119359 225134559436119359 endpoint_8_71_p4 endpoint_8_71_w4
private theorem endpoint_8_71_w6 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 6 1 225134559436119359 = some 225134559436119359 := by decide +kernel
private theorem endpoint_8_71_p7 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 7 225134559436119359 = some 225134559436119359 :=
  join_receipt_window endpoint_8_71_flag endpoint_8_71_sources 0 6 1 225134559436119359 225134559436119359 225134559436119359 endpoint_8_71_p6 endpoint_8_71_w6
def endpoint_8_71 : CertifiedEndpoint :=
  ⟨⟨8, 71, 2882⟩, 225134559436119359, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_8_71_flag endpoint_8_71_sources 7 225134559436119359 225134559436119359 rfl endpoint_8_71_base endpoint_8_71_p7) (by decide)⟩
private def endpoint_8_72_flag : Flag := ⟨8, 72, 2821⟩
private def endpoint_8_72_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_8_72_base : receiptBase endpoint_8_72_flag endpoint_8_72_sources = some 224625498672217266 := by decide +kernel
private theorem endpoint_8_72_w0 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 2 224625498672217266 = some 224625498672217266 := by decide +kernel
private theorem endpoint_8_72_w2 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 2 2 224625498672217266 = some 224625498672217266 := by decide +kernel
private theorem endpoint_8_72_p4 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 4 224625498672217266 = some 224625498672217266 :=
  join_receipt_window endpoint_8_72_flag endpoint_8_72_sources 0 2 2 224625498672217266 224625498672217266 224625498672217266 endpoint_8_72_w0 endpoint_8_72_w2
private theorem endpoint_8_72_w4 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 4 2 224625498672217266 = some 224625498672217266 := by decide +kernel
private theorem endpoint_8_72_p6 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 6 224625498672217266 = some 224625498672217266 :=
  join_receipt_window endpoint_8_72_flag endpoint_8_72_sources 0 4 2 224625498672217266 224625498672217266 224625498672217266 endpoint_8_72_p4 endpoint_8_72_w4
private theorem endpoint_8_72_w6 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 6 1 224625498672217266 = some 224625498672217266 := by decide +kernel
private theorem endpoint_8_72_p7 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 7 224625498672217266 = some 224625498672217266 :=
  join_receipt_window endpoint_8_72_flag endpoint_8_72_sources 0 6 1 224625498672217266 224625498672217266 224625498672217266 endpoint_8_72_p6 endpoint_8_72_w6
def endpoint_8_72 : CertifiedEndpoint :=
  ⟨⟨8, 72, 2821⟩, 224625498672217266, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_8_72_flag endpoint_8_72_sources 7 224625498672217266 224625498672217266 rfl endpoint_8_72_base endpoint_8_72_p7) (by decide)⟩
private def endpoint_8_73_flag : Flag := ⟨8, 73, 2757⟩
private def endpoint_8_73_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_8_73_base : receiptBase endpoint_8_73_flag endpoint_8_73_sources = some 222304514227755112 := by decide +kernel
private theorem endpoint_8_73_w0 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 2 222304514227755112 = some 222304514227755112 := by decide +kernel
private theorem endpoint_8_73_w2 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 2 2 222304514227755112 = some 222304514227755112 := by decide +kernel
private theorem endpoint_8_73_p4 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 4 222304514227755112 = some 222304514227755112 :=
  join_receipt_window endpoint_8_73_flag endpoint_8_73_sources 0 2 2 222304514227755112 222304514227755112 222304514227755112 endpoint_8_73_w0 endpoint_8_73_w2
private theorem endpoint_8_73_w4 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 4 2 222304514227755112 = some 222304514227755112 := by decide +kernel
private theorem endpoint_8_73_p6 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 6 222304514227755112 = some 222304514227755112 :=
  join_receipt_window endpoint_8_73_flag endpoint_8_73_sources 0 4 2 222304514227755112 222304514227755112 222304514227755112 endpoint_8_73_p4 endpoint_8_73_w4
private theorem endpoint_8_73_w6 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 6 1 222304514227755112 = some 222304514227755112 := by decide +kernel
private theorem endpoint_8_73_p7 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 7 222304514227755112 = some 222304514227755112 :=
  join_receipt_window endpoint_8_73_flag endpoint_8_73_sources 0 6 1 222304514227755112 222304514227755112 222304514227755112 endpoint_8_73_p6 endpoint_8_73_w6
def endpoint_8_73 : CertifiedEndpoint :=
  ⟨⟨8, 73, 2757⟩, 222304514227755112, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_8_73_flag endpoint_8_73_sources 7 222304514227755112 222304514227755112 rfl endpoint_8_73_base endpoint_8_73_p7) (by decide)⟩
private def endpoint_8_74_flag : Flag := ⟨8, 74, 2690⟩
private def endpoint_8_74_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_8_74_base : receiptBase endpoint_8_74_flag endpoint_8_74_sources = some 219612008562216671 := by decide +kernel
private theorem endpoint_8_74_w0 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 2 219612008562216671 = some 219612008562216671 := by decide +kernel
private theorem endpoint_8_74_w2 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 2 2 219612008562216671 = some 219612008562216671 := by decide +kernel
private theorem endpoint_8_74_p4 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 4 219612008562216671 = some 219612008562216671 :=
  join_receipt_window endpoint_8_74_flag endpoint_8_74_sources 0 2 2 219612008562216671 219612008562216671 219612008562216671 endpoint_8_74_w0 endpoint_8_74_w2
private theorem endpoint_8_74_w4 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 4 2 219612008562216671 = some 219612008562216671 := by decide +kernel
private theorem endpoint_8_74_p6 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 6 219612008562216671 = some 219612008562216671 :=
  join_receipt_window endpoint_8_74_flag endpoint_8_74_sources 0 4 2 219612008562216671 219612008562216671 219612008562216671 endpoint_8_74_p4 endpoint_8_74_w4
private theorem endpoint_8_74_w6 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 6 1 219612008562216671 = some 219612008562216671 := by decide +kernel
private theorem endpoint_8_74_p7 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 7 219612008562216671 = some 219612008562216671 :=
  join_receipt_window endpoint_8_74_flag endpoint_8_74_sources 0 6 1 219612008562216671 219612008562216671 219612008562216671 endpoint_8_74_p6 endpoint_8_74_w6
def endpoint_8_74 : CertifiedEndpoint :=
  ⟨⟨8, 74, 2690⟩, 219612008562216671, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_8_74_flag endpoint_8_74_sources 7 219612008562216671 219612008562216671 rfl endpoint_8_74_base endpoint_8_74_p7) (by decide)⟩
private def endpoint_8_75_flag : Flag := ⟨8, 75, 2621⟩
private def endpoint_8_75_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_8_75_base : receiptBase endpoint_8_75_flag endpoint_8_75_sources = some 220816466870913568 := by decide +kernel
private theorem endpoint_8_75_w0 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 2 220816466870913568 = some 220816466870913568 := by decide +kernel
private theorem endpoint_8_75_w2 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 2 2 220816466870913568 = some 220816466870913568 := by decide +kernel
private theorem endpoint_8_75_p4 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 4 220816466870913568 = some 220816466870913568 :=
  join_receipt_window endpoint_8_75_flag endpoint_8_75_sources 0 2 2 220816466870913568 220816466870913568 220816466870913568 endpoint_8_75_w0 endpoint_8_75_w2
private theorem endpoint_8_75_w4 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 4 2 220816466870913568 = some 220816466870913568 := by decide +kernel
private theorem endpoint_8_75_p6 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 6 220816466870913568 = some 220816466870913568 :=
  join_receipt_window endpoint_8_75_flag endpoint_8_75_sources 0 4 2 220816466870913568 220816466870913568 220816466870913568 endpoint_8_75_p4 endpoint_8_75_w4
private theorem endpoint_8_75_w6 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 6 1 220816466870913568 = some 220816466870913568 := by decide +kernel
private theorem endpoint_8_75_p7 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 7 220816466870913568 = some 220816466870913568 :=
  join_receipt_window endpoint_8_75_flag endpoint_8_75_sources 0 6 1 220816466870913568 220816466870913568 220816466870913568 endpoint_8_75_p6 endpoint_8_75_w6
def endpoint_8_75 : CertifiedEndpoint :=
  ⟨⟨8, 75, 2621⟩, 220816466870913568, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_8_75_flag endpoint_8_75_sources 7 220816466870913568 220816466870913568 rfl endpoint_8_75_base endpoint_8_75_p7) (by decide)⟩
private def endpoint_8_76_flag : Flag := ⟨8, 76, 2549⟩
private def endpoint_8_76_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_8_76_base : receiptBase endpoint_8_76_flag endpoint_8_76_sources = some 217409603224168448 := by decide +kernel
private theorem endpoint_8_76_w0 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 2 217409603224168448 = some 217409603224168448 := by decide +kernel
private theorem endpoint_8_76_w2 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 2 2 217409603224168448 = some 217409603224168448 := by decide +kernel
private theorem endpoint_8_76_p4 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 4 217409603224168448 = some 217409603224168448 :=
  join_receipt_window endpoint_8_76_flag endpoint_8_76_sources 0 2 2 217409603224168448 217409603224168448 217409603224168448 endpoint_8_76_w0 endpoint_8_76_w2
private theorem endpoint_8_76_w4 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 4 2 217409603224168448 = some 217409603224168448 := by decide +kernel
private theorem endpoint_8_76_p6 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 6 217409603224168448 = some 217409603224168448 :=
  join_receipt_window endpoint_8_76_flag endpoint_8_76_sources 0 4 2 217409603224168448 217409603224168448 217409603224168448 endpoint_8_76_p4 endpoint_8_76_w4
private theorem endpoint_8_76_w6 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 6 1 217409603224168448 = some 217409603224168448 := by decide +kernel
private theorem endpoint_8_76_p7 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 7 217409603224168448 = some 217409603224168448 :=
  join_receipt_window endpoint_8_76_flag endpoint_8_76_sources 0 6 1 217409603224168448 217409603224168448 217409603224168448 endpoint_8_76_p6 endpoint_8_76_w6
def endpoint_8_76 : CertifiedEndpoint :=
  ⟨⟨8, 76, 2549⟩, 217409603224168448, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_8_76_flag endpoint_8_76_sources 7 217409603224168448 217409603224168448 rfl endpoint_8_76_base endpoint_8_76_p7) (by decide)⟩
private def endpoint_8_77_flag : Flag := ⟨8, 77, 2474⟩
private def endpoint_8_77_sources : Sources := ⟨contact11, contact11, contact13⟩
private theorem endpoint_8_77_base : receiptBase endpoint_8_77_flag endpoint_8_77_sources = some 213698583067945717 := by decide +kernel
private theorem endpoint_8_77_w0 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 2 213698583067945717 = some 213698583067945717 := by decide +kernel
private theorem endpoint_8_77_w2 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 2 2 213698583067945717 = some 213698583067945717 := by decide +kernel
private theorem endpoint_8_77_p4 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 4 213698583067945717 = some 213698583067945717 :=
  join_receipt_window endpoint_8_77_flag endpoint_8_77_sources 0 2 2 213698583067945717 213698583067945717 213698583067945717 endpoint_8_77_w0 endpoint_8_77_w2
private theorem endpoint_8_77_w4 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 4 2 213698583067945717 = some 213698583067945717 := by decide +kernel
private theorem endpoint_8_77_p6 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 6 213698583067945717 = some 213698583067945717 :=
  join_receipt_window endpoint_8_77_flag endpoint_8_77_sources 0 4 2 213698583067945717 213698583067945717 213698583067945717 endpoint_8_77_p4 endpoint_8_77_w4
private theorem endpoint_8_77_w6 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 6 1 213698583067945717 = some 213698583067945717 := by decide +kernel
private theorem endpoint_8_77_p7 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 7 213698583067945717 = some 213698583067945717 :=
  join_receipt_window endpoint_8_77_flag endpoint_8_77_sources 0 6 1 213698583067945717 213698583067945717 213698583067945717 endpoint_8_77_p6 endpoint_8_77_w6
def endpoint_8_77 : CertifiedEndpoint :=
  ⟨⟨8, 77, 2474⟩, 213698583067945717, .terminal ⟨contact11, contact11, contact13⟩ (finish_receipt_window endpoint_8_77_flag endpoint_8_77_sources 7 213698583067945717 213698583067945717 rfl endpoint_8_77_base endpoint_8_77_p7) (by decide)⟩
private def endpoint_8_78_flag : Flag := ⟨8, 78, 2397⟩
private def endpoint_8_78_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_8_78_base : receiptBase endpoint_8_78_flag endpoint_8_78_sources = some 211651904204272399 := by decide +kernel
private theorem endpoint_8_78_w0 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 2 211651904204272399 = some 211651904204272399 := by decide +kernel
private theorem endpoint_8_78_w2 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 2 2 211651904204272399 = some 211651904204272399 := by decide +kernel
private theorem endpoint_8_78_p4 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 4 211651904204272399 = some 211651904204272399 :=
  join_receipt_window endpoint_8_78_flag endpoint_8_78_sources 0 2 2 211651904204272399 211651904204272399 211651904204272399 endpoint_8_78_w0 endpoint_8_78_w2
private theorem endpoint_8_78_w4 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 4 2 211651904204272399 = some 211651904204272399 := by decide +kernel
private theorem endpoint_8_78_p6 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 6 211651904204272399 = some 211651904204272399 :=
  join_receipt_window endpoint_8_78_flag endpoint_8_78_sources 0 4 2 211651904204272399 211651904204272399 211651904204272399 endpoint_8_78_p4 endpoint_8_78_w4
private theorem endpoint_8_78_w6 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 6 1 211651904204272399 = some 211651904204272399 := by decide +kernel
private theorem endpoint_8_78_p7 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 7 211651904204272399 = some 211651904204272399 :=
  join_receipt_window endpoint_8_78_flag endpoint_8_78_sources 0 6 1 211651904204272399 211651904204272399 211651904204272399 endpoint_8_78_p6 endpoint_8_78_w6
def endpoint_8_78 : CertifiedEndpoint :=
  ⟨⟨8, 78, 2397⟩, 211651904204272399, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_8_78_flag endpoint_8_78_sources 7 211651904204272399 211651904204272399 rfl endpoint_8_78_base endpoint_8_78_p7) (by decide)⟩
private def endpoint_8_79_flag : Flag := ⟨8, 79, 2317⟩
private def endpoint_8_79_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_8_79_base : receiptBase endpoint_8_79_flag endpoint_8_79_sources = some 206997455894739668 := by decide +kernel
private theorem endpoint_8_79_w0 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 2 206997455894739668 = some 206997455894739668 := by decide +kernel
private theorem endpoint_8_79_w2 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 2 2 206997455894739668 = some 206997455894739668 := by decide +kernel
private theorem endpoint_8_79_p4 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 4 206997455894739668 = some 206997455894739668 :=
  join_receipt_window endpoint_8_79_flag endpoint_8_79_sources 0 2 2 206997455894739668 206997455894739668 206997455894739668 endpoint_8_79_w0 endpoint_8_79_w2
private theorem endpoint_8_79_w4 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 4 2 206997455894739668 = some 206997455894739668 := by decide +kernel
private theorem endpoint_8_79_p6 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 6 206997455894739668 = some 206997455894739668 :=
  join_receipt_window endpoint_8_79_flag endpoint_8_79_sources 0 4 2 206997455894739668 206997455894739668 206997455894739668 endpoint_8_79_p4 endpoint_8_79_w4
private theorem endpoint_8_79_w6 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 6 1 206997455894739668 = some 206997455894739668 := by decide +kernel
private theorem endpoint_8_79_p7 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 7 206997455894739668 = some 206997455894739668 :=
  join_receipt_window endpoint_8_79_flag endpoint_8_79_sources 0 6 1 206997455894739668 206997455894739668 206997455894739668 endpoint_8_79_p6 endpoint_8_79_w6
def endpoint_8_79 : CertifiedEndpoint :=
  ⟨⟨8, 79, 2317⟩, 206997455894739668, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_8_79_flag endpoint_8_79_sources 7 206997455894739668 206997455894739668 rfl endpoint_8_79_base endpoint_8_79_p7) (by decide)⟩
private def endpoint_8_80_flag : Flag := ⟨8, 80, 2234⟩
private def endpoint_8_80_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_8_80_base : receiptBase endpoint_8_80_flag endpoint_8_80_sources = some 201911379964014819 := by decide +kernel
private theorem endpoint_8_80_w0 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 2 201911379964014819 = some 201911379964014819 := by decide +kernel
private theorem endpoint_8_80_w2 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 2 2 201911379964014819 = some 201911379964014819 := by decide +kernel
private theorem endpoint_8_80_p4 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 4 201911379964014819 = some 201911379964014819 :=
  join_receipt_window endpoint_8_80_flag endpoint_8_80_sources 0 2 2 201911379964014819 201911379964014819 201911379964014819 endpoint_8_80_w0 endpoint_8_80_w2
private theorem endpoint_8_80_w4 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 4 2 201911379964014819 = some 201911379964014819 := by decide +kernel
private theorem endpoint_8_80_p6 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 6 201911379964014819 = some 201911379964014819 :=
  join_receipt_window endpoint_8_80_flag endpoint_8_80_sources 0 4 2 201911379964014819 201911379964014819 201911379964014819 endpoint_8_80_p4 endpoint_8_80_w4
private theorem endpoint_8_80_w6 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 6 1 201911379964014819 = some 201911379964014819 := by decide +kernel
private theorem endpoint_8_80_p7 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 7 201911379964014819 = some 201911379964014819 :=
  join_receipt_window endpoint_8_80_flag endpoint_8_80_sources 0 6 1 201911379964014819 201911379964014819 201911379964014819 endpoint_8_80_p6 endpoint_8_80_w6
def endpoint_8_80 : CertifiedEndpoint :=
  ⟨⟨8, 80, 2234⟩, 201911379964014819, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_8_80_flag endpoint_8_80_sources 7 201911379964014819 201911379964014819 rfl endpoint_8_80_base endpoint_8_80_p7) (by decide)⟩
private def endpoint_8_81_flag : Flag := ⟨8, 81, 2149⟩
private def endpoint_8_81_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_8_81_base : receiptBase endpoint_8_81_flag endpoint_8_81_sources = some 198650211638697426 := by decide +kernel
private theorem endpoint_8_81_w0 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 2 198650211638697426 = some 198650211638697426 := by decide +kernel
private theorem endpoint_8_81_w2 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 2 2 198650211638697426 = some 198650211638697426 := by decide +kernel
private theorem endpoint_8_81_p4 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 4 198650211638697426 = some 198650211638697426 :=
  join_receipt_window endpoint_8_81_flag endpoint_8_81_sources 0 2 2 198650211638697426 198650211638697426 198650211638697426 endpoint_8_81_w0 endpoint_8_81_w2
private theorem endpoint_8_81_w4 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 4 2 198650211638697426 = some 198650211638697426 := by decide +kernel
private theorem endpoint_8_81_p6 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 6 198650211638697426 = some 198650211638697426 :=
  join_receipt_window endpoint_8_81_flag endpoint_8_81_sources 0 4 2 198650211638697426 198650211638697426 198650211638697426 endpoint_8_81_p4 endpoint_8_81_w4
private theorem endpoint_8_81_w6 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 6 1 198650211638697426 = some 198650211638697426 := by decide +kernel
private theorem endpoint_8_81_p7 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 7 198650211638697426 = some 198650211638697426 :=
  join_receipt_window endpoint_8_81_flag endpoint_8_81_sources 0 6 1 198650211638697426 198650211638697426 198650211638697426 endpoint_8_81_p6 endpoint_8_81_w6
def endpoint_8_81 : CertifiedEndpoint :=
  ⟨⟨8, 81, 2149⟩, 198650211638697426, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_8_81_flag endpoint_8_81_sources 7 198650211638697426 198650211638697426 rfl endpoint_8_81_base endpoint_8_81_p7) (by decide)⟩
private def endpoint_8_82_flag : Flag := ⟨8, 82, 2061⟩
private def endpoint_8_82_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_8_82_base : receiptBase endpoint_8_82_flag endpoint_8_82_sources = some 194874373708775441 := by decide +kernel
private theorem endpoint_8_82_w0 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 2 194874373708775441 = some 194874373708775441 := by decide +kernel
private theorem endpoint_8_82_w2 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 2 2 194874373708775441 = some 194874373708775441 := by decide +kernel
private theorem endpoint_8_82_p4 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 4 194874373708775441 = some 194874373708775441 :=
  join_receipt_window endpoint_8_82_flag endpoint_8_82_sources 0 2 2 194874373708775441 194874373708775441 194874373708775441 endpoint_8_82_w0 endpoint_8_82_w2
private theorem endpoint_8_82_w4 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 4 2 194874373708775441 = some 194874373708775441 := by decide +kernel
private theorem endpoint_8_82_p6 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 6 194874373708775441 = some 194874373708775441 :=
  join_receipt_window endpoint_8_82_flag endpoint_8_82_sources 0 4 2 194874373708775441 194874373708775441 194874373708775441 endpoint_8_82_p4 endpoint_8_82_w4
private theorem endpoint_8_82_w6 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 6 1 194874373708775441 = some 194874373708775441 := by decide +kernel
private theorem endpoint_8_82_p7 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 7 194874373708775441 = some 194874373708775441 :=
  join_receipt_window endpoint_8_82_flag endpoint_8_82_sources 0 6 1 194874373708775441 194874373708775441 194874373708775441 endpoint_8_82_p6 endpoint_8_82_w6
def endpoint_8_82 : CertifiedEndpoint :=
  ⟨⟨8, 82, 2061⟩, 194874373708775441, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_8_82_flag endpoint_8_82_sources 7 194874373708775441 194874373708775441 rfl endpoint_8_82_base endpoint_8_82_p7) (by decide)⟩
private def endpoint_8_83_flag : Flag := ⟨8, 83, 1971⟩
private def endpoint_8_83_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_8_83_base : receiptBase endpoint_8_83_flag endpoint_8_83_sources = some 188448795904503204 := by decide +kernel
private theorem endpoint_8_83_w0 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 0 2 188448795904503204 = some 188448795904503204 := by decide +kernel
private theorem endpoint_8_83_w2 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 2 2 188448795904503204 = some 188448795904503204 := by decide +kernel
private theorem endpoint_8_83_p4 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 0 4 188448795904503204 = some 188448795904503204 :=
  join_receipt_window endpoint_8_83_flag endpoint_8_83_sources 0 2 2 188448795904503204 188448795904503204 188448795904503204 endpoint_8_83_w0 endpoint_8_83_w2
private theorem endpoint_8_83_w4 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 4 2 188448795904503204 = some 188448795904503204 := by decide +kernel
private theorem endpoint_8_83_p6 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 0 6 188448795904503204 = some 188448795904503204 :=
  join_receipt_window endpoint_8_83_flag endpoint_8_83_sources 0 4 2 188448795904503204 188448795904503204 188448795904503204 endpoint_8_83_p4 endpoint_8_83_w4
private theorem endpoint_8_83_w6 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 6 1 188448795904503204 = some 188448795904503204 := by decide +kernel
private theorem endpoint_8_83_p7 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 0 7 188448795904503204 = some 188448795904503204 :=
  join_receipt_window endpoint_8_83_flag endpoint_8_83_sources 0 6 1 188448795904503204 188448795904503204 188448795904503204 endpoint_8_83_p6 endpoint_8_83_w6
def endpoint_8_83 : CertifiedEndpoint :=
  ⟨⟨8, 83, 1971⟩, 188448795904503204, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_8_83_flag endpoint_8_83_sources 7 188448795904503204 188448795904503204 rfl endpoint_8_83_base endpoint_8_83_p7) (by decide)⟩
private def endpoint_8_84_flag : Flag := ⟨8, 84, 1878⟩
private def endpoint_8_84_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_8_84_base : receiptBase endpoint_8_84_flag endpoint_8_84_sources = some 181545734851240562 := by decide +kernel
private theorem endpoint_8_84_w0 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 0 2 181545734851240562 = some 181545734851240562 := by decide +kernel
private theorem endpoint_8_84_w2 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 2 2 181545734851240562 = some 181545734851240562 := by decide +kernel
private theorem endpoint_8_84_p4 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 0 4 181545734851240562 = some 181545734851240562 :=
  join_receipt_window endpoint_8_84_flag endpoint_8_84_sources 0 2 2 181545734851240562 181545734851240562 181545734851240562 endpoint_8_84_w0 endpoint_8_84_w2
private theorem endpoint_8_84_w4 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 4 2 181545734851240562 = some 181545734851240562 := by decide +kernel
private theorem endpoint_8_84_p6 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 0 6 181545734851240562 = some 181545734851240562 :=
  join_receipt_window endpoint_8_84_flag endpoint_8_84_sources 0 4 2 181545734851240562 181545734851240562 181545734851240562 endpoint_8_84_p4 endpoint_8_84_w4
private theorem endpoint_8_84_w6 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 6 1 181545734851240562 = some 181545734851240562 := by decide +kernel
private theorem endpoint_8_84_p7 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 0 7 181545734851240562 = some 181545734851240562 :=
  join_receipt_window endpoint_8_84_flag endpoint_8_84_sources 0 6 1 181545734851240562 181545734851240562 181545734851240562 endpoint_8_84_p6 endpoint_8_84_w6
def endpoint_8_84 : CertifiedEndpoint :=
  ⟨⟨8, 84, 1878⟩, 181545734851240562, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_8_84_flag endpoint_8_84_sources 7 181545734851240562 181545734851240562 rfl endpoint_8_84_base endpoint_8_84_p7) (by decide)⟩
private def endpoint_8_85_flag : Flag := ⟨8, 85, 1782⟩
private def endpoint_8_85_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_8_85_base : receiptBase endpoint_8_85_flag endpoint_8_85_sources = some 174155783486915735 := by decide +kernel
private theorem endpoint_8_85_w0 : receiptWindow endpoint_8_85_flag endpoint_8_85_sources 0 2 174155783486915735 = some 174155783486915735 := by decide +kernel
private theorem endpoint_8_85_w2 : receiptWindow endpoint_8_85_flag endpoint_8_85_sources 2 2 174155783486915735 = some 174155783486915735 := by decide +kernel
private theorem endpoint_8_85_p4 : receiptWindow endpoint_8_85_flag endpoint_8_85_sources 0 4 174155783486915735 = some 174155783486915735 :=
  join_receipt_window endpoint_8_85_flag endpoint_8_85_sources 0 2 2 174155783486915735 174155783486915735 174155783486915735 endpoint_8_85_w0 endpoint_8_85_w2
private theorem endpoint_8_85_w4 : receiptWindow endpoint_8_85_flag endpoint_8_85_sources 4 2 174155783486915735 = some 174155783486915735 := by decide +kernel
private theorem endpoint_8_85_p6 : receiptWindow endpoint_8_85_flag endpoint_8_85_sources 0 6 174155783486915735 = some 174155783486915735 :=
  join_receipt_window endpoint_8_85_flag endpoint_8_85_sources 0 4 2 174155783486915735 174155783486915735 174155783486915735 endpoint_8_85_p4 endpoint_8_85_w4
private theorem endpoint_8_85_w6 : receiptWindow endpoint_8_85_flag endpoint_8_85_sources 6 1 174155783486915735 = some 174155783486915735 := by decide +kernel
private theorem endpoint_8_85_p7 : receiptWindow endpoint_8_85_flag endpoint_8_85_sources 0 7 174155783486915735 = some 174155783486915735 :=
  join_receipt_window endpoint_8_85_flag endpoint_8_85_sources 0 6 1 174155783486915735 174155783486915735 174155783486915735 endpoint_8_85_p6 endpoint_8_85_w6
def endpoint_8_85 : CertifiedEndpoint :=
  ⟨⟨8, 85, 1782⟩, 174155783486915735, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_8_85_flag endpoint_8_85_sources 7 174155783486915735 174155783486915735 rfl endpoint_8_85_base endpoint_8_85_p7) (by decide)⟩
def endpoint_8_86 : CertifiedEndpoint :=
  ⟨⟨8, 86, 1683⟩, 259147126509592353, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_87 : CertifiedEndpoint :=
  ⟨⟨8, 87, 1582⟩, 246069158918773027, .intrinsic (by decide +kernel) (by decide)⟩

def endpointBlock05 : List CertifiedEndpoint := [
  endpoint_7_51, endpoint_7_52, endpoint_7_53, endpoint_7_54, endpoint_7_55, endpoint_7_56, endpoint_7_57,
  endpoint_7_58, endpoint_7_59, endpoint_7_60, endpoint_7_61, endpoint_7_62, endpoint_7_63, endpoint_7_64,
  endpoint_7_65, endpoint_7_66, endpoint_7_67, endpoint_7_68, endpoint_7_69, endpoint_7_70, endpoint_7_71,
  endpoint_7_72, endpoint_7_73, endpoint_7_74, endpoint_7_75, endpoint_7_76, endpoint_7_77, endpoint_7_78,
  endpoint_7_79, endpoint_7_80, endpoint_7_81, endpoint_7_82, endpoint_7_83, endpoint_7_84, endpoint_7_85,
  endpoint_7_86, endpoint_7_87, endpoint_7_88, endpoint_7_89, endpoint_7_90, endpoint_7_91, endpoint_7_92,
  endpoint_7_93, endpoint_7_94, endpoint_7_95, endpoint_7_96, endpoint_7_97, endpoint_7_98, endpoint_7_99,
  endpoint_7_100, endpoint_8_8, endpoint_8_9, endpoint_8_10, endpoint_8_11, endpoint_8_12, endpoint_8_13,
  endpoint_8_14, endpoint_8_15, endpoint_8_16, endpoint_8_17, endpoint_8_18, endpoint_8_19, endpoint_8_20,
  endpoint_8_21, endpoint_8_22, endpoint_8_23, endpoint_8_24, endpoint_8_25, endpoint_8_26, endpoint_8_27,
  endpoint_8_28, endpoint_8_29, endpoint_8_30, endpoint_8_31, endpoint_8_32, endpoint_8_33, endpoint_8_34,
  endpoint_8_35, endpoint_8_36, endpoint_8_37, endpoint_8_38, endpoint_8_39, endpoint_8_40, endpoint_8_41,
  endpoint_8_42, endpoint_8_43, endpoint_8_44, endpoint_8_45, endpoint_8_46, endpoint_8_47, endpoint_8_48,
  endpoint_8_49, endpoint_8_50, endpoint_8_51, endpoint_8_52, endpoint_8_53, endpoint_8_54, endpoint_8_55,
  endpoint_8_56, endpoint_8_57, endpoint_8_58, endpoint_8_59, endpoint_8_60, endpoint_8_61, endpoint_8_62,
  endpoint_8_63, endpoint_8_64, endpoint_8_65, endpoint_8_66, endpoint_8_67, endpoint_8_68, endpoint_8_69,
  endpoint_8_70, endpoint_8_71, endpoint_8_72, endpoint_8_73, endpoint_8_74, endpoint_8_75, endpoint_8_76,
  endpoint_8_77, endpoint_8_78, endpoint_8_79, endpoint_8_80, endpoint_8_81, endpoint_8_82, endpoint_8_83,
  endpoint_8_84, endpoint_8_85, endpoint_8_86, endpoint_8_87
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
