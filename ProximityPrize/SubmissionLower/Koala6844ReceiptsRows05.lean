import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def endpoint_7_40 : CertifiedEndpoint :=
  ⟨⟨7, 40, 4004⟩, 241394886084061532, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_41 : CertifiedEndpoint :=
  ⟨⟨7, 41, 3979⟩, 246510502268161716, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_42 : CertifiedEndpoint :=
  ⟨⟨7, 42, 3954⟩, 251540251280179366, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_43 : CertifiedEndpoint :=
  ⟨⟨7, 43, 3929⟩, 256484133120114482, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_7_44_flag : Flag := ⟨7, 44, 3903⟩
private def endpoint_7_44_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_44_base : receiptBase endpoint_7_44_flag endpoint_7_44_sources = some 175972404801563592 := by decide +kernel
private theorem endpoint_7_44_w0 : receiptWindow endpoint_7_44_flag endpoint_7_44_sources 0 2 175972404801563592 = some 175972404801563592 := by decide +kernel
private theorem endpoint_7_44_w2 : receiptWindow endpoint_7_44_flag endpoint_7_44_sources 2 2 175972404801563592 = some 175972404801563592 := by decide +kernel
private theorem endpoint_7_44_p4 : receiptWindow endpoint_7_44_flag endpoint_7_44_sources 0 4 175972404801563592 = some 175972404801563592 :=
  join_receipt_window endpoint_7_44_flag endpoint_7_44_sources 0 2 2 175972404801563592 175972404801563592 175972404801563592 endpoint_7_44_w0 endpoint_7_44_w2
private theorem endpoint_7_44_w4 : receiptWindow endpoint_7_44_flag endpoint_7_44_sources 4 2 175972404801563592 = some 175972404801563592 := by decide +kernel
private theorem endpoint_7_44_p6 : receiptWindow endpoint_7_44_flag endpoint_7_44_sources 0 6 175972404801563592 = some 175972404801563592 :=
  join_receipt_window endpoint_7_44_flag endpoint_7_44_sources 0 4 2 175972404801563592 175972404801563592 175972404801563592 endpoint_7_44_p4 endpoint_7_44_w4
def endpoint_7_44 : CertifiedEndpoint :=
  ⟨⟨7, 44, 3903⟩, 175972404801563592, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_44_flag endpoint_7_44_sources 6 175972404801563592 175972404801563592 rfl endpoint_7_44_base endpoint_7_44_p6) (by decide)⟩
private def endpoint_7_45_flag : Flag := ⟨7, 45, 3877⟩
private def endpoint_7_45_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_45_base : receiptBase endpoint_7_45_flag endpoint_7_45_sources = some 178214954906923243 := by decide +kernel
private theorem endpoint_7_45_w0 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 0 2 178214954906923243 = some 178214954906923243 := by decide +kernel
private theorem endpoint_7_45_w2 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 2 2 178214954906923243 = some 178214954906923243 := by decide +kernel
private theorem endpoint_7_45_p4 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 0 4 178214954906923243 = some 178214954906923243 :=
  join_receipt_window endpoint_7_45_flag endpoint_7_45_sources 0 2 2 178214954906923243 178214954906923243 178214954906923243 endpoint_7_45_w0 endpoint_7_45_w2
private theorem endpoint_7_45_w4 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 4 2 178214954906923243 = some 178214954906923243 := by decide +kernel
private theorem endpoint_7_45_p6 : receiptWindow endpoint_7_45_flag endpoint_7_45_sources 0 6 178214954906923243 = some 178214954906923243 :=
  join_receipt_window endpoint_7_45_flag endpoint_7_45_sources 0 4 2 178214954906923243 178214954906923243 178214954906923243 endpoint_7_45_p4 endpoint_7_45_w4
def endpoint_7_45 : CertifiedEndpoint :=
  ⟨⟨7, 45, 3877⟩, 178214954906923243, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_45_flag endpoint_7_45_sources 6 178214954906923243 178214954906923243 rfl endpoint_7_45_base endpoint_7_45_p6) (by decide)⟩
private def endpoint_7_46_flag : Flag := ⟨7, 46, 3850⟩
private def endpoint_7_46_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_46_base : receiptBase endpoint_7_46_flag endpoint_7_46_sources = some 180365546900173165 := by decide +kernel
private theorem endpoint_7_46_w0 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 0 2 180365546900173165 = some 180365546900173165 := by decide +kernel
private theorem endpoint_7_46_w2 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 2 2 180365546900173165 = some 180365546900173165 := by decide +kernel
private theorem endpoint_7_46_p4 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 0 4 180365546900173165 = some 180365546900173165 :=
  join_receipt_window endpoint_7_46_flag endpoint_7_46_sources 0 2 2 180365546900173165 180365546900173165 180365546900173165 endpoint_7_46_w0 endpoint_7_46_w2
private theorem endpoint_7_46_w4 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 4 2 180365546900173165 = some 180365546900173165 := by decide +kernel
private theorem endpoint_7_46_p6 : receiptWindow endpoint_7_46_flag endpoint_7_46_sources 0 6 180365546900173165 = some 180365546900173165 :=
  join_receipt_window endpoint_7_46_flag endpoint_7_46_sources 0 4 2 180365546900173165 180365546900173165 180365546900173165 endpoint_7_46_p4 endpoint_7_46_w4
def endpoint_7_46 : CertifiedEndpoint :=
  ⟨⟨7, 46, 3850⟩, 180365546900173165, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_46_flag endpoint_7_46_sources 6 180365546900173165 180365546900173165 rfl endpoint_7_46_base endpoint_7_46_p6) (by decide)⟩
private def endpoint_7_47_flag : Flag := ⟨7, 47, 3823⟩
private def endpoint_7_47_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_47_base : receiptBase endpoint_7_47_flag endpoint_7_47_sources = some 182468615580226171 := by decide +kernel
private theorem endpoint_7_47_w0 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 0 2 182468615580226171 = some 182468615580226171 := by decide +kernel
private theorem endpoint_7_47_w2 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 2 2 182468615580226171 = some 182468615580226171 := by decide +kernel
private theorem endpoint_7_47_p4 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 0 4 182468615580226171 = some 182468615580226171 :=
  join_receipt_window endpoint_7_47_flag endpoint_7_47_sources 0 2 2 182468615580226171 182468615580226171 182468615580226171 endpoint_7_47_w0 endpoint_7_47_w2
private theorem endpoint_7_47_w4 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 4 2 182468615580226171 = some 182468615580226171 := by decide +kernel
private theorem endpoint_7_47_p6 : receiptWindow endpoint_7_47_flag endpoint_7_47_sources 0 6 182468615580226171 = some 182468615580226171 :=
  join_receipt_window endpoint_7_47_flag endpoint_7_47_sources 0 4 2 182468615580226171 182468615580226171 182468615580226171 endpoint_7_47_p4 endpoint_7_47_w4
def endpoint_7_47 : CertifiedEndpoint :=
  ⟨⟨7, 47, 3823⟩, 182468615580226171, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_47_flag endpoint_7_47_sources 6 182468615580226171 182468615580226171 rfl endpoint_7_47_base endpoint_7_47_p6) (by decide)⟩
private def endpoint_7_48_flag : Flag := ⟨7, 48, 3795⟩
private def endpoint_7_48_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_48_base : receiptBase endpoint_7_48_flag endpoint_7_48_sources = some 184476269907209673 := by decide +kernel
private theorem endpoint_7_48_w0 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 0 2 184476269907209673 = some 184476269907209673 := by decide +kernel
private theorem endpoint_7_48_w2 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 2 2 184476269907209673 = some 184476269907209673 := by decide +kernel
private theorem endpoint_7_48_p4 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 0 4 184476269907209673 = some 184476269907209673 :=
  join_receipt_window endpoint_7_48_flag endpoint_7_48_sources 0 2 2 184476269907209673 184476269907209673 184476269907209673 endpoint_7_48_w0 endpoint_7_48_w2
private theorem endpoint_7_48_w4 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 4 2 184476269907209673 = some 184476269907209673 := by decide +kernel
private theorem endpoint_7_48_p6 : receiptWindow endpoint_7_48_flag endpoint_7_48_sources 0 6 184476269907209673 = some 184476269907209673 :=
  join_receipt_window endpoint_7_48_flag endpoint_7_48_sources 0 4 2 184476269907209673 184476269907209673 184476269907209673 endpoint_7_48_p4 endpoint_7_48_w4
def endpoint_7_48 : CertifiedEndpoint :=
  ⟨⟨7, 48, 3795⟩, 184476269907209673, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_48_flag endpoint_7_48_sources 6 184476269907209673 184476269907209673 rfl endpoint_7_48_base endpoint_7_48_p6) (by decide)⟩
private def endpoint_7_49_flag : Flag := ⟨7, 49, 3767⟩
private def endpoint_7_49_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_49_base : receiptBase endpoint_7_49_flag endpoint_7_49_sources = some 186434672800516372 := by decide +kernel
private theorem endpoint_7_49_w0 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 0 2 186434672800516372 = some 186434672800516372 := by decide +kernel
private theorem endpoint_7_49_w2 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 2 2 186434672800516372 = some 186434672800516372 := by decide +kernel
private theorem endpoint_7_49_p4 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 0 4 186434672800516372 = some 186434672800516372 :=
  join_receipt_window endpoint_7_49_flag endpoint_7_49_sources 0 2 2 186434672800516372 186434672800516372 186434672800516372 endpoint_7_49_w0 endpoint_7_49_w2
private theorem endpoint_7_49_w4 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 4 2 186434672800516372 = some 186434672800516372 := by decide +kernel
private theorem endpoint_7_49_p6 : receiptWindow endpoint_7_49_flag endpoint_7_49_sources 0 6 186434672800516372 = some 186434672800516372 :=
  join_receipt_window endpoint_7_49_flag endpoint_7_49_sources 0 4 2 186434672800516372 186434672800516372 186434672800516372 endpoint_7_49_p4 endpoint_7_49_w4
def endpoint_7_49 : CertifiedEndpoint :=
  ⟨⟨7, 49, 3767⟩, 186434672800516372, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_49_flag endpoint_7_49_sources 6 186434672800516372 186434672800516372 rfl endpoint_7_49_base endpoint_7_49_p6) (by decide)⟩
private def endpoint_7_50_flag : Flag := ⟨7, 50, 3739⟩
private def endpoint_7_50_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_50_base : receiptBase endpoint_7_50_flag endpoint_7_50_sources = some 188343824260146268 := by decide +kernel
private theorem endpoint_7_50_w0 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 0 2 188343824260146268 = some 188343824260146268 := by decide +kernel
private theorem endpoint_7_50_w2 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 2 2 188343824260146268 = some 188343824260146268 := by decide +kernel
private theorem endpoint_7_50_p4 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 0 4 188343824260146268 = some 188343824260146268 :=
  join_receipt_window endpoint_7_50_flag endpoint_7_50_sources 0 2 2 188343824260146268 188343824260146268 188343824260146268 endpoint_7_50_w0 endpoint_7_50_w2
private theorem endpoint_7_50_w4 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 4 2 188343824260146268 = some 188343824260146268 := by decide +kernel
private theorem endpoint_7_50_p6 : receiptWindow endpoint_7_50_flag endpoint_7_50_sources 0 6 188343824260146268 = some 188343824260146268 :=
  join_receipt_window endpoint_7_50_flag endpoint_7_50_sources 0 4 2 188343824260146268 188343824260146268 188343824260146268 endpoint_7_50_p4 endpoint_7_50_w4
def endpoint_7_50 : CertifiedEndpoint :=
  ⟨⟨7, 50, 3739⟩, 188343824260146268, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_50_flag endpoint_7_50_sources 6 188343824260146268 188343824260146268 rfl endpoint_7_50_base endpoint_7_50_p6) (by decide)⟩
private def endpoint_7_51_flag : Flag := ⟨7, 51, 3709⟩
private def endpoint_7_51_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_7_51_base : receiptBase endpoint_7_51_flag endpoint_7_51_sources = some 190102757844914518 := by decide +kernel
private theorem endpoint_7_51_w0 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 0 2 190102757844914518 = some 190102757844914518 := by decide +kernel
private theorem endpoint_7_51_w2 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 2 2 190102757844914518 = some 190102757844914518 := by decide +kernel
private theorem endpoint_7_51_p4 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 0 4 190102757844914518 = some 190102757844914518 :=
  join_receipt_window endpoint_7_51_flag endpoint_7_51_sources 0 2 2 190102757844914518 190102757844914518 190102757844914518 endpoint_7_51_w0 endpoint_7_51_w2
private theorem endpoint_7_51_w4 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 4 2 190102757844914518 = some 190102757844914518 := by decide +kernel
private theorem endpoint_7_51_p6 : receiptWindow endpoint_7_51_flag endpoint_7_51_sources 0 6 190102757844914518 = some 190102757844914518 :=
  join_receipt_window endpoint_7_51_flag endpoint_7_51_sources 0 4 2 190102757844914518 190102757844914518 190102757844914518 endpoint_7_51_p4 endpoint_7_51_w4
def endpoint_7_51 : CertifiedEndpoint :=
  ⟨⟨7, 51, 3709⟩, 190102757844914518, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_7_51_flag endpoint_7_51_sources 6 190102757844914518 190102757844914518 rfl endpoint_7_51_base endpoint_7_51_p6) (by decide)⟩
private def endpoint_7_52_flag : Flag := ⟨7, 52, 3680⟩
private def endpoint_7_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_52_base : receiptBase endpoint_7_52_flag endpoint_7_52_sources = some 193056907165045741 := by decide +kernel
private theorem endpoint_7_52_w0 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 0 2 193056907165045741 = some 193056907165045741 := by decide +kernel
private theorem endpoint_7_52_w2 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 2 2 193056907165045741 = some 193056907165045741 := by decide +kernel
private theorem endpoint_7_52_p4 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 0 4 193056907165045741 = some 193056907165045741 :=
  join_receipt_window endpoint_7_52_flag endpoint_7_52_sources 0 2 2 193056907165045741 193056907165045741 193056907165045741 endpoint_7_52_w0 endpoint_7_52_w2
private theorem endpoint_7_52_w4 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 4 2 193056907165045741 = some 193056907165045741 := by decide +kernel
private theorem endpoint_7_52_p6 : receiptWindow endpoint_7_52_flag endpoint_7_52_sources 0 6 193056907165045741 = some 193056907165045741 :=
  join_receipt_window endpoint_7_52_flag endpoint_7_52_sources 0 4 2 193056907165045741 193056907165045741 193056907165045741 endpoint_7_52_p4 endpoint_7_52_w4
def endpoint_7_52 : CertifiedEndpoint :=
  ⟨⟨7, 52, 3680⟩, 193056907165045741, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_52_flag endpoint_7_52_sources 6 193056907165045741 193056907165045741 rfl endpoint_7_52_base endpoint_7_52_p6) (by decide)⟩
private def endpoint_7_53_flag : Flag := ⟨7, 53, 3649⟩
private def endpoint_7_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_53_base : receiptBase endpoint_7_53_flag endpoint_7_53_sources = some 194662460179590078 := by decide +kernel
private theorem endpoint_7_53_w0 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 0 2 194662460179590078 = some 194662460179590078 := by decide +kernel
private theorem endpoint_7_53_w2 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 2 2 194662460179590078 = some 194662460179590078 := by decide +kernel
private theorem endpoint_7_53_p4 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 0 4 194662460179590078 = some 194662460179590078 :=
  join_receipt_window endpoint_7_53_flag endpoint_7_53_sources 0 2 2 194662460179590078 194662460179590078 194662460179590078 endpoint_7_53_w0 endpoint_7_53_w2
private theorem endpoint_7_53_w4 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 4 2 194662460179590078 = some 194662460179590078 := by decide +kernel
private theorem endpoint_7_53_p6 : receiptWindow endpoint_7_53_flag endpoint_7_53_sources 0 6 194662460179590078 = some 194662460179590078 :=
  join_receipt_window endpoint_7_53_flag endpoint_7_53_sources 0 4 2 194662460179590078 194662460179590078 194662460179590078 endpoint_7_53_p4 endpoint_7_53_w4
def endpoint_7_53 : CertifiedEndpoint :=
  ⟨⟨7, 53, 3649⟩, 194662460179590078, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_53_flag endpoint_7_53_sources 6 194662460179590078 194662460179590078 rfl endpoint_7_53_base endpoint_7_53_p6) (by decide)⟩
private def endpoint_7_54_flag : Flag := ⟨7, 54, 3618⟩
private def endpoint_7_54_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_54_base : receiptBase endpoint_7_54_flag endpoint_7_54_sources = some 196213010257393522 := by decide +kernel
private theorem endpoint_7_54_w0 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 0 2 196213010257393522 = some 196213010257393522 := by decide +kernel
private theorem endpoint_7_54_w2 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 2 2 196213010257393522 = some 196213010257393522 := by decide +kernel
private theorem endpoint_7_54_p4 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 0 4 196213010257393522 = some 196213010257393522 :=
  join_receipt_window endpoint_7_54_flag endpoint_7_54_sources 0 2 2 196213010257393522 196213010257393522 196213010257393522 endpoint_7_54_w0 endpoint_7_54_w2
private theorem endpoint_7_54_w4 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 4 2 196213010257393522 = some 196213010257393522 := by decide +kernel
private theorem endpoint_7_54_p6 : receiptWindow endpoint_7_54_flag endpoint_7_54_sources 0 6 196213010257393522 = some 196213010257393522 :=
  join_receipt_window endpoint_7_54_flag endpoint_7_54_sources 0 4 2 196213010257393522 196213010257393522 196213010257393522 endpoint_7_54_p4 endpoint_7_54_w4
def endpoint_7_54 : CertifiedEndpoint :=
  ⟨⟨7, 54, 3618⟩, 196213010257393522, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_54_flag endpoint_7_54_sources 6 196213010257393522 196213010257393522 rfl endpoint_7_54_base endpoint_7_54_p6) (by decide)⟩
private def endpoint_7_55_flag : Flag := ⟨7, 55, 3586⟩
private def endpoint_7_55_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_55_base : receiptBase endpoint_7_55_flag endpoint_7_55_sources = some 197654090265119257 := by decide +kernel
private theorem endpoint_7_55_w0 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 0 2 197654090265119257 = some 197654090265119257 := by decide +kernel
private theorem endpoint_7_55_w2 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 2 2 197654090265119257 = some 197654090265119257 := by decide +kernel
private theorem endpoint_7_55_p4 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 0 4 197654090265119257 = some 197654090265119257 :=
  join_receipt_window endpoint_7_55_flag endpoint_7_55_sources 0 2 2 197654090265119257 197654090265119257 197654090265119257 endpoint_7_55_w0 endpoint_7_55_w2
private theorem endpoint_7_55_w4 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 4 2 197654090265119257 = some 197654090265119257 := by decide +kernel
private theorem endpoint_7_55_p6 : receiptWindow endpoint_7_55_flag endpoint_7_55_sources 0 6 197654090265119257 = some 197654090265119257 :=
  join_receipt_window endpoint_7_55_flag endpoint_7_55_sources 0 4 2 197654090265119257 197654090265119257 197654090265119257 endpoint_7_55_p4 endpoint_7_55_w4
def endpoint_7_55 : CertifiedEndpoint :=
  ⟨⟨7, 55, 3586⟩, 197654090265119257, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_55_flag endpoint_7_55_sources 6 197654090265119257 197654090265119257 rfl endpoint_7_55_base endpoint_7_55_p6) (by decide)⟩
private def endpoint_7_56_flag : Flag := ⟨7, 56, 3553⟩
private def endpoint_7_56_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_56_base : receiptBase endpoint_7_56_flag endpoint_7_56_sources = some 198983081015303430 := by decide +kernel
private theorem endpoint_7_56_w0 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 0 2 198983081015303430 = some 198983081015303430 := by decide +kernel
private theorem endpoint_7_56_w2 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 2 2 198983081015303430 = some 198983081015303430 := by decide +kernel
private theorem endpoint_7_56_p4 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 0 4 198983081015303430 = some 198983081015303430 :=
  join_receipt_window endpoint_7_56_flag endpoint_7_56_sources 0 2 2 198983081015303430 198983081015303430 198983081015303430 endpoint_7_56_w0 endpoint_7_56_w2
private theorem endpoint_7_56_w4 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 4 2 198983081015303430 = some 198983081015303430 := by decide +kernel
private theorem endpoint_7_56_p6 : receiptWindow endpoint_7_56_flag endpoint_7_56_sources 0 6 198983081015303430 = some 198983081015303430 :=
  join_receipt_window endpoint_7_56_flag endpoint_7_56_sources 0 4 2 198983081015303430 198983081015303430 198983081015303430 endpoint_7_56_p4 endpoint_7_56_w4
def endpoint_7_56 : CertifiedEndpoint :=
  ⟨⟨7, 56, 3553⟩, 198983081015303430, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_56_flag endpoint_7_56_sources 6 198983081015303430 198983081015303430 rfl endpoint_7_56_base endpoint_7_56_p6) (by decide)⟩
private def endpoint_7_57_flag : Flag := ⟨7, 57, 3520⟩
private def endpoint_7_57_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_7_57_base : receiptBase endpoint_7_57_flag endpoint_7_57_sources = some 200253576578794908 := by decide +kernel
private theorem endpoint_7_57_w0 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 0 2 200253576578794908 = some 200253576578794908 := by decide +kernel
private theorem endpoint_7_57_w2 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 2 2 200253576578794908 = some 200253576578794908 := by decide +kernel
private theorem endpoint_7_57_p4 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 0 4 200253576578794908 = some 200253576578794908 :=
  join_receipt_window endpoint_7_57_flag endpoint_7_57_sources 0 2 2 200253576578794908 200253576578794908 200253576578794908 endpoint_7_57_w0 endpoint_7_57_w2
private theorem endpoint_7_57_w4 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 4 2 200253576578794908 = some 200253576578794908 := by decide +kernel
private theorem endpoint_7_57_p6 : receiptWindow endpoint_7_57_flag endpoint_7_57_sources 0 6 200253576578794908 = some 200253576578794908 :=
  join_receipt_window endpoint_7_57_flag endpoint_7_57_sources 0 4 2 200253576578794908 200253576578794908 200253576578794908 endpoint_7_57_p4 endpoint_7_57_w4
def endpoint_7_57 : CertifiedEndpoint :=
  ⟨⟨7, 57, 3520⟩, 200253576578794908, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_7_57_flag endpoint_7_57_sources 6 200253576578794908 200253576578794908 rfl endpoint_7_57_base endpoint_7_57_p6) (by decide)⟩
private def endpoint_7_58_flag : Flag := ⟨7, 58, 3485⟩
private def endpoint_7_58_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_58_base : receiptBase endpoint_7_58_flag endpoint_7_58_sources = some 201999119847879462 := by decide +kernel
private theorem endpoint_7_58_w0 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 0 2 201999119847879462 = some 201999119847879462 := by decide +kernel
private theorem endpoint_7_58_w2 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 2 2 201999119847879462 = some 201999119847879462 := by decide +kernel
private theorem endpoint_7_58_p4 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 0 4 201999119847879462 = some 201999119847879462 :=
  join_receipt_window endpoint_7_58_flag endpoint_7_58_sources 0 2 2 201999119847879462 201999119847879462 201999119847879462 endpoint_7_58_w0 endpoint_7_58_w2
private theorem endpoint_7_58_w4 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 4 2 201999119847879462 = some 201999119847879462 := by decide +kernel
private theorem endpoint_7_58_p6 : receiptWindow endpoint_7_58_flag endpoint_7_58_sources 0 6 201999119847879462 = some 201999119847879462 :=
  join_receipt_window endpoint_7_58_flag endpoint_7_58_sources 0 4 2 201999119847879462 201999119847879462 201999119847879462 endpoint_7_58_p4 endpoint_7_58_w4
def endpoint_7_58 : CertifiedEndpoint :=
  ⟨⟨7, 58, 3485⟩, 201999119847879462, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_58_flag endpoint_7_58_sources 6 201999119847879462 201999119847879462 rfl endpoint_7_58_base endpoint_7_58_p6) (by decide)⟩
private def endpoint_7_59_flag : Flag := ⟨7, 59, 3449⟩
private def endpoint_7_59_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_59_base : receiptBase endpoint_7_59_flag endpoint_7_59_sources = some 202970006688594093 := by decide +kernel
private theorem endpoint_7_59_w0 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 0 2 202970006688594093 = some 202970006688594093 := by decide +kernel
private theorem endpoint_7_59_w2 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 2 2 202970006688594093 = some 202970006688594093 := by decide +kernel
private theorem endpoint_7_59_p4 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 0 4 202970006688594093 = some 202970006688594093 :=
  join_receipt_window endpoint_7_59_flag endpoint_7_59_sources 0 2 2 202970006688594093 202970006688594093 202970006688594093 endpoint_7_59_w0 endpoint_7_59_w2
private theorem endpoint_7_59_w4 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 4 2 202970006688594093 = some 202970006688594093 := by decide +kernel
private theorem endpoint_7_59_p6 : receiptWindow endpoint_7_59_flag endpoint_7_59_sources 0 6 202970006688594093 = some 202970006688594093 :=
  join_receipt_window endpoint_7_59_flag endpoint_7_59_sources 0 4 2 202970006688594093 202970006688594093 202970006688594093 endpoint_7_59_p4 endpoint_7_59_w4
def endpoint_7_59 : CertifiedEndpoint :=
  ⟨⟨7, 59, 3449⟩, 202970006688594093, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_59_flag endpoint_7_59_sources 6 202970006688594093 202970006688594093 rfl endpoint_7_59_base endpoint_7_59_p6) (by decide)⟩
private def endpoint_7_60_flag : Flag := ⟨7, 60, 3413⟩
private def endpoint_7_60_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_60_base : receiptBase endpoint_7_60_flag endpoint_7_60_sources = some 203877159967688325 := by decide +kernel
private theorem endpoint_7_60_w0 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 0 2 203877159967688325 = some 203877159967688325 := by decide +kernel
private theorem endpoint_7_60_w2 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 2 2 203877159967688325 = some 203877159967688325 := by decide +kernel
private theorem endpoint_7_60_p4 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 0 4 203877159967688325 = some 203877159967688325 :=
  join_receipt_window endpoint_7_60_flag endpoint_7_60_sources 0 2 2 203877159967688325 203877159967688325 203877159967688325 endpoint_7_60_w0 endpoint_7_60_w2
private theorem endpoint_7_60_w4 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 4 2 203877159967688325 = some 203877159967688325 := by decide +kernel
private theorem endpoint_7_60_p6 : receiptWindow endpoint_7_60_flag endpoint_7_60_sources 0 6 203877159967688325 = some 203877159967688325 :=
  join_receipt_window endpoint_7_60_flag endpoint_7_60_sources 0 4 2 203877159967688325 203877159967688325 203877159967688325 endpoint_7_60_p4 endpoint_7_60_w4
def endpoint_7_60 : CertifiedEndpoint :=
  ⟨⟨7, 60, 3413⟩, 203877159967688325, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_60_flag endpoint_7_60_sources 6 203877159967688325 203877159967688325 rfl endpoint_7_60_base endpoint_7_60_p6) (by decide)⟩
private def endpoint_7_61_flag : Flag := ⟨7, 61, 3375⟩
private def endpoint_7_61_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_61_base : receiptBase endpoint_7_61_flag endpoint_7_61_sources = some 204600790642571226 := by decide +kernel
private theorem endpoint_7_61_w0 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 0 2 204600790642571226 = some 204600790642571226 := by decide +kernel
private theorem endpoint_7_61_w2 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 2 2 204600790642571226 = some 204600790642571226 := by decide +kernel
private theorem endpoint_7_61_p4 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 0 4 204600790642571226 = some 204600790642571226 :=
  join_receipt_window endpoint_7_61_flag endpoint_7_61_sources 0 2 2 204600790642571226 204600790642571226 204600790642571226 endpoint_7_61_w0 endpoint_7_61_w2
private theorem endpoint_7_61_w4 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 4 2 204600790642571226 = some 204600790642571226 := by decide +kernel
private theorem endpoint_7_61_p6 : receiptWindow endpoint_7_61_flag endpoint_7_61_sources 0 6 204600790642571226 = some 204600790642571226 :=
  join_receipt_window endpoint_7_61_flag endpoint_7_61_sources 0 4 2 204600790642571226 204600790642571226 204600790642571226 endpoint_7_61_p4 endpoint_7_61_w4
def endpoint_7_61 : CertifiedEndpoint :=
  ⟨⟨7, 61, 3375⟩, 204600790642571226, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_61_flag endpoint_7_61_sources 6 204600790642571226 204600790642571226 rfl endpoint_7_61_base endpoint_7_61_p6) (by decide)⟩
private def endpoint_7_62_flag : Flag := ⟨7, 62, 3335⟩
private def endpoint_7_62_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_7_62_base : receiptBase endpoint_7_62_flag endpoint_7_62_sources = some 205135660338315093 := by decide +kernel
private theorem endpoint_7_62_w0 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 0 2 205135660338315093 = some 205135660338315093 := by decide +kernel
private theorem endpoint_7_62_w2 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 2 2 205135660338315093 = some 205135660338315093 := by decide +kernel
private theorem endpoint_7_62_p4 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 0 4 205135660338315093 = some 205135660338315093 :=
  join_receipt_window endpoint_7_62_flag endpoint_7_62_sources 0 2 2 205135660338315093 205135660338315093 205135660338315093 endpoint_7_62_w0 endpoint_7_62_w2
private theorem endpoint_7_62_w4 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 4 2 205135660338315093 = some 205135660338315093 := by decide +kernel
private theorem endpoint_7_62_p6 : receiptWindow endpoint_7_62_flag endpoint_7_62_sources 0 6 205135660338315093 = some 205135660338315093 :=
  join_receipt_window endpoint_7_62_flag endpoint_7_62_sources 0 4 2 205135660338315093 205135660338315093 205135660338315093 endpoint_7_62_p4 endpoint_7_62_w4
def endpoint_7_62 : CertifiedEndpoint :=
  ⟨⟨7, 62, 3335⟩, 205135660338315093, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_7_62_flag endpoint_7_62_sources 6 205135660338315093 205135660338315093 rfl endpoint_7_62_base endpoint_7_62_p6) (by decide)⟩
private def endpoint_7_63_flag : Flag := ⟨7, 63, 3295⟩
private def endpoint_7_63_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_63_base : receiptBase endpoint_7_63_flag endpoint_7_63_sources = some 207746229662647866 := by decide +kernel
private theorem endpoint_7_63_w0 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 0 2 207746229662647866 = some 207746229662647866 := by decide +kernel
private theorem endpoint_7_63_w2 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 2 2 207746229662647866 = some 207746229662647866 := by decide +kernel
private theorem endpoint_7_63_p4 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 0 4 207746229662647866 = some 207746229662647866 :=
  join_receipt_window endpoint_7_63_flag endpoint_7_63_sources 0 2 2 207746229662647866 207746229662647866 207746229662647866 endpoint_7_63_w0 endpoint_7_63_w2
private theorem endpoint_7_63_w4 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 4 2 207746229662647866 = some 207746229662647866 := by decide +kernel
private theorem endpoint_7_63_p6 : receiptWindow endpoint_7_63_flag endpoint_7_63_sources 0 6 207746229662647866 = some 207746229662647866 :=
  join_receipt_window endpoint_7_63_flag endpoint_7_63_sources 0 4 2 207746229662647866 207746229662647866 207746229662647866 endpoint_7_63_p4 endpoint_7_63_w4
def endpoint_7_63 : CertifiedEndpoint :=
  ⟨⟨7, 63, 3295⟩, 207746229662647866, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_63_flag endpoint_7_63_sources 6 207746229662647866 207746229662647866 rfl endpoint_7_63_base endpoint_7_63_p6) (by decide)⟩
private def endpoint_7_64_flag : Flag := ⟨7, 64, 3252⟩
private def endpoint_7_64_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_64_base : receiptBase endpoint_7_64_flag endpoint_7_64_sources = some 207936751780189337 := by decide +kernel
private theorem endpoint_7_64_w0 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 0 2 207936751780189337 = some 207936751780189337 := by decide +kernel
private theorem endpoint_7_64_w2 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 2 2 207936751780189337 = some 207936751780189337 := by decide +kernel
private theorem endpoint_7_64_p4 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 0 4 207936751780189337 = some 207936751780189337 :=
  join_receipt_window endpoint_7_64_flag endpoint_7_64_sources 0 2 2 207936751780189337 207936751780189337 207936751780189337 endpoint_7_64_w0 endpoint_7_64_w2
private theorem endpoint_7_64_w4 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 4 2 207936751780189337 = some 207936751780189337 := by decide +kernel
private theorem endpoint_7_64_p6 : receiptWindow endpoint_7_64_flag endpoint_7_64_sources 0 6 207936751780189337 = some 207936751780189337 :=
  join_receipt_window endpoint_7_64_flag endpoint_7_64_sources 0 4 2 207936751780189337 207936751780189337 207936751780189337 endpoint_7_64_p4 endpoint_7_64_w4
def endpoint_7_64 : CertifiedEndpoint :=
  ⟨⟨7, 64, 3252⟩, 207936751780189337, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_64_flag endpoint_7_64_sources 6 207936751780189337 207936751780189337 rfl endpoint_7_64_base endpoint_7_64_p6) (by decide)⟩
private def endpoint_7_65_flag : Flag := ⟨7, 65, 3208⟩
private def endpoint_7_65_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_65_base : receiptBase endpoint_7_65_flag endpoint_7_65_sources = some 207986312172393620 := by decide +kernel
private theorem endpoint_7_65_w0 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 0 2 207986312172393620 = some 207986312172393620 := by decide +kernel
private theorem endpoint_7_65_w2 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 2 2 207986312172393620 = some 207986312172393620 := by decide +kernel
private theorem endpoint_7_65_p4 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 0 4 207986312172393620 = some 207986312172393620 :=
  join_receipt_window endpoint_7_65_flag endpoint_7_65_sources 0 2 2 207986312172393620 207986312172393620 207986312172393620 endpoint_7_65_w0 endpoint_7_65_w2
private theorem endpoint_7_65_w4 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 4 2 207986312172393620 = some 207986312172393620 := by decide +kernel
private theorem endpoint_7_65_p6 : receiptWindow endpoint_7_65_flag endpoint_7_65_sources 0 6 207986312172393620 = some 207986312172393620 :=
  join_receipt_window endpoint_7_65_flag endpoint_7_65_sources 0 4 2 207986312172393620 207986312172393620 207986312172393620 endpoint_7_65_p4 endpoint_7_65_w4
def endpoint_7_65 : CertifiedEndpoint :=
  ⟨⟨7, 65, 3208⟩, 207986312172393620, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_65_flag endpoint_7_65_sources 6 207986312172393620 207986312172393620 rfl endpoint_7_65_base endpoint_7_65_p6) (by decide)⟩
private def endpoint_7_66_flag : Flag := ⟨7, 66, 3161⟩
private def endpoint_7_66_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_7_66_base : receiptBase endpoint_7_66_flag endpoint_7_66_sources = some 207762055173773858 := by decide +kernel
private theorem endpoint_7_66_w0 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 0 2 207762055173773858 = some 207762055173773858 := by decide +kernel
private theorem endpoint_7_66_w2 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 2 2 207762055173773858 = some 207762055173773858 := by decide +kernel
private theorem endpoint_7_66_p4 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 0 4 207762055173773858 = some 207762055173773858 :=
  join_receipt_window endpoint_7_66_flag endpoint_7_66_sources 0 2 2 207762055173773858 207762055173773858 207762055173773858 endpoint_7_66_w0 endpoint_7_66_w2
private theorem endpoint_7_66_w4 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 4 2 207762055173773858 = some 207762055173773858 := by decide +kernel
private theorem endpoint_7_66_p6 : receiptWindow endpoint_7_66_flag endpoint_7_66_sources 0 6 207762055173773858 = some 207762055173773858 :=
  join_receipt_window endpoint_7_66_flag endpoint_7_66_sources 0 4 2 207762055173773858 207762055173773858 207762055173773858 endpoint_7_66_p4 endpoint_7_66_w4
def endpoint_7_66 : CertifiedEndpoint :=
  ⟨⟨7, 66, 3161⟩, 207762055173773858, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_7_66_flag endpoint_7_66_sources 6 207762055173773858 207762055173773858 rfl endpoint_7_66_base endpoint_7_66_p6) (by decide)⟩
private def endpoint_7_67_flag : Flag := ⟨7, 67, 3112⟩
private def endpoint_7_67_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_7_67_base : receiptBase endpoint_7_67_flag endpoint_7_67_sources = some 208819363658210001 := by decide +kernel
private theorem endpoint_7_67_w0 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 0 2 208819363658210001 = some 208819363658210001 := by decide +kernel
private theorem endpoint_7_67_w2 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 2 2 208819363658210001 = some 208819363658210001 := by decide +kernel
private theorem endpoint_7_67_p4 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 0 4 208819363658210001 = some 208819363658210001 :=
  join_receipt_window endpoint_7_67_flag endpoint_7_67_sources 0 2 2 208819363658210001 208819363658210001 208819363658210001 endpoint_7_67_w0 endpoint_7_67_w2
private theorem endpoint_7_67_w4 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 4 2 208819363658210001 = some 208819363658210001 := by decide +kernel
private theorem endpoint_7_67_p6 : receiptWindow endpoint_7_67_flag endpoint_7_67_sources 0 6 208819363658210001 = some 208819363658210001 :=
  join_receipt_window endpoint_7_67_flag endpoint_7_67_sources 0 4 2 208819363658210001 208819363658210001 208819363658210001 endpoint_7_67_p4 endpoint_7_67_w4
def endpoint_7_67 : CertifiedEndpoint :=
  ⟨⟨7, 67, 3112⟩, 208819363658210001, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_7_67_flag endpoint_7_67_sources 6 208819363658210001 208819363658210001 rfl endpoint_7_67_base endpoint_7_67_p6) (by decide)⟩
private def endpoint_7_68_flag : Flag := ⟨7, 68, 3061⟩
private def endpoint_7_68_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_7_68_base : receiptBase endpoint_7_68_flag endpoint_7_68_sources = some 208155260854856615 := by decide +kernel
private theorem endpoint_7_68_w0 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 0 2 208155260854856615 = some 208155260854856615 := by decide +kernel
private theorem endpoint_7_68_w2 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 2 2 208155260854856615 = some 208155260854856615 := by decide +kernel
private theorem endpoint_7_68_p4 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 0 4 208155260854856615 = some 208155260854856615 :=
  join_receipt_window endpoint_7_68_flag endpoint_7_68_sources 0 2 2 208155260854856615 208155260854856615 208155260854856615 endpoint_7_68_w0 endpoint_7_68_w2
private theorem endpoint_7_68_w4 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 4 2 208155260854856615 = some 208155260854856615 := by decide +kernel
private theorem endpoint_7_68_p6 : receiptWindow endpoint_7_68_flag endpoint_7_68_sources 0 6 208155260854856615 = some 208155260854856615 :=
  join_receipt_window endpoint_7_68_flag endpoint_7_68_sources 0 4 2 208155260854856615 208155260854856615 208155260854856615 endpoint_7_68_p4 endpoint_7_68_w4
def endpoint_7_68 : CertifiedEndpoint :=
  ⟨⟨7, 68, 3061⟩, 208155260854856615, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_7_68_flag endpoint_7_68_sources 6 208155260854856615 208155260854856615 rfl endpoint_7_68_base endpoint_7_68_p6) (by decide)⟩
private def endpoint_7_69_flag : Flag := ⟨7, 69, 3007⟩
private def endpoint_7_69_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_7_69_base : receiptBase endpoint_7_69_flag endpoint_7_69_sources = some 207194461935348528 := by decide +kernel
private theorem endpoint_7_69_w0 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 0 2 207194461935348528 = some 207194461935348528 := by decide +kernel
private theorem endpoint_7_69_w2 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 2 2 207194461935348528 = some 207194461935348528 := by decide +kernel
private theorem endpoint_7_69_p4 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 0 4 207194461935348528 = some 207194461935348528 :=
  join_receipt_window endpoint_7_69_flag endpoint_7_69_sources 0 2 2 207194461935348528 207194461935348528 207194461935348528 endpoint_7_69_w0 endpoint_7_69_w2
private theorem endpoint_7_69_w4 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 4 2 207194461935348528 = some 207194461935348528 := by decide +kernel
private theorem endpoint_7_69_p6 : receiptWindow endpoint_7_69_flag endpoint_7_69_sources 0 6 207194461935348528 = some 207194461935348528 :=
  join_receipt_window endpoint_7_69_flag endpoint_7_69_sources 0 4 2 207194461935348528 207194461935348528 207194461935348528 endpoint_7_69_p4 endpoint_7_69_w4
def endpoint_7_69 : CertifiedEndpoint :=
  ⟨⟨7, 69, 3007⟩, 207194461935348528, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_7_69_flag endpoint_7_69_sources 6 207194461935348528 207194461935348528 rfl endpoint_7_69_base endpoint_7_69_p6) (by decide)⟩
private def endpoint_7_70_flag : Flag := ⟨7, 70, 2950⟩
private def endpoint_7_70_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_7_70_base : receiptBase endpoint_7_70_flag endpoint_7_70_sources = some 207454508737225819 := by decide +kernel
private theorem endpoint_7_70_w0 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 0 2 207454508737225819 = some 207454508737225819 := by decide +kernel
private theorem endpoint_7_70_w2 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 2 2 207454508737225819 = some 207454508737225819 := by decide +kernel
private theorem endpoint_7_70_p4 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 0 4 207454508737225819 = some 207454508737225819 :=
  join_receipt_window endpoint_7_70_flag endpoint_7_70_sources 0 2 2 207454508737225819 207454508737225819 207454508737225819 endpoint_7_70_w0 endpoint_7_70_w2
private theorem endpoint_7_70_w4 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 4 2 207454508737225819 = some 207454508737225819 := by decide +kernel
private theorem endpoint_7_70_p6 : receiptWindow endpoint_7_70_flag endpoint_7_70_sources 0 6 207454508737225819 = some 207454508737225819 :=
  join_receipt_window endpoint_7_70_flag endpoint_7_70_sources 0 4 2 207454508737225819 207454508737225819 207454508737225819 endpoint_7_70_p4 endpoint_7_70_w4
def endpoint_7_70 : CertifiedEndpoint :=
  ⟨⟨7, 70, 2950⟩, 207454508737225819, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_7_70_flag endpoint_7_70_sources 6 207454508737225819 207454508737225819 rfl endpoint_7_70_base endpoint_7_70_p6) (by decide)⟩
private def endpoint_7_71_flag : Flag := ⟨7, 71, 2891⟩
private def endpoint_7_71_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_7_71_base : receiptBase endpoint_7_71_flag endpoint_7_71_sources = some 207492309776758766 := by decide +kernel
private theorem endpoint_7_71_w0 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 0 2 207492309776758766 = some 207492309776758766 := by decide +kernel
private theorem endpoint_7_71_w2 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 2 2 207492309776758766 = some 207492309776758766 := by decide +kernel
private theorem endpoint_7_71_p4 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 0 4 207492309776758766 = some 207492309776758766 :=
  join_receipt_window endpoint_7_71_flag endpoint_7_71_sources 0 2 2 207492309776758766 207492309776758766 207492309776758766 endpoint_7_71_w0 endpoint_7_71_w2
private theorem endpoint_7_71_w4 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 4 2 207492309776758766 = some 207492309776758766 := by decide +kernel
private theorem endpoint_7_71_p6 : receiptWindow endpoint_7_71_flag endpoint_7_71_sources 0 6 207492309776758766 = some 207492309776758766 :=
  join_receipt_window endpoint_7_71_flag endpoint_7_71_sources 0 4 2 207492309776758766 207492309776758766 207492309776758766 endpoint_7_71_p4 endpoint_7_71_w4
def endpoint_7_71 : CertifiedEndpoint :=
  ⟨⟨7, 71, 2891⟩, 207492309776758766, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_7_71_flag endpoint_7_71_sources 6 207492309776758766 207492309776758766 rfl endpoint_7_71_base endpoint_7_71_p6) (by decide)⟩
private def endpoint_7_72_flag : Flag := ⟨7, 72, 2829⟩
private def endpoint_7_72_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_7_72_base : receiptBase endpoint_7_72_flag endpoint_7_72_sources = some 205640702580625678 := by decide +kernel
private theorem endpoint_7_72_w0 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 0 2 205640702580625678 = some 205640702580625678 := by decide +kernel
private theorem endpoint_7_72_w2 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 2 2 205640702580625678 = some 205640702580625678 := by decide +kernel
private theorem endpoint_7_72_p4 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 0 4 205640702580625678 = some 205640702580625678 :=
  join_receipt_window endpoint_7_72_flag endpoint_7_72_sources 0 2 2 205640702580625678 205640702580625678 205640702580625678 endpoint_7_72_w0 endpoint_7_72_w2
private theorem endpoint_7_72_w4 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 4 2 205640702580625678 = some 205640702580625678 := by decide +kernel
private theorem endpoint_7_72_p6 : receiptWindow endpoint_7_72_flag endpoint_7_72_sources 0 6 205640702580625678 = some 205640702580625678 :=
  join_receipt_window endpoint_7_72_flag endpoint_7_72_sources 0 4 2 205640702580625678 205640702580625678 205640702580625678 endpoint_7_72_p4 endpoint_7_72_w4
def endpoint_7_72 : CertifiedEndpoint :=
  ⟨⟨7, 72, 2829⟩, 205640702580625678, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_7_72_flag endpoint_7_72_sources 6 205640702580625678 205640702580625678 rfl endpoint_7_72_base endpoint_7_72_p6) (by decide)⟩
private def endpoint_7_73_flag : Flag := ⟨7, 73, 2764⟩
private def endpoint_7_73_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_7_73_base : receiptBase endpoint_7_73_flag endpoint_7_73_sources = some 206482802071314814 := by decide +kernel
private theorem endpoint_7_73_w0 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 0 2 206482802071314814 = some 206482802071314814 := by decide +kernel
private theorem endpoint_7_73_w2 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 2 2 206482802071314814 = some 206482802071314814 := by decide +kernel
private theorem endpoint_7_73_p4 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 0 4 206482802071314814 = some 206482802071314814 :=
  join_receipt_window endpoint_7_73_flag endpoint_7_73_sources 0 2 2 206482802071314814 206482802071314814 206482802071314814 endpoint_7_73_w0 endpoint_7_73_w2
private theorem endpoint_7_73_w4 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 4 2 206482802071314814 = some 206482802071314814 := by decide +kernel
private theorem endpoint_7_73_p6 : receiptWindow endpoint_7_73_flag endpoint_7_73_sources 0 6 206482802071314814 = some 206482802071314814 :=
  join_receipt_window endpoint_7_73_flag endpoint_7_73_sources 0 4 2 206482802071314814 206482802071314814 206482802071314814 endpoint_7_73_p4 endpoint_7_73_w4
def endpoint_7_73 : CertifiedEndpoint :=
  ⟨⟨7, 73, 2764⟩, 206482802071314814, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_7_73_flag endpoint_7_73_sources 6 206482802071314814 206482802071314814 rfl endpoint_7_73_base endpoint_7_73_p6) (by decide)⟩
private def endpoint_7_74_flag : Flag := ⟨7, 74, 2697⟩
private def endpoint_7_74_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_7_74_base : receiptBase endpoint_7_74_flag endpoint_7_74_sources = some 203996538817858661 := by decide +kernel
private theorem endpoint_7_74_w0 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 0 2 203996538817858661 = some 203996538817858661 := by decide +kernel
private theorem endpoint_7_74_w2 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 2 2 203996538817858661 = some 203996538817858661 := by decide +kernel
private theorem endpoint_7_74_p4 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 0 4 203996538817858661 = some 203996538817858661 :=
  join_receipt_window endpoint_7_74_flag endpoint_7_74_sources 0 2 2 203996538817858661 203996538817858661 203996538817858661 endpoint_7_74_w0 endpoint_7_74_w2
private theorem endpoint_7_74_w4 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 4 2 203996538817858661 = some 203996538817858661 := by decide +kernel
private theorem endpoint_7_74_p6 : receiptWindow endpoint_7_74_flag endpoint_7_74_sources 0 6 203996538817858661 = some 203996538817858661 :=
  join_receipt_window endpoint_7_74_flag endpoint_7_74_sources 0 4 2 203996538817858661 203996538817858661 203996538817858661 endpoint_7_74_p4 endpoint_7_74_w4
def endpoint_7_74 : CertifiedEndpoint :=
  ⟨⟨7, 74, 2697⟩, 203996538817858661, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_7_74_flag endpoint_7_74_sources 6 203996538817858661 203996538817858661 rfl endpoint_7_74_base endpoint_7_74_p6) (by decide)⟩
private def endpoint_7_75_flag : Flag := ⟨7, 75, 2627⟩
private def endpoint_7_75_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_7_75_base : receiptBase endpoint_7_75_flag endpoint_7_75_sources = some 201156861855985049 := by decide +kernel
private theorem endpoint_7_75_w0 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 0 2 201156861855985049 = some 201156861855985049 := by decide +kernel
private theorem endpoint_7_75_w2 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 2 2 201156861855985049 = some 201156861855985049 := by decide +kernel
private theorem endpoint_7_75_p4 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 0 4 201156861855985049 = some 201156861855985049 :=
  join_receipt_window endpoint_7_75_flag endpoint_7_75_sources 0 2 2 201156861855985049 201156861855985049 201156861855985049 endpoint_7_75_w0 endpoint_7_75_w2
private theorem endpoint_7_75_w4 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 4 2 201156861855985049 = some 201156861855985049 := by decide +kernel
private theorem endpoint_7_75_p6 : receiptWindow endpoint_7_75_flag endpoint_7_75_sources 0 6 201156861855985049 = some 201156861855985049 :=
  join_receipt_window endpoint_7_75_flag endpoint_7_75_sources 0 4 2 201156861855985049 201156861855985049 201156861855985049 endpoint_7_75_p4 endpoint_7_75_w4
def endpoint_7_75 : CertifiedEndpoint :=
  ⟨⟨7, 75, 2627⟩, 201156861855985049, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_7_75_flag endpoint_7_75_sources 6 201156861855985049 201156861855985049 rfl endpoint_7_75_base endpoint_7_75_p6) (by decide)⟩
private def endpoint_7_76_flag : Flag := ⟨7, 76, 2554⟩
private def endpoint_7_76_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_7_76_base : receiptBase endpoint_7_76_flag endpoint_7_76_sources = some 201646373454173534 := by decide +kernel
private theorem endpoint_7_76_w0 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 0 2 201646373454173534 = some 201646373454173534 := by decide +kernel
private theorem endpoint_7_76_w2 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 2 2 201646373454173534 = some 201646373454173534 := by decide +kernel
private theorem endpoint_7_76_p4 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 0 4 201646373454173534 = some 201646373454173534 :=
  join_receipt_window endpoint_7_76_flag endpoint_7_76_sources 0 2 2 201646373454173534 201646373454173534 201646373454173534 endpoint_7_76_w0 endpoint_7_76_w2
private theorem endpoint_7_76_w4 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 4 2 201646373454173534 = some 201646373454173534 := by decide +kernel
private theorem endpoint_7_76_p6 : receiptWindow endpoint_7_76_flag endpoint_7_76_sources 0 6 201646373454173534 = some 201646373454173534 :=
  join_receipt_window endpoint_7_76_flag endpoint_7_76_sources 0 4 2 201646373454173534 201646373454173534 201646373454173534 endpoint_7_76_p4 endpoint_7_76_w4
def endpoint_7_76 : CertifiedEndpoint :=
  ⟨⟨7, 76, 2554⟩, 201646373454173534, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_7_76_flag endpoint_7_76_sources 6 201646373454173534 201646373454173534 rfl endpoint_7_76_base endpoint_7_76_p6) (by decide)⟩
private def endpoint_7_77_flag : Flag := ⟨7, 77, 2478⟩
private def endpoint_7_77_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_7_77_base : receiptBase endpoint_7_77_flag endpoint_7_77_sources = some 198045879818441642 := by decide +kernel
private theorem endpoint_7_77_w0 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 0 2 198045879818441642 = some 198045879818441642 := by decide +kernel
private theorem endpoint_7_77_w2 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 2 2 198045879818441642 = some 198045879818441642 := by decide +kernel
private theorem endpoint_7_77_p4 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 0 4 198045879818441642 = some 198045879818441642 :=
  join_receipt_window endpoint_7_77_flag endpoint_7_77_sources 0 2 2 198045879818441642 198045879818441642 198045879818441642 endpoint_7_77_w0 endpoint_7_77_w2
private theorem endpoint_7_77_w4 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 4 2 198045879818441642 = some 198045879818441642 := by decide +kernel
private theorem endpoint_7_77_p6 : receiptWindow endpoint_7_77_flag endpoint_7_77_sources 0 6 198045879818441642 = some 198045879818441642 :=
  join_receipt_window endpoint_7_77_flag endpoint_7_77_sources 0 4 2 198045879818441642 198045879818441642 198045879818441642 endpoint_7_77_p4 endpoint_7_77_w4
def endpoint_7_77 : CertifiedEndpoint :=
  ⟨⟨7, 77, 2478⟩, 198045879818441642, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_7_77_flag endpoint_7_77_sources 6 198045879818441642 198045879818441642 rfl endpoint_7_77_base endpoint_7_77_p6) (by decide)⟩
private def endpoint_7_78_flag : Flag := ⟨7, 78, 2400⟩
private def endpoint_7_78_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_7_78_base : receiptBase endpoint_7_78_flag endpoint_7_78_sources = some 194143916390590485 := by decide +kernel
private theorem endpoint_7_78_w0 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 0 2 194143916390590485 = some 194143916390590485 := by decide +kernel
private theorem endpoint_7_78_w2 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 2 2 194143916390590485 = some 194143916390590485 := by decide +kernel
private theorem endpoint_7_78_p4 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 0 4 194143916390590485 = some 194143916390590485 :=
  join_receipt_window endpoint_7_78_flag endpoint_7_78_sources 0 2 2 194143916390590485 194143916390590485 194143916390590485 endpoint_7_78_w0 endpoint_7_78_w2
private theorem endpoint_7_78_w4 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 4 2 194143916390590485 = some 194143916390590485 := by decide +kernel
private theorem endpoint_7_78_p6 : receiptWindow endpoint_7_78_flag endpoint_7_78_sources 0 6 194143916390590485 = some 194143916390590485 :=
  join_receipt_window endpoint_7_78_flag endpoint_7_78_sources 0 4 2 194143916390590485 194143916390590485 194143916390590485 endpoint_7_78_p4 endpoint_7_78_w4
def endpoint_7_78 : CertifiedEndpoint :=
  ⟨⟨7, 78, 2400⟩, 194143916390590485, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_7_78_flag endpoint_7_78_sources 6 194143916390590485 194143916390590485 rfl endpoint_7_78_base endpoint_7_78_p6) (by decide)⟩
private def endpoint_7_79_flag : Flag := ⟨7, 79, 2319⟩
private def endpoint_7_79_sources : Sources := ⟨contact11, contact11, contact13⟩
private theorem endpoint_7_79_base : receiptBase endpoint_7_79_flag endpoint_7_79_sources = some 189854561195708165 := by decide +kernel
private theorem endpoint_7_79_w0 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 0 2 189854561195708165 = some 189854561195708165 := by decide +kernel
private theorem endpoint_7_79_w2 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 2 2 189854561195708165 = some 189854561195708165 := by decide +kernel
private theorem endpoint_7_79_p4 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 0 4 189854561195708165 = some 189854561195708165 :=
  join_receipt_window endpoint_7_79_flag endpoint_7_79_sources 0 2 2 189854561195708165 189854561195708165 189854561195708165 endpoint_7_79_w0 endpoint_7_79_w2
private theorem endpoint_7_79_w4 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 4 2 189854561195708165 = some 189854561195708165 := by decide +kernel
private theorem endpoint_7_79_p6 : receiptWindow endpoint_7_79_flag endpoint_7_79_sources 0 6 189854561195708165 = some 189854561195708165 :=
  join_receipt_window endpoint_7_79_flag endpoint_7_79_sources 0 4 2 189854561195708165 189854561195708165 189854561195708165 endpoint_7_79_p4 endpoint_7_79_w4
def endpoint_7_79 : CertifiedEndpoint :=
  ⟨⟨7, 79, 2319⟩, 189854561195708165, .terminal ⟨contact11, contact11, contact13⟩ (finish_receipt_window endpoint_7_79_flag endpoint_7_79_sources 6 189854561195708165 189854561195708165 rfl endpoint_7_79_base endpoint_7_79_p6) (by decide)⟩
private def endpoint_7_80_flag : Flag := ⟨7, 80, 2235⟩
private def endpoint_7_80_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_7_80_base : receiptBase endpoint_7_80_flag endpoint_7_80_sources = some 187223522944429496 := by decide +kernel
private theorem endpoint_7_80_w0 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 0 2 187223522944429496 = some 187223522944429496 := by decide +kernel
private theorem endpoint_7_80_w2 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 2 2 187223522944429496 = some 187223522944429496 := by decide +kernel
private theorem endpoint_7_80_p4 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 0 4 187223522944429496 = some 187223522944429496 :=
  join_receipt_window endpoint_7_80_flag endpoint_7_80_sources 0 2 2 187223522944429496 187223522944429496 187223522944429496 endpoint_7_80_w0 endpoint_7_80_w2
private theorem endpoint_7_80_w4 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 4 2 187223522944429496 = some 187223522944429496 := by decide +kernel
private theorem endpoint_7_80_p6 : receiptWindow endpoint_7_80_flag endpoint_7_80_sources 0 6 187223522944429496 = some 187223522944429496 :=
  join_receipt_window endpoint_7_80_flag endpoint_7_80_sources 0 4 2 187223522944429496 187223522944429496 187223522944429496 endpoint_7_80_p4 endpoint_7_80_w4
def endpoint_7_80 : CertifiedEndpoint :=
  ⟨⟨7, 80, 2235⟩, 187223522944429496, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_7_80_flag endpoint_7_80_sources 6 187223522944429496 187223522944429496 rfl endpoint_7_80_base endpoint_7_80_p6) (by decide)⟩
private def endpoint_7_81_flag : Flag := ⟨7, 81, 2149⟩
private def endpoint_7_81_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_7_81_base : receiptBase endpoint_7_81_flag endpoint_7_81_sources = some 182097799272837448 := by decide +kernel
private theorem endpoint_7_81_w0 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 0 2 182097799272837448 = some 182097799272837448 := by decide +kernel
private theorem endpoint_7_81_w2 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 2 2 182097799272837448 = some 182097799272837448 := by decide +kernel
private theorem endpoint_7_81_p4 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 0 4 182097799272837448 = some 182097799272837448 :=
  join_receipt_window endpoint_7_81_flag endpoint_7_81_sources 0 2 2 182097799272837448 182097799272837448 182097799272837448 endpoint_7_81_w0 endpoint_7_81_w2
private theorem endpoint_7_81_w4 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 4 2 182097799272837448 = some 182097799272837448 := by decide +kernel
private theorem endpoint_7_81_p6 : receiptWindow endpoint_7_81_flag endpoint_7_81_sources 0 6 182097799272837448 = some 182097799272837448 :=
  join_receipt_window endpoint_7_81_flag endpoint_7_81_sources 0 4 2 182097799272837448 182097799272837448 182097799272837448 endpoint_7_81_p4 endpoint_7_81_w4
def endpoint_7_81 : CertifiedEndpoint :=
  ⟨⟨7, 81, 2149⟩, 182097799272837448, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_7_81_flag endpoint_7_81_sources 6 182097799272837448 182097799272837448 rfl endpoint_7_81_base endpoint_7_81_p6) (by decide)⟩
private def endpoint_7_82_flag : Flag := ⟨7, 82, 2060⟩
private def endpoint_7_82_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_7_82_base : receiptBase endpoint_7_82_flag endpoint_7_82_sources = some 176553751136992923 := by decide +kernel
private theorem endpoint_7_82_w0 : receiptWindow endpoint_7_82_flag endpoint_7_82_sources 0 2 176553751136992923 = some 176553751136992923 := by decide +kernel
private theorem endpoint_7_82_w2 : receiptWindow endpoint_7_82_flag endpoint_7_82_sources 2 2 176553751136992923 = some 176553751136992923 := by decide +kernel
private theorem endpoint_7_82_p4 : receiptWindow endpoint_7_82_flag endpoint_7_82_sources 0 4 176553751136992923 = some 176553751136992923 :=
  join_receipt_window endpoint_7_82_flag endpoint_7_82_sources 0 2 2 176553751136992923 176553751136992923 176553751136992923 endpoint_7_82_w0 endpoint_7_82_w2
private theorem endpoint_7_82_w4 : receiptWindow endpoint_7_82_flag endpoint_7_82_sources 4 2 176553751136992923 = some 176553751136992923 := by decide +kernel
private theorem endpoint_7_82_p6 : receiptWindow endpoint_7_82_flag endpoint_7_82_sources 0 6 176553751136992923 = some 176553751136992923 :=
  join_receipt_window endpoint_7_82_flag endpoint_7_82_sources 0 4 2 176553751136992923 176553751136992923 176553751136992923 endpoint_7_82_p4 endpoint_7_82_w4
def endpoint_7_82 : CertifiedEndpoint :=
  ⟨⟨7, 82, 2060⟩, 176553751136992923, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_7_82_flag endpoint_7_82_sources 6 176553751136992923 176553751136992923 rfl endpoint_7_82_base endpoint_7_82_p6) (by decide)⟩
def endpoint_7_83 : CertifiedEndpoint :=
  ⟨⟨7, 83, 1968⟩, 255997506147367119, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_84 : CertifiedEndpoint :=
  ⟨⟨7, 84, 1874⟩, 246508374348745154, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_85 : CertifiedEndpoint :=
  ⟨⟨7, 85, 1777⟩, 236291871264286030, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_86 : CertifiedEndpoint :=
  ⟨⟨7, 86, 1677⟩, 225332843863622241, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_87 : CertifiedEndpoint :=
  ⟨⟨7, 87, 1574⟩, 213616139116386281, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_88 : CertifiedEndpoint :=
  ⟨⟨7, 88, 1469⟩, 201268040885039657, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_89 : CertifiedEndpoint :=
  ⟨⟨7, 89, 1361⟩, 188135326586467518, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_90 : CertifiedEndpoint :=
  ⟨⟨7, 90, 1250⟩, 174202843190302358, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_91 : CertifiedEndpoint :=
  ⟨⟨7, 91, 1137⟩, 159601925569128186, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_92 : CertifiedEndpoint :=
  ⟨⟨7, 92, 1020⟩, 144026128556715300, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_93 : CertifiedEndpoint :=
  ⟨⟨7, 93, 902⟩, 127904813841673241, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_94 : CertifiedEndpoint :=
  ⟨⟨7, 94, 780⟩, 110778313674657456, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_95 : CertifiedEndpoint :=
  ⟨⟨7, 95, 656⟩, 92932869181407639, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_96 : CertifiedEndpoint :=
  ⟨⟨7, 96, 528⟩, 74048565835367416, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_97 : CertifiedEndpoint :=
  ⟨⟨7, 97, 399⟩, 54574969365636336, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_98 : CertifiedEndpoint :=
  ⟨⟨7, 98, 266⟩, 34032207982379838, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_7_99 : CertifiedEndpoint :=
  ⟨⟨7, 99, 131⟩, 12719992171664288, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_8 : CertifiedEndpoint :=
  ⟨⟨8, 8, 4583⟩, 43166557314346471, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_9 : CertifiedEndpoint :=
  ⟨⟨8, 9, 4565⟩, 45853136997539254, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_10 : CertifiedEndpoint :=
  ⟨⟨8, 10, 4547⟩, 48517141749874585, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_11 : CertifiedEndpoint :=
  ⟨⟨8, 11, 4529⟩, 57096890758563122, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_12 : CertifiedEndpoint :=
  ⟨⟨8, 12, 4511⟩, 65604808915558477, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_13 : CertifiedEndpoint :=
  ⟨⟨8, 13, 4492⟩, 74024385926497889, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_14 : CertifiedEndpoint :=
  ⟨⟨8, 14, 4474⟩, 82386701005736794, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_15 : CertifiedEndpoint :=
  ⟨⟨8, 15, 4455⟩, 90656792190179584, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_16 : CertifiedEndpoint :=
  ⟨⟨8, 16, 4436⟩, 98851169774189020, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_17 : CertifiedEndpoint :=
  ⟨⟨8, 17, 4417⟩, 106969833757765102, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_18 : CertifiedEndpoint :=
  ⟨⟨8, 18, 4398⟩, 115012784140907830, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_19 : CertifiedEndpoint :=
  ⟨⟨8, 19, 4379⟩, 122980020923617204, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_20 : CertifiedEndpoint :=
  ⟨⟨8, 20, 4359⟩, 130841444190939861, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_21 : CertifiedEndpoint :=
  ⟨⟨8, 21, 4340⟩, 138655312398412441, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_22 : CertifiedEndpoint :=
  ⟨⟨8, 22, 4320⟩, 146359484341758132, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_23 : CertifiedEndpoint :=
  ⟨⟨8, 23, 4300⟩, 153984059935930297, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_24 : CertifiedEndpoint :=
  ⟨⟨8, 24, 4279⟩, 161491173768495229, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_25 : CertifiedEndpoint :=
  ⟨⟨8, 25, 4259⟩, 168954615289950256, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_26 : CertifiedEndpoint :=
  ⟨⟨8, 26, 4238⟩, 176296712301057878, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_27 : CertifiedEndpoint :=
  ⟨⟨8, 27, 4217⟩, 183555330214251802, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_28 : CertifiedEndpoint :=
  ⟨⟨8, 28, 4196⟩, 190730469029532028, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_29 : CertifiedEndpoint :=
  ⟨⟨8, 29, 4175⟩, 197822128746898556, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_30 : CertifiedEndpoint :=
  ⟨⟨8, 30, 4153⟩, 204780795707697163, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_31 : CertifiedEndpoint :=
  ⟨⟨8, 31, 4131⟩, 211652100821841900, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_32 : CertifiedEndpoint :=
  ⟨⟨8, 32, 4109⟩, 218436044089332767, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_33 : CertifiedEndpoint :=
  ⟨⟨8, 33, 4087⟩, 225132625510169764, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_34 : CertifiedEndpoint :=
  ⟨⟨8, 34, 4064⟩, 231684565928218324, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_35 : CertifiedEndpoint :=
  ⟨⟨8, 35, 4041⟩, 238145261750872842, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_36 : CertifiedEndpoint :=
  ⟨⟨8, 36, 4018⟩, 244514712978133318, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_37 : CertifiedEndpoint :=
  ⟨⟨8, 37, 3994⟩, 250729816330754927, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_38 : CertifiedEndpoint :=
  ⟨⟨8, 38, 3970⟩, 256849792339242322, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_8_39_flag : Flag := ⟨8, 39, 3946⟩
private def endpoint_8_39_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_39_base : receiptBase endpoint_8_39_flag endpoint_8_39_sources = some 174434486865227639 := by decide +kernel
private theorem endpoint_8_39_w0 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 2 174434486865227639 = some 174434486865227639 := by decide +kernel
private theorem endpoint_8_39_w2 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 2 2 174434486865227639 = some 174434486865227639 := by decide +kernel
private theorem endpoint_8_39_p4 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 4 174434486865227639 = some 174434486865227639 :=
  join_receipt_window endpoint_8_39_flag endpoint_8_39_sources 0 2 2 174434486865227639 174434486865227639 174434486865227639 endpoint_8_39_w0 endpoint_8_39_w2
private theorem endpoint_8_39_w4 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 4 2 174434486865227639 = some 174434486865227639 := by decide +kernel
private theorem endpoint_8_39_p6 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 6 174434486865227639 = some 174434486865227639 :=
  join_receipt_window endpoint_8_39_flag endpoint_8_39_sources 0 4 2 174434486865227639 174434486865227639 174434486865227639 endpoint_8_39_p4 endpoint_8_39_w4
private theorem endpoint_8_39_w6 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 6 1 174434486865227639 = some 174434486865227639 := by decide +kernel
private theorem endpoint_8_39_p7 : receiptWindow endpoint_8_39_flag endpoint_8_39_sources 0 7 174434486865227639 = some 174434486865227639 :=
  join_receipt_window endpoint_8_39_flag endpoint_8_39_sources 0 6 1 174434486865227639 174434486865227639 174434486865227639 endpoint_8_39_p6 endpoint_8_39_w6
def endpoint_8_39 : CertifiedEndpoint :=
  ⟨⟨8, 39, 3946⟩, 174434486865227639, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_39_flag endpoint_8_39_sources 7 174434486865227639 174434486865227639 rfl endpoint_8_39_base endpoint_8_39_p7) (by decide)⟩
private def endpoint_8_40_flag : Flag := ⟨8, 40, 3921⟩
private def endpoint_8_40_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_40_base : receiptBase endpoint_8_40_flag endpoint_8_40_sources = some 177065828188587594 := by decide +kernel
private theorem endpoint_8_40_w0 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 2 177065828188587594 = some 177065828188587594 := by decide +kernel
private theorem endpoint_8_40_w2 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 2 2 177065828188587594 = some 177065828188587594 := by decide +kernel
private theorem endpoint_8_40_p4 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 4 177065828188587594 = some 177065828188587594 :=
  join_receipt_window endpoint_8_40_flag endpoint_8_40_sources 0 2 2 177065828188587594 177065828188587594 177065828188587594 endpoint_8_40_w0 endpoint_8_40_w2
private theorem endpoint_8_40_w4 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 4 2 177065828188587594 = some 177065828188587594 := by decide +kernel
private theorem endpoint_8_40_p6 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 6 177065828188587594 = some 177065828188587594 :=
  join_receipt_window endpoint_8_40_flag endpoint_8_40_sources 0 4 2 177065828188587594 177065828188587594 177065828188587594 endpoint_8_40_p4 endpoint_8_40_w4
private theorem endpoint_8_40_w6 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 6 1 177065828188587594 = some 177065828188587594 := by decide +kernel
private theorem endpoint_8_40_p7 : receiptWindow endpoint_8_40_flag endpoint_8_40_sources 0 7 177065828188587594 = some 177065828188587594 :=
  join_receipt_window endpoint_8_40_flag endpoint_8_40_sources 0 6 1 177065828188587594 177065828188587594 177065828188587594 endpoint_8_40_p6 endpoint_8_40_w6
def endpoint_8_40 : CertifiedEndpoint :=
  ⟨⟨8, 40, 3921⟩, 177065828188587594, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_40_flag endpoint_8_40_sources 7 177065828188587594 177065828188587594 rfl endpoint_8_40_base endpoint_8_40_p7) (by decide)⟩
private def endpoint_8_41_flag : Flag := ⟨8, 41, 3896⟩
private def endpoint_8_41_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_41_base : receiptBase endpoint_8_41_flag endpoint_8_41_sources = some 179649597692919498 := by decide +kernel
private theorem endpoint_8_41_w0 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 2 179649597692919498 = some 179649597692919498 := by decide +kernel
private theorem endpoint_8_41_w2 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 2 2 179649597692919498 = some 179649597692919498 := by decide +kernel
private theorem endpoint_8_41_p4 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 4 179649597692919498 = some 179649597692919498 :=
  join_receipt_window endpoint_8_41_flag endpoint_8_41_sources 0 2 2 179649597692919498 179649597692919498 179649597692919498 endpoint_8_41_w0 endpoint_8_41_w2
private theorem endpoint_8_41_w4 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 4 2 179649597692919498 = some 179649597692919498 := by decide +kernel
private theorem endpoint_8_41_p6 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 6 179649597692919498 = some 179649597692919498 :=
  join_receipt_window endpoint_8_41_flag endpoint_8_41_sources 0 4 2 179649597692919498 179649597692919498 179649597692919498 endpoint_8_41_p4 endpoint_8_41_w4
private theorem endpoint_8_41_w6 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 6 1 179649597692919498 = some 179649597692919498 := by decide +kernel
private theorem endpoint_8_41_p7 : receiptWindow endpoint_8_41_flag endpoint_8_41_sources 0 7 179649597692919498 = some 179649597692919498 :=
  join_receipt_window endpoint_8_41_flag endpoint_8_41_sources 0 6 1 179649597692919498 179649597692919498 179649597692919498 endpoint_8_41_p6 endpoint_8_41_w6
def endpoint_8_41 : CertifiedEndpoint :=
  ⟨⟨8, 41, 3896⟩, 179649597692919498, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_41_flag endpoint_8_41_sources 7 179649597692919498 179649597692919498 rfl endpoint_8_41_base endpoint_8_41_p7) (by decide)⟩
private def endpoint_8_42_flag : Flag := ⟨8, 42, 3871⟩
private def endpoint_8_42_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_42_base : receiptBase endpoint_8_42_flag endpoint_8_42_sources = some 182185795378223350 := by decide +kernel
private theorem endpoint_8_42_w0 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 2 182185795378223350 = some 182185795378223350 := by decide +kernel
private theorem endpoint_8_42_w2 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 2 2 182185795378223350 = some 182185795378223350 := by decide +kernel
private theorem endpoint_8_42_p4 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 4 182185795378223350 = some 182185795378223350 :=
  join_receipt_window endpoint_8_42_flag endpoint_8_42_sources 0 2 2 182185795378223350 182185795378223350 182185795378223350 endpoint_8_42_w0 endpoint_8_42_w2
private theorem endpoint_8_42_w4 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 4 2 182185795378223350 = some 182185795378223350 := by decide +kernel
private theorem endpoint_8_42_p6 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 6 182185795378223350 = some 182185795378223350 :=
  join_receipt_window endpoint_8_42_flag endpoint_8_42_sources 0 4 2 182185795378223350 182185795378223350 182185795378223350 endpoint_8_42_p4 endpoint_8_42_w4
private theorem endpoint_8_42_w6 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 6 1 182185795378223350 = some 182185795378223350 := by decide +kernel
private theorem endpoint_8_42_p7 : receiptWindow endpoint_8_42_flag endpoint_8_42_sources 0 7 182185795378223350 = some 182185795378223350 :=
  join_receipt_window endpoint_8_42_flag endpoint_8_42_sources 0 6 1 182185795378223350 182185795378223350 182185795378223350 endpoint_8_42_p6 endpoint_8_42_w6
def endpoint_8_42 : CertifiedEndpoint :=
  ⟨⟨8, 42, 3871⟩, 182185795378223350, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_42_flag endpoint_8_42_sources 7 182185795378223350 182185795378223350 rfl endpoint_8_42_base endpoint_8_42_p7) (by decide)⟩
private def endpoint_8_43_flag : Flag := ⟨8, 43, 3845⟩
private def endpoint_8_43_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_43_base : receiptBase endpoint_8_43_flag endpoint_8_43_sources = some 184627149179506026 := by decide +kernel
private theorem endpoint_8_43_w0 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 2 184627149179506026 = some 184627149179506026 := by decide +kernel
private theorem endpoint_8_43_w2 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 2 2 184627149179506026 = some 184627149179506026 := by decide +kernel
private theorem endpoint_8_43_p4 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 4 184627149179506026 = some 184627149179506026 :=
  join_receipt_window endpoint_8_43_flag endpoint_8_43_sources 0 2 2 184627149179506026 184627149179506026 184627149179506026 endpoint_8_43_w0 endpoint_8_43_w2
private theorem endpoint_8_43_w4 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 4 2 184627149179506026 = some 184627149179506026 := by decide +kernel
private theorem endpoint_8_43_p6 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 6 184627149179506026 = some 184627149179506026 :=
  join_receipt_window endpoint_8_43_flag endpoint_8_43_sources 0 4 2 184627149179506026 184627149179506026 184627149179506026 endpoint_8_43_p4 endpoint_8_43_w4
private theorem endpoint_8_43_w6 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 6 1 184627149179506026 = some 184627149179506026 := by decide +kernel
private theorem endpoint_8_43_p7 : receiptWindow endpoint_8_43_flag endpoint_8_43_sources 0 7 184627149179506026 = some 184627149179506026 :=
  join_receipt_window endpoint_8_43_flag endpoint_8_43_sources 0 6 1 184627149179506026 184627149179506026 184627149179506026 endpoint_8_43_p6 endpoint_8_43_w6
def endpoint_8_43 : CertifiedEndpoint :=
  ⟨⟨8, 43, 3845⟩, 184627149179506026, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_43_flag endpoint_8_43_sources 7 184627149179506026 184627149179506026 rfl endpoint_8_43_base endpoint_8_43_p7) (by decide)⟩
private def endpoint_8_44_flag : Flag := ⟨8, 44, 3819⟩
private def endpoint_8_44_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_44_base : receiptBase endpoint_8_44_flag endpoint_8_44_sources = some 187019065600230138 := by decide +kernel
private theorem endpoint_8_44_w0 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 2 187019065600230138 = some 187019065600230138 := by decide +kernel
private theorem endpoint_8_44_w2 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 2 2 187019065600230138 = some 187019065600230138 := by decide +kernel
private theorem endpoint_8_44_p4 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 4 187019065600230138 = some 187019065600230138 :=
  join_receipt_window endpoint_8_44_flag endpoint_8_44_sources 0 2 2 187019065600230138 187019065600230138 187019065600230138 endpoint_8_44_w0 endpoint_8_44_w2
private theorem endpoint_8_44_w4 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 4 2 187019065600230138 = some 187019065600230138 := by decide +kernel
private theorem endpoint_8_44_p6 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 6 187019065600230138 = some 187019065600230138 :=
  join_receipt_window endpoint_8_44_flag endpoint_8_44_sources 0 4 2 187019065600230138 187019065600230138 187019065600230138 endpoint_8_44_p4 endpoint_8_44_w4
private theorem endpoint_8_44_w6 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 6 1 187019065600230138 = some 187019065600230138 := by decide +kernel
private theorem endpoint_8_44_p7 : receiptWindow endpoint_8_44_flag endpoint_8_44_sources 0 7 187019065600230138 = some 187019065600230138 :=
  join_receipt_window endpoint_8_44_flag endpoint_8_44_sources 0 6 1 187019065600230138 187019065600230138 187019065600230138 endpoint_8_44_p6 endpoint_8_44_w6
def endpoint_8_44 : CertifiedEndpoint :=
  ⟨⟨8, 44, 3819⟩, 187019065600230138, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_44_flag endpoint_8_44_sources 7 187019065600230138 187019065600230138 rfl endpoint_8_44_base endpoint_8_44_p7) (by decide)⟩
private def endpoint_8_45_flag : Flag := ⟨8, 45, 3792⟩
private def endpoint_8_45_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_45_base : receiptBase endpoint_8_45_flag endpoint_8_45_sources = some 189312407013872051 := by decide +kernel
private theorem endpoint_8_45_w0 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 2 189312407013872051 = some 189312407013872051 := by decide +kernel
private theorem endpoint_8_45_w2 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 2 2 189312407013872051 = some 189312407013872051 := by decide +kernel
private theorem endpoint_8_45_p4 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 4 189312407013872051 = some 189312407013872051 :=
  join_receipt_window endpoint_8_45_flag endpoint_8_45_sources 0 2 2 189312407013872051 189312407013872051 189312407013872051 endpoint_8_45_w0 endpoint_8_45_w2
private theorem endpoint_8_45_w4 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 4 2 189312407013872051 = some 189312407013872051 := by decide +kernel
private theorem endpoint_8_45_p6 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 6 189312407013872051 = some 189312407013872051 :=
  join_receipt_window endpoint_8_45_flag endpoint_8_45_sources 0 4 2 189312407013872051 189312407013872051 189312407013872051 endpoint_8_45_p4 endpoint_8_45_w4
private theorem endpoint_8_45_w6 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 6 1 189312407013872051 = some 189312407013872051 := by decide +kernel
private theorem endpoint_8_45_p7 : receiptWindow endpoint_8_45_flag endpoint_8_45_sources 0 7 189312407013872051 = some 189312407013872051 :=
  join_receipt_window endpoint_8_45_flag endpoint_8_45_sources 0 6 1 189312407013872051 189312407013872051 189312407013872051 endpoint_8_45_p6 endpoint_8_45_w6
def endpoint_8_45 : CertifiedEndpoint :=
  ⟨⟨8, 45, 3792⟩, 189312407013872051, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_45_flag endpoint_8_45_sources 7 189312407013872051 189312407013872051 rfl endpoint_8_45_base endpoint_8_45_p7) (by decide)⟩
private def endpoint_8_46_flag : Flag := ⟨8, 46, 3765⟩
private def endpoint_8_46_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_46_base : receiptBase endpoint_8_46_flag endpoint_8_46_sources = some 191554445485424889 := by decide +kernel
private theorem endpoint_8_46_w0 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 2 191554445485424889 = some 191554445485424889 := by decide +kernel
private theorem endpoint_8_46_w2 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 2 2 191554445485424889 = some 191554445485424889 := by decide +kernel
private theorem endpoint_8_46_p4 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 4 191554445485424889 = some 191554445485424889 :=
  join_receipt_window endpoint_8_46_flag endpoint_8_46_sources 0 2 2 191554445485424889 191554445485424889 191554445485424889 endpoint_8_46_w0 endpoint_8_46_w2
private theorem endpoint_8_46_w4 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 4 2 191554445485424889 = some 191554445485424889 := by decide +kernel
private theorem endpoint_8_46_p6 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 6 191554445485424889 = some 191554445485424889 :=
  join_receipt_window endpoint_8_46_flag endpoint_8_46_sources 0 4 2 191554445485424889 191554445485424889 191554445485424889 endpoint_8_46_p4 endpoint_8_46_w4
private theorem endpoint_8_46_w6 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 6 1 191554445485424889 = some 191554445485424889 := by decide +kernel
private theorem endpoint_8_46_p7 : receiptWindow endpoint_8_46_flag endpoint_8_46_sources 0 7 191554445485424889 = some 191554445485424889 :=
  join_receipt_window endpoint_8_46_flag endpoint_8_46_sources 0 6 1 191554445485424889 191554445485424889 191554445485424889 endpoint_8_46_p6 endpoint_8_46_w6
def endpoint_8_46 : CertifiedEndpoint :=
  ⟨⟨8, 46, 3765⟩, 191554445485424889, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_46_flag endpoint_8_46_sources 7 191554445485424889 191554445485424889 rfl endpoint_8_46_base endpoint_8_46_p7) (by decide)⟩
private def endpoint_8_47_flag : Flag := ⟨8, 47, 3738⟩
private def endpoint_8_47_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_47_base : receiptBase endpoint_8_47_flag endpoint_8_47_sources = some 193745181014888652 := by decide +kernel
private theorem endpoint_8_47_w0 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 2 193745181014888652 = some 193745181014888652 := by decide +kernel
private theorem endpoint_8_47_w2 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 2 2 193745181014888652 = some 193745181014888652 := by decide +kernel
private theorem endpoint_8_47_p4 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 4 193745181014888652 = some 193745181014888652 :=
  join_receipt_window endpoint_8_47_flag endpoint_8_47_sources 0 2 2 193745181014888652 193745181014888652 193745181014888652 endpoint_8_47_w0 endpoint_8_47_w2
private theorem endpoint_8_47_w4 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 4 2 193745181014888652 = some 193745181014888652 := by decide +kernel
private theorem endpoint_8_47_p6 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 6 193745181014888652 = some 193745181014888652 :=
  join_receipt_window endpoint_8_47_flag endpoint_8_47_sources 0 4 2 193745181014888652 193745181014888652 193745181014888652 endpoint_8_47_p4 endpoint_8_47_w4
private theorem endpoint_8_47_w6 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 6 1 193745181014888652 = some 193745181014888652 := by decide +kernel
private theorem endpoint_8_47_p7 : receiptWindow endpoint_8_47_flag endpoint_8_47_sources 0 7 193745181014888652 = some 193745181014888652 :=
  join_receipt_window endpoint_8_47_flag endpoint_8_47_sources 0 6 1 193745181014888652 193745181014888652 193745181014888652 endpoint_8_47_p6 endpoint_8_47_w6
def endpoint_8_47 : CertifiedEndpoint :=
  ⟨⟨8, 47, 3738⟩, 193745181014888652, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_47_flag endpoint_8_47_sources 7 193745181014888652 193745181014888652 rfl endpoint_8_47_base endpoint_8_47_p7) (by decide)⟩
private def endpoint_8_48_flag : Flag := ⟨8, 48, 3710⟩
private def endpoint_8_48_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_48_base : receiptBase endpoint_8_48_flag endpoint_8_48_sources = some 195832677633443936 := by decide +kernel
private theorem endpoint_8_48_w0 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 2 195832677633443936 = some 195832677633443936 := by decide +kernel
private theorem endpoint_8_48_w2 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 2 2 195832677633443936 = some 195832677633443936 := by decide +kernel
private theorem endpoint_8_48_p4 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 4 195832677633443936 = some 195832677633443936 :=
  join_receipt_window endpoint_8_48_flag endpoint_8_48_sources 0 2 2 195832677633443936 195832677633443936 195832677633443936 endpoint_8_48_w0 endpoint_8_48_w2
private theorem endpoint_8_48_w4 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 4 2 195832677633443936 = some 195832677633443936 := by decide +kernel
private theorem endpoint_8_48_p6 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 6 195832677633443936 = some 195832677633443936 :=
  join_receipt_window endpoint_8_48_flag endpoint_8_48_sources 0 4 2 195832677633443936 195832677633443936 195832677633443936 endpoint_8_48_p4 endpoint_8_48_w4
private theorem endpoint_8_48_w6 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 6 1 195832677633443936 = some 195832677633443936 := by decide +kernel
private theorem endpoint_8_48_p7 : receiptWindow endpoint_8_48_flag endpoint_8_48_sources 0 7 195832677633443936 = some 195832677633443936 :=
  join_receipt_window endpoint_8_48_flag endpoint_8_48_sources 0 6 1 195832677633443936 195832677633443936 195832677633443936 endpoint_8_48_p6 endpoint_8_48_w6
def endpoint_8_48 : CertifiedEndpoint :=
  ⟨⟨8, 48, 3710⟩, 195832677633443936, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_48_flag endpoint_8_48_sources 7 195832677633443936 195832677633443936 rfl endpoint_8_48_base endpoint_8_48_p7) (by decide)⟩
private def endpoint_8_49_flag : Flag := ⟨8, 49, 3681⟩
private def endpoint_8_49_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_49_base : receiptBase endpoint_8_49_flag endpoint_8_49_sources = some 197814136998794973 := by decide +kernel
private theorem endpoint_8_49_w0 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 2 197814136998794973 = some 197814136998794973 := by decide +kernel
private theorem endpoint_8_49_w2 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 2 2 197814136998794973 = some 197814136998794973 := by decide +kernel
private theorem endpoint_8_49_p4 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 4 197814136998794973 = some 197814136998794973 :=
  join_receipt_window endpoint_8_49_flag endpoint_8_49_sources 0 2 2 197814136998794973 197814136998794973 197814136998794973 endpoint_8_49_w0 endpoint_8_49_w2
private theorem endpoint_8_49_w4 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 4 2 197814136998794973 = some 197814136998794973 := by decide +kernel
private theorem endpoint_8_49_p6 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 6 197814136998794973 = some 197814136998794973 :=
  join_receipt_window endpoint_8_49_flag endpoint_8_49_sources 0 4 2 197814136998794973 197814136998794973 197814136998794973 endpoint_8_49_p4 endpoint_8_49_w4
private theorem endpoint_8_49_w6 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 6 1 197814136998794973 = some 197814136998794973 := by decide +kernel
private theorem endpoint_8_49_p7 : receiptWindow endpoint_8_49_flag endpoint_8_49_sources 0 7 197814136998794973 = some 197814136998794973 :=
  join_receipt_window endpoint_8_49_flag endpoint_8_49_sources 0 6 1 197814136998794973 197814136998794973 197814136998794973 endpoint_8_49_p6 endpoint_8_49_w6
def endpoint_8_49 : CertifiedEndpoint :=
  ⟨⟨8, 49, 3681⟩, 197814136998794973, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_49_flag endpoint_8_49_sources 7 197814136998794973 197814136998794973 rfl endpoint_8_49_base endpoint_8_49_p7) (by decide)⟩
private def endpoint_8_50_flag : Flag := ⟨8, 50, 3652⟩
private def endpoint_8_50_sources : Sources := ⟨contact09, contact09, contact10⟩
private theorem endpoint_8_50_base : receiptBase endpoint_8_50_flag endpoint_8_50_sources = some 199740562298995910 := by decide +kernel
private theorem endpoint_8_50_w0 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 2 199740562298995910 = some 199740562298995910 := by decide +kernel
private theorem endpoint_8_50_w2 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 2 2 199740562298995910 = some 199740562298995910 := by decide +kernel
private theorem endpoint_8_50_p4 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 4 199740562298995910 = some 199740562298995910 :=
  join_receipt_window endpoint_8_50_flag endpoint_8_50_sources 0 2 2 199740562298995910 199740562298995910 199740562298995910 endpoint_8_50_w0 endpoint_8_50_w2
private theorem endpoint_8_50_w4 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 4 2 199740562298995910 = some 199740562298995910 := by decide +kernel
private theorem endpoint_8_50_p6 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 6 199740562298995910 = some 199740562298995910 :=
  join_receipt_window endpoint_8_50_flag endpoint_8_50_sources 0 4 2 199740562298995910 199740562298995910 199740562298995910 endpoint_8_50_p4 endpoint_8_50_w4
private theorem endpoint_8_50_w6 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 6 1 199740562298995910 = some 199740562298995910 := by decide +kernel
private theorem endpoint_8_50_p7 : receiptWindow endpoint_8_50_flag endpoint_8_50_sources 0 7 199740562298995910 = some 199740562298995910 :=
  join_receipt_window endpoint_8_50_flag endpoint_8_50_sources 0 6 1 199740562298995910 199740562298995910 199740562298995910 endpoint_8_50_p6 endpoint_8_50_w6
def endpoint_8_50 : CertifiedEndpoint :=
  ⟨⟨8, 50, 3652⟩, 199740562298995910, .terminal ⟨contact09, contact09, contact10⟩ (finish_receipt_window endpoint_8_50_flag endpoint_8_50_sources 7 199740562298995910 199740562298995910 rfl endpoint_8_50_base endpoint_8_50_p7) (by decide)⟩
private def endpoint_8_51_flag : Flag := ⟨8, 51, 3622⟩
private def endpoint_8_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_51_base : receiptBase endpoint_8_51_flag endpoint_8_51_sources = some 202647757666630660 := by decide +kernel
private theorem endpoint_8_51_w0 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 2 202647757666630660 = some 202647757666630660 := by decide +kernel
private theorem endpoint_8_51_w2 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 2 2 202647757666630660 = some 202647757666630660 := by decide +kernel
private theorem endpoint_8_51_p4 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 4 202647757666630660 = some 202647757666630660 :=
  join_receipt_window endpoint_8_51_flag endpoint_8_51_sources 0 2 2 202647757666630660 202647757666630660 202647757666630660 endpoint_8_51_w0 endpoint_8_51_w2
private theorem endpoint_8_51_w4 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 4 2 202647757666630660 = some 202647757666630660 := by decide +kernel
private theorem endpoint_8_51_p6 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 6 202647757666630660 = some 202647757666630660 :=
  join_receipt_window endpoint_8_51_flag endpoint_8_51_sources 0 4 2 202647757666630660 202647757666630660 202647757666630660 endpoint_8_51_p4 endpoint_8_51_w4
private theorem endpoint_8_51_w6 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 6 1 202647757666630660 = some 202647757666630660 := by decide +kernel
private theorem endpoint_8_51_p7 : receiptWindow endpoint_8_51_flag endpoint_8_51_sources 0 7 202647757666630660 = some 202647757666630660 :=
  join_receipt_window endpoint_8_51_flag endpoint_8_51_sources 0 6 1 202647757666630660 202647757666630660 202647757666630660 endpoint_8_51_p6 endpoint_8_51_w6
def endpoint_8_51 : CertifiedEndpoint :=
  ⟨⟨8, 51, 3622⟩, 202647757666630660, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_51_flag endpoint_8_51_sources 7 202647757666630660 202647757666630660 rfl endpoint_8_51_base endpoint_8_51_p7) (by decide)⟩
private def endpoint_8_52_flag : Flag := ⟨8, 52, 3591⟩
private def endpoint_8_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_52_base : receiptBase endpoint_8_52_flag endpoint_8_52_sources = some 204352781448023932 := by decide +kernel
private theorem endpoint_8_52_w0 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 2 204352781448023932 = some 204352781448023932 := by decide +kernel
private theorem endpoint_8_52_w2 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 2 2 204352781448023932 = some 204352781448023932 := by decide +kernel
private theorem endpoint_8_52_p4 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 4 204352781448023932 = some 204352781448023932 :=
  join_receipt_window endpoint_8_52_flag endpoint_8_52_sources 0 2 2 204352781448023932 204352781448023932 204352781448023932 endpoint_8_52_w0 endpoint_8_52_w2
private theorem endpoint_8_52_w4 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 4 2 204352781448023932 = some 204352781448023932 := by decide +kernel
private theorem endpoint_8_52_p6 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 6 204352781448023932 = some 204352781448023932 :=
  join_receipt_window endpoint_8_52_flag endpoint_8_52_sources 0 4 2 204352781448023932 204352781448023932 204352781448023932 endpoint_8_52_p4 endpoint_8_52_w4
private theorem endpoint_8_52_w6 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 6 1 204352781448023932 = some 204352781448023932 := by decide +kernel
private theorem endpoint_8_52_p7 : receiptWindow endpoint_8_52_flag endpoint_8_52_sources 0 7 204352781448023932 = some 204352781448023932 :=
  join_receipt_window endpoint_8_52_flag endpoint_8_52_sources 0 6 1 204352781448023932 204352781448023932 204352781448023932 endpoint_8_52_p6 endpoint_8_52_w6
def endpoint_8_52 : CertifiedEndpoint :=
  ⟨⟨8, 52, 3591⟩, 204352781448023932, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_52_flag endpoint_8_52_sources 7 204352781448023932 204352781448023932 rfl endpoint_8_52_base endpoint_8_52_p7) (by decide)⟩
private def endpoint_8_53_flag : Flag := ⟨8, 53, 3560⟩
private def endpoint_8_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_53_base : receiptBase endpoint_8_53_flag endpoint_8_53_sources = some 205998472899581656 := by decide +kernel
private theorem endpoint_8_53_w0 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 2 205998472899581656 = some 205998472899581656 := by decide +kernel
private theorem endpoint_8_53_w2 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 2 2 205998472899581656 = some 205998472899581656 := by decide +kernel
private theorem endpoint_8_53_p4 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 4 205998472899581656 = some 205998472899581656 :=
  join_receipt_window endpoint_8_53_flag endpoint_8_53_sources 0 2 2 205998472899581656 205998472899581656 205998472899581656 endpoint_8_53_w0 endpoint_8_53_w2
private theorem endpoint_8_53_w4 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 4 2 205998472899581656 = some 205998472899581656 := by decide +kernel
private theorem endpoint_8_53_p6 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 6 205998472899581656 = some 205998472899581656 :=
  join_receipt_window endpoint_8_53_flag endpoint_8_53_sources 0 4 2 205998472899581656 205998472899581656 205998472899581656 endpoint_8_53_p4 endpoint_8_53_w4
private theorem endpoint_8_53_w6 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 6 1 205998472899581656 = some 205998472899581656 := by decide +kernel
private theorem endpoint_8_53_p7 : receiptWindow endpoint_8_53_flag endpoint_8_53_sources 0 7 205998472899581656 = some 205998472899581656 :=
  join_receipt_window endpoint_8_53_flag endpoint_8_53_sources 0 6 1 205998472899581656 205998472899581656 205998472899581656 endpoint_8_53_p6 endpoint_8_53_w6
def endpoint_8_53 : CertifiedEndpoint :=
  ⟨⟨8, 53, 3560⟩, 205998472899581656, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_53_flag endpoint_8_53_sources 7 205998472899581656 205998472899581656 rfl endpoint_8_53_base endpoint_8_53_p7) (by decide)⟩
private def endpoint_8_54_flag : Flag := ⟨8, 54, 3528⟩
private def endpoint_8_54_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_54_base : receiptBase endpoint_8_54_flag endpoint_8_54_sources = some 207526773944391792 := by decide +kernel
private theorem endpoint_8_54_w0 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 2 207526773944391792 = some 207526773944391792 := by decide +kernel
private theorem endpoint_8_54_w2 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 2 2 207526773944391792 = some 207526773944391792 := by decide +kernel
private theorem endpoint_8_54_p4 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 4 207526773944391792 = some 207526773944391792 :=
  join_receipt_window endpoint_8_54_flag endpoint_8_54_sources 0 2 2 207526773944391792 207526773944391792 207526773944391792 endpoint_8_54_w0 endpoint_8_54_w2
private theorem endpoint_8_54_w4 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 4 2 207526773944391792 = some 207526773944391792 := by decide +kernel
private theorem endpoint_8_54_p6 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 6 207526773944391792 = some 207526773944391792 :=
  join_receipt_window endpoint_8_54_flag endpoint_8_54_sources 0 4 2 207526773944391792 207526773944391792 207526773944391792 endpoint_8_54_p4 endpoint_8_54_w4
private theorem endpoint_8_54_w6 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 6 1 207526773944391792 = some 207526773944391792 := by decide +kernel
private theorem endpoint_8_54_p7 : receiptWindow endpoint_8_54_flag endpoint_8_54_sources 0 7 207526773944391792 = some 207526773944391792 :=
  join_receipt_window endpoint_8_54_flag endpoint_8_54_sources 0 6 1 207526773944391792 207526773944391792 207526773944391792 endpoint_8_54_p6 endpoint_8_54_w6
def endpoint_8_54 : CertifiedEndpoint :=
  ⟨⟨8, 54, 3528⟩, 207526773944391792, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_54_flag endpoint_8_54_sources 7 207526773944391792 207526773944391792 rfl endpoint_8_54_base endpoint_8_54_p7) (by decide)⟩
private def endpoint_8_55_flag : Flag := ⟨8, 55, 3496⟩
private def endpoint_8_55_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_8_55_base : receiptBase endpoint_8_55_flag endpoint_8_55_sources = some 208993859093339856 := by decide +kernel
private theorem endpoint_8_55_w0 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 2 208993859093339856 = some 208993859093339856 := by decide +kernel
private theorem endpoint_8_55_w2 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 2 2 208993859093339856 = some 208993859093339856 := by decide +kernel
private theorem endpoint_8_55_p4 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 4 208993859093339856 = some 208993859093339856 :=
  join_receipt_window endpoint_8_55_flag endpoint_8_55_sources 0 2 2 208993859093339856 208993859093339856 208993859093339856 endpoint_8_55_w0 endpoint_8_55_w2
private theorem endpoint_8_55_w4 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 4 2 208993859093339856 = some 208993859093339856 := by decide +kernel
private theorem endpoint_8_55_p6 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 6 208993859093339856 = some 208993859093339856 :=
  join_receipt_window endpoint_8_55_flag endpoint_8_55_sources 0 4 2 208993859093339856 208993859093339856 208993859093339856 endpoint_8_55_p4 endpoint_8_55_w4
private theorem endpoint_8_55_w6 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 6 1 208993859093339856 = some 208993859093339856 := by decide +kernel
private theorem endpoint_8_55_p7 : receiptWindow endpoint_8_55_flag endpoint_8_55_sources 0 7 208993859093339856 = some 208993859093339856 :=
  join_receipt_window endpoint_8_55_flag endpoint_8_55_sources 0 6 1 208993859093339856 208993859093339856 208993859093339856 endpoint_8_55_p6 endpoint_8_55_w6
def endpoint_8_55 : CertifiedEndpoint :=
  ⟨⟨8, 55, 3496⟩, 208993859093339856, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_8_55_flag endpoint_8_55_sources 7 208993859093339856 208993859093339856 rfl endpoint_8_55_base endpoint_8_55_p7) (by decide)⟩
private def endpoint_8_56_flag : Flag := ⟨8, 56, 3462⟩
private def endpoint_8_56_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_56_base : receiptBase endpoint_8_56_flag endpoint_8_56_sources = some 211015557534959699 := by decide +kernel
private theorem endpoint_8_56_w0 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 2 211015557534959699 = some 211015557534959699 := by decide +kernel
private theorem endpoint_8_56_w2 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 2 2 211015557534959699 = some 211015557534959699 := by decide +kernel
private theorem endpoint_8_56_p4 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 4 211015557534959699 = some 211015557534959699 :=
  join_receipt_window endpoint_8_56_flag endpoint_8_56_sources 0 2 2 211015557534959699 211015557534959699 211015557534959699 endpoint_8_56_w0 endpoint_8_56_w2
private theorem endpoint_8_56_w4 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 4 2 211015557534959699 = some 211015557534959699 := by decide +kernel
private theorem endpoint_8_56_p6 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 6 211015557534959699 = some 211015557534959699 :=
  join_receipt_window endpoint_8_56_flag endpoint_8_56_sources 0 4 2 211015557534959699 211015557534959699 211015557534959699 endpoint_8_56_p4 endpoint_8_56_w4
private theorem endpoint_8_56_w6 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 6 1 211015557534959699 = some 211015557534959699 := by decide +kernel
private theorem endpoint_8_56_p7 : receiptWindow endpoint_8_56_flag endpoint_8_56_sources 0 7 211015557534959699 = some 211015557534959699 :=
  join_receipt_window endpoint_8_56_flag endpoint_8_56_sources 0 6 1 211015557534959699 211015557534959699 211015557534959699 endpoint_8_56_p6 endpoint_8_56_w6
def endpoint_8_56 : CertifiedEndpoint :=
  ⟨⟨8, 56, 3462⟩, 211015557534959699, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_56_flag endpoint_8_56_sources 7 211015557534959699 211015557534959699 rfl endpoint_8_56_base endpoint_8_56_p7) (by decide)⟩
private def endpoint_8_57_flag : Flag := ⟨8, 57, 3427⟩
private def endpoint_8_57_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_57_base : receiptBase endpoint_8_57_flag endpoint_8_57_sources = some 212167899816909485 := by decide +kernel
private theorem endpoint_8_57_w0 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 2 212167899816909485 = some 212167899816909485 := by decide +kernel
private theorem endpoint_8_57_w2 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 2 2 212167899816909485 = some 212167899816909485 := by decide +kernel
private theorem endpoint_8_57_p4 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 4 212167899816909485 = some 212167899816909485 :=
  join_receipt_window endpoint_8_57_flag endpoint_8_57_sources 0 2 2 212167899816909485 212167899816909485 212167899816909485 endpoint_8_57_w0 endpoint_8_57_w2
private theorem endpoint_8_57_w4 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 4 2 212167899816909485 = some 212167899816909485 := by decide +kernel
private theorem endpoint_8_57_p6 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 6 212167899816909485 = some 212167899816909485 :=
  join_receipt_window endpoint_8_57_flag endpoint_8_57_sources 0 4 2 212167899816909485 212167899816909485 212167899816909485 endpoint_8_57_p4 endpoint_8_57_w4
private theorem endpoint_8_57_w6 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 6 1 212167899816909485 = some 212167899816909485 := by decide +kernel
private theorem endpoint_8_57_p7 : receiptWindow endpoint_8_57_flag endpoint_8_57_sources 0 7 212167899816909485 = some 212167899816909485 :=
  join_receipt_window endpoint_8_57_flag endpoint_8_57_sources 0 6 1 212167899816909485 212167899816909485 212167899816909485 endpoint_8_57_p6 endpoint_8_57_w6
def endpoint_8_57 : CertifiedEndpoint :=
  ⟨⟨8, 57, 3427⟩, 212167899816909485, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_57_flag endpoint_8_57_sources 7 212167899816909485 212167899816909485 rfl endpoint_8_57_base endpoint_8_57_p7) (by decide)⟩
private def endpoint_8_58_flag : Flag := ⟨8, 58, 3392⟩
private def endpoint_8_58_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_58_base : receiptBase endpoint_8_58_flag endpoint_8_58_sources = some 213253375504917622 := by decide +kernel
private theorem endpoint_8_58_w0 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 2 213253375504917622 = some 213253375504917622 := by decide +kernel
private theorem endpoint_8_58_w2 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 2 2 213253375504917622 = some 213253375504917622 := by decide +kernel
private theorem endpoint_8_58_p4 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 4 213253375504917622 = some 213253375504917622 :=
  join_receipt_window endpoint_8_58_flag endpoint_8_58_sources 0 2 2 213253375504917622 213253375504917622 213253375504917622 endpoint_8_58_w0 endpoint_8_58_w2
private theorem endpoint_8_58_w4 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 4 2 213253375504917622 = some 213253375504917622 := by decide +kernel
private theorem endpoint_8_58_p6 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 6 213253375504917622 = some 213253375504917622 :=
  join_receipt_window endpoint_8_58_flag endpoint_8_58_sources 0 4 2 213253375504917622 213253375504917622 213253375504917622 endpoint_8_58_p4 endpoint_8_58_w4
private theorem endpoint_8_58_w6 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 6 1 213253375504917622 = some 213253375504917622 := by decide +kernel
private theorem endpoint_8_58_p7 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 7 213253375504917622 = some 213253375504917622 :=
  join_receipt_window endpoint_8_58_flag endpoint_8_58_sources 0 6 1 213253375504917622 213253375504917622 213253375504917622 endpoint_8_58_p6 endpoint_8_58_w6
def endpoint_8_58 : CertifiedEndpoint :=
  ⟨⟨8, 58, 3392⟩, 213253375504917622, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_58_flag endpoint_8_58_sources 7 213253375504917622 213253375504917622 rfl endpoint_8_58_base endpoint_8_58_p7) (by decide)⟩
private def endpoint_8_59_flag : Flag := ⟨8, 59, 3355⟩
private def endpoint_8_59_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_59_base : receiptBase endpoint_8_59_flag endpoint_8_59_sources = some 214146018584591397 := by decide +kernel
private theorem endpoint_8_59_w0 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 2 214146018584591397 = some 214146018584591397 := by decide +kernel
private theorem endpoint_8_59_w2 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 2 2 214146018584591397 = some 214146018584591397 := by decide +kernel
private theorem endpoint_8_59_p4 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 4 214146018584591397 = some 214146018584591397 :=
  join_receipt_window endpoint_8_59_flag endpoint_8_59_sources 0 2 2 214146018584591397 214146018584591397 214146018584591397 endpoint_8_59_w0 endpoint_8_59_w2
private theorem endpoint_8_59_w4 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 4 2 214146018584591397 = some 214146018584591397 := by decide +kernel
private theorem endpoint_8_59_p6 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 6 214146018584591397 = some 214146018584591397 :=
  join_receipt_window endpoint_8_59_flag endpoint_8_59_sources 0 4 2 214146018584591397 214146018584591397 214146018584591397 endpoint_8_59_p4 endpoint_8_59_w4
private theorem endpoint_8_59_w6 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 6 1 214146018584591397 = some 214146018584591397 := by decide +kernel
private theorem endpoint_8_59_p7 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 7 214146018584591397 = some 214146018584591397 :=
  join_receipt_window endpoint_8_59_flag endpoint_8_59_sources 0 6 1 214146018584591397 214146018584591397 214146018584591397 endpoint_8_59_p6 endpoint_8_59_w6
def endpoint_8_59 : CertifiedEndpoint :=
  ⟨⟨8, 59, 3355⟩, 214146018584591397, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_59_flag endpoint_8_59_sources 7 214146018584591397 214146018584591397 rfl endpoint_8_59_base endpoint_8_59_p7) (by decide)⟩
private def endpoint_8_60_flag : Flag := ⟨8, 60, 3318⟩
private def endpoint_8_60_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_60_base : receiptBase endpoint_8_60_flag endpoint_8_60_sources = some 214968027938270471 := by decide +kernel
private theorem endpoint_8_60_w0 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 2 214968027938270471 = some 214968027938270471 := by decide +kernel
private theorem endpoint_8_60_w2 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 2 2 214968027938270471 = some 214968027938270471 := by decide +kernel
private theorem endpoint_8_60_p4 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 4 214968027938270471 = some 214968027938270471 :=
  join_receipt_window endpoint_8_60_flag endpoint_8_60_sources 0 2 2 214968027938270471 214968027938270471 214968027938270471 endpoint_8_60_w0 endpoint_8_60_w2
private theorem endpoint_8_60_w4 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 4 2 214968027938270471 = some 214968027938270471 := by decide +kernel
private theorem endpoint_8_60_p6 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 6 214968027938270471 = some 214968027938270471 :=
  join_receipt_window endpoint_8_60_flag endpoint_8_60_sources 0 4 2 214968027938270471 214968027938270471 214968027938270471 endpoint_8_60_p4 endpoint_8_60_w4
private theorem endpoint_8_60_w6 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 6 1 214968027938270471 = some 214968027938270471 := by decide +kernel
private theorem endpoint_8_60_p7 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 7 214968027938270471 = some 214968027938270471 :=
  join_receipt_window endpoint_8_60_flag endpoint_8_60_sources 0 6 1 214968027938270471 214968027938270471 214968027938270471 endpoint_8_60_p6 endpoint_8_60_w6
def endpoint_8_60 : CertifiedEndpoint :=
  ⟨⟨8, 60, 3318⟩, 214968027938270471, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_60_flag endpoint_8_60_sources 7 214968027938270471 214968027938270471 rfl endpoint_8_60_base endpoint_8_60_p7) (by decide)⟩
private def endpoint_8_61_flag : Flag := ⟨8, 61, 3278⟩
private def endpoint_8_61_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_61_base : receiptBase endpoint_8_61_flag endpoint_8_61_sources = some 217679340796837560 := by decide +kernel
private theorem endpoint_8_61_w0 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 2 217679340796837560 = some 217679340796837560 := by decide +kernel
private theorem endpoint_8_61_w2 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 2 2 217679340796837560 = some 217679340796837560 := by decide +kernel
private theorem endpoint_8_61_p4 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 4 217679340796837560 = some 217679340796837560 :=
  join_receipt_window endpoint_8_61_flag endpoint_8_61_sources 0 2 2 217679340796837560 217679340796837560 217679340796837560 endpoint_8_61_w0 endpoint_8_61_w2
private theorem endpoint_8_61_w4 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 4 2 217679340796837560 = some 217679340796837560 := by decide +kernel
private theorem endpoint_8_61_p6 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 6 217679340796837560 = some 217679340796837560 :=
  join_receipt_window endpoint_8_61_flag endpoint_8_61_sources 0 4 2 217679340796837560 217679340796837560 217679340796837560 endpoint_8_61_p4 endpoint_8_61_w4
private theorem endpoint_8_61_w6 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 6 1 217679340796837560 = some 217679340796837560 := by decide +kernel
private theorem endpoint_8_61_p7 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 7 217679340796837560 = some 217679340796837560 :=
  join_receipt_window endpoint_8_61_flag endpoint_8_61_sources 0 6 1 217679340796837560 217679340796837560 217679340796837560 endpoint_8_61_p6 endpoint_8_61_w6
def endpoint_8_61 : CertifiedEndpoint :=
  ⟨⟨8, 61, 3278⟩, 217679340796837560, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_61_flag endpoint_8_61_sources 7 217679340796837560 217679340796837560 rfl endpoint_8_61_base endpoint_8_61_p7) (by decide)⟩
private def endpoint_8_62_flag : Flag := ⟨8, 62, 3238⟩
private def endpoint_8_62_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_62_base : receiptBase endpoint_8_62_flag endpoint_8_62_sources = some 218144508049079244 := by decide +kernel
private theorem endpoint_8_62_w0 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 2 218144508049079244 = some 218144508049079244 := by decide +kernel
private theorem endpoint_8_62_w2 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 2 2 218144508049079244 = some 218144508049079244 := by decide +kernel
private theorem endpoint_8_62_p4 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 4 218144508049079244 = some 218144508049079244 :=
  join_receipt_window endpoint_8_62_flag endpoint_8_62_sources 0 2 2 218144508049079244 218144508049079244 218144508049079244 endpoint_8_62_w0 endpoint_8_62_w2
private theorem endpoint_8_62_w4 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 4 2 218144508049079244 = some 218144508049079244 := by decide +kernel
private theorem endpoint_8_62_p6 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 6 218144508049079244 = some 218144508049079244 :=
  join_receipt_window endpoint_8_62_flag endpoint_8_62_sources 0 4 2 218144508049079244 218144508049079244 218144508049079244 endpoint_8_62_p4 endpoint_8_62_w4
private theorem endpoint_8_62_w6 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 6 1 218144508049079244 = some 218144508049079244 := by decide +kernel
private theorem endpoint_8_62_p7 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 7 218144508049079244 = some 218144508049079244 :=
  join_receipt_window endpoint_8_62_flag endpoint_8_62_sources 0 6 1 218144508049079244 218144508049079244 218144508049079244 endpoint_8_62_p6 endpoint_8_62_w6
def endpoint_8_62 : CertifiedEndpoint :=
  ⟨⟨8, 62, 3238⟩, 218144508049079244, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_62_flag endpoint_8_62_sources 7 218144508049079244 218144508049079244 rfl endpoint_8_62_base endpoint_8_62_p7) (by decide)⟩
private def endpoint_8_63_flag : Flag := ⟨8, 63, 3196⟩
private def endpoint_8_63_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_63_base : receiptBase endpoint_8_63_flag endpoint_8_63_sources = some 218397442890987488 := by decide +kernel
private theorem endpoint_8_63_w0 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 2 218397442890987488 = some 218397442890987488 := by decide +kernel
private theorem endpoint_8_63_w2 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 2 2 218397442890987488 = some 218397442890987488 := by decide +kernel
private theorem endpoint_8_63_p4 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 4 218397442890987488 = some 218397442890987488 :=
  join_receipt_window endpoint_8_63_flag endpoint_8_63_sources 0 2 2 218397442890987488 218397442890987488 218397442890987488 endpoint_8_63_w0 endpoint_8_63_w2
private theorem endpoint_8_63_w4 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 4 2 218397442890987488 = some 218397442890987488 := by decide +kernel
private theorem endpoint_8_63_p6 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 6 218397442890987488 = some 218397442890987488 :=
  join_receipt_window endpoint_8_63_flag endpoint_8_63_sources 0 4 2 218397442890987488 218397442890987488 218397442890987488 endpoint_8_63_p4 endpoint_8_63_w4
private theorem endpoint_8_63_w6 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 6 1 218397442890987488 = some 218397442890987488 := by decide +kernel
private theorem endpoint_8_63_p7 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 7 218397442890987488 = some 218397442890987488 :=
  join_receipt_window endpoint_8_63_flag endpoint_8_63_sources 0 6 1 218397442890987488 218397442890987488 218397442890987488 endpoint_8_63_p6 endpoint_8_63_w6
def endpoint_8_63 : CertifiedEndpoint :=
  ⟨⟨8, 63, 3196⟩, 218397442890987488, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_63_flag endpoint_8_63_sources 7 218397442890987488 218397442890987488 rfl endpoint_8_63_base endpoint_8_63_p7) (by decide)⟩
private def endpoint_8_64_flag : Flag := ⟨8, 64, 3152⟩
private def endpoint_8_64_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_64_base : receiptBase endpoint_8_64_flag endpoint_8_64_sources = some 218432440652007312 := by decide +kernel
private theorem endpoint_8_64_w0 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 2 218432440652007312 = some 218432440652007312 := by decide +kernel
private theorem endpoint_8_64_w2 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 2 2 218432440652007312 = some 218432440652007312 := by decide +kernel
private theorem endpoint_8_64_p4 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 4 218432440652007312 = some 218432440652007312 :=
  join_receipt_window endpoint_8_64_flag endpoint_8_64_sources 0 2 2 218432440652007312 218432440652007312 218432440652007312 endpoint_8_64_w0 endpoint_8_64_w2
private theorem endpoint_8_64_w4 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 4 2 218432440652007312 = some 218432440652007312 := by decide +kernel
private theorem endpoint_8_64_p6 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 6 218432440652007312 = some 218432440652007312 :=
  join_receipt_window endpoint_8_64_flag endpoint_8_64_sources 0 4 2 218432440652007312 218432440652007312 218432440652007312 endpoint_8_64_p4 endpoint_8_64_w4
private theorem endpoint_8_64_w6 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 6 1 218432440652007312 = some 218432440652007312 := by decide +kernel
private theorem endpoint_8_64_p7 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 7 218432440652007312 = some 218432440652007312 :=
  join_receipt_window endpoint_8_64_flag endpoint_8_64_sources 0 6 1 218432440652007312 218432440652007312 218432440652007312 endpoint_8_64_p6 endpoint_8_64_w6
def endpoint_8_64 : CertifiedEndpoint :=
  ⟨⟨8, 64, 3152⟩, 218432440652007312, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_64_flag endpoint_8_64_sources 7 218432440652007312 218432440652007312 rfl endpoint_8_64_base endpoint_8_64_p7) (by decide)⟩
private def endpoint_8_65_flag : Flag := ⟨8, 65, 3105⟩
private def endpoint_8_65_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_8_65_base : receiptBase endpoint_8_65_flag endpoint_8_65_sources = some 219572259656453635 := by decide +kernel
private theorem endpoint_8_65_w0 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 2 219572259656453635 = some 219572259656453635 := by decide +kernel
private theorem endpoint_8_65_w2 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 2 2 219572259656453635 = some 219572259656453635 := by decide +kernel
private theorem endpoint_8_65_p4 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 4 219572259656453635 = some 219572259656453635 :=
  join_receipt_window endpoint_8_65_flag endpoint_8_65_sources 0 2 2 219572259656453635 219572259656453635 219572259656453635 endpoint_8_65_w0 endpoint_8_65_w2
private theorem endpoint_8_65_w4 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 4 2 219572259656453635 = some 219572259656453635 := by decide +kernel
private theorem endpoint_8_65_p6 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 6 219572259656453635 = some 219572259656453635 :=
  join_receipt_window endpoint_8_65_flag endpoint_8_65_sources 0 4 2 219572259656453635 219572259656453635 219572259656453635 endpoint_8_65_p4 endpoint_8_65_w4
private theorem endpoint_8_65_w6 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 6 1 219572259656453635 = some 219572259656453635 := by decide +kernel
private theorem endpoint_8_65_p7 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 7 219572259656453635 = some 219572259656453635 :=
  join_receipt_window endpoint_8_65_flag endpoint_8_65_sources 0 6 1 219572259656453635 219572259656453635 219572259656453635 endpoint_8_65_p6 endpoint_8_65_w6
def endpoint_8_65 : CertifiedEndpoint :=
  ⟨⟨8, 65, 3105⟩, 219572259656453635, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_8_65_flag endpoint_8_65_sources 7 219572259656453635 219572259656453635 rfl endpoint_8_65_base endpoint_8_65_p7) (by decide)⟩
private def endpoint_8_66_flag : Flag := ⟨8, 66, 3057⟩
private def endpoint_8_66_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_8_66_base : receiptBase endpoint_8_66_flag endpoint_8_66_sources = some 219152822550054544 := by decide +kernel
private theorem endpoint_8_66_w0 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 2 219152822550054544 = some 219152822550054544 := by decide +kernel
private theorem endpoint_8_66_w2 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 2 2 219152822550054544 = some 219152822550054544 := by decide +kernel
private theorem endpoint_8_66_p4 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 4 219152822550054544 = some 219152822550054544 :=
  join_receipt_window endpoint_8_66_flag endpoint_8_66_sources 0 2 2 219152822550054544 219152822550054544 219152822550054544 endpoint_8_66_w0 endpoint_8_66_w2
private theorem endpoint_8_66_w4 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 4 2 219152822550054544 = some 219152822550054544 := by decide +kernel
private theorem endpoint_8_66_p6 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 6 219152822550054544 = some 219152822550054544 :=
  join_receipt_window endpoint_8_66_flag endpoint_8_66_sources 0 4 2 219152822550054544 219152822550054544 219152822550054544 endpoint_8_66_p4 endpoint_8_66_w4
private theorem endpoint_8_66_w6 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 6 1 219152822550054544 = some 219152822550054544 := by decide +kernel
private theorem endpoint_8_66_p7 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 7 219152822550054544 = some 219152822550054544 :=
  join_receipt_window endpoint_8_66_flag endpoint_8_66_sources 0 6 1 219152822550054544 219152822550054544 219152822550054544 endpoint_8_66_p6 endpoint_8_66_w6
def endpoint_8_66 : CertifiedEndpoint :=
  ⟨⟨8, 66, 3057⟩, 219152822550054544, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_8_66_flag endpoint_8_66_sources 7 219152822550054544 219152822550054544 rfl endpoint_8_66_base endpoint_8_66_p7) (by decide)⟩
private def endpoint_8_67_flag : Flag := ⟨8, 67, 3006⟩
private def endpoint_8_67_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_8_67_base : receiptBase endpoint_8_67_flag endpoint_8_67_sources = some 218424465175794723 := by decide +kernel
private theorem endpoint_8_67_w0 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 2 218424465175794723 = some 218424465175794723 := by decide +kernel
private theorem endpoint_8_67_w2 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 2 2 218424465175794723 = some 218424465175794723 := by decide +kernel
private theorem endpoint_8_67_p4 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 4 218424465175794723 = some 218424465175794723 :=
  join_receipt_window endpoint_8_67_flag endpoint_8_67_sources 0 2 2 218424465175794723 218424465175794723 218424465175794723 endpoint_8_67_w0 endpoint_8_67_w2
private theorem endpoint_8_67_w4 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 4 2 218424465175794723 = some 218424465175794723 := by decide +kernel
private theorem endpoint_8_67_p6 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 6 218424465175794723 = some 218424465175794723 :=
  join_receipt_window endpoint_8_67_flag endpoint_8_67_sources 0 4 2 218424465175794723 218424465175794723 218424465175794723 endpoint_8_67_p4 endpoint_8_67_w4
private theorem endpoint_8_67_w6 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 6 1 218424465175794723 = some 218424465175794723 := by decide +kernel
private theorem endpoint_8_67_p7 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 7 218424465175794723 = some 218424465175794723 :=
  join_receipt_window endpoint_8_67_flag endpoint_8_67_sources 0 6 1 218424465175794723 218424465175794723 218424465175794723 endpoint_8_67_p6 endpoint_8_67_w6
def endpoint_8_67 : CertifiedEndpoint :=
  ⟨⟨8, 67, 3006⟩, 218424465175794723, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_8_67_flag endpoint_8_67_sources 7 218424465175794723 218424465175794723 rfl endpoint_8_67_base endpoint_8_67_p7) (by decide)⟩
private def endpoint_8_68_flag : Flag := ⟨8, 68, 2952⟩
private def endpoint_8_68_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_8_68_base : receiptBase endpoint_8_68_flag endpoint_8_68_sources = some 218816676076271703 := by decide +kernel
private theorem endpoint_8_68_w0 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 2 218816676076271703 = some 218816676076271703 := by decide +kernel
private theorem endpoint_8_68_w2 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 2 2 218816676076271703 = some 218816676076271703 := by decide +kernel
private theorem endpoint_8_68_p4 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 4 218816676076271703 = some 218816676076271703 :=
  join_receipt_window endpoint_8_68_flag endpoint_8_68_sources 0 2 2 218816676076271703 218816676076271703 218816676076271703 endpoint_8_68_w0 endpoint_8_68_w2
private theorem endpoint_8_68_w4 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 4 2 218816676076271703 = some 218816676076271703 := by decide +kernel
private theorem endpoint_8_68_p6 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 6 218816676076271703 = some 218816676076271703 :=
  join_receipt_window endpoint_8_68_flag endpoint_8_68_sources 0 4 2 218816676076271703 218816676076271703 218816676076271703 endpoint_8_68_p4 endpoint_8_68_w4
private theorem endpoint_8_68_w6 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 6 1 218816676076271703 = some 218816676076271703 := by decide +kernel
private theorem endpoint_8_68_p7 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 7 218816676076271703 = some 218816676076271703 :=
  join_receipt_window endpoint_8_68_flag endpoint_8_68_sources 0 6 1 218816676076271703 218816676076271703 218816676076271703 endpoint_8_68_p6 endpoint_8_68_w6
def endpoint_8_68 : CertifiedEndpoint :=
  ⟨⟨8, 68, 2952⟩, 218816676076271703, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_8_68_flag endpoint_8_68_sources 7 218816676076271703 218816676076271703 rfl endpoint_8_68_base endpoint_8_68_p7) (by decide)⟩
private def endpoint_8_69_flag : Flag := ⟨8, 69, 2896⟩
private def endpoint_8_69_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_8_69_base : receiptBase endpoint_8_69_flag endpoint_8_69_sources = some 217511690128876560 := by decide +kernel
private theorem endpoint_8_69_w0 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 2 217511690128876560 = some 217511690128876560 := by decide +kernel
private theorem endpoint_8_69_w2 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 2 2 217511690128876560 = some 217511690128876560 := by decide +kernel
private theorem endpoint_8_69_p4 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 4 217511690128876560 = some 217511690128876560 :=
  join_receipt_window endpoint_8_69_flag endpoint_8_69_sources 0 2 2 217511690128876560 217511690128876560 217511690128876560 endpoint_8_69_w0 endpoint_8_69_w2
private theorem endpoint_8_69_w4 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 4 2 217511690128876560 = some 217511690128876560 := by decide +kernel
private theorem endpoint_8_69_p6 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 6 217511690128876560 = some 217511690128876560 :=
  join_receipt_window endpoint_8_69_flag endpoint_8_69_sources 0 4 2 217511690128876560 217511690128876560 217511690128876560 endpoint_8_69_p4 endpoint_8_69_w4
private theorem endpoint_8_69_w6 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 6 1 217511690128876560 = some 217511690128876560 := by decide +kernel
private theorem endpoint_8_69_p7 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 7 217511690128876560 = some 217511690128876560 :=
  join_receipt_window endpoint_8_69_flag endpoint_8_69_sources 0 6 1 217511690128876560 217511690128876560 217511690128876560 endpoint_8_69_p6 endpoint_8_69_w6
def endpoint_8_69 : CertifiedEndpoint :=
  ⟨⟨8, 69, 2896⟩, 217511690128876560, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_8_69_flag endpoint_8_69_sources 7 217511690128876560 217511690128876560 rfl endpoint_8_69_base endpoint_8_69_p7) (by decide)⟩
private def endpoint_8_70_flag : Flag := ⟨8, 70, 2837⟩
private def endpoint_8_70_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_8_70_base : receiptBase endpoint_8_70_flag endpoint_8_70_sources = some 217337212426286881 := by decide +kernel
private theorem endpoint_8_70_w0 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 2 217337212426286881 = some 217337212426286881 := by decide +kernel
private theorem endpoint_8_70_w2 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 2 2 217337212426286881 = some 217337212426286881 := by decide +kernel
private theorem endpoint_8_70_p4 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 4 217337212426286881 = some 217337212426286881 :=
  join_receipt_window endpoint_8_70_flag endpoint_8_70_sources 0 2 2 217337212426286881 217337212426286881 217337212426286881 endpoint_8_70_w0 endpoint_8_70_w2
private theorem endpoint_8_70_w4 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 4 2 217337212426286881 = some 217337212426286881 := by decide +kernel
private theorem endpoint_8_70_p6 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 6 217337212426286881 = some 217337212426286881 :=
  join_receipt_window endpoint_8_70_flag endpoint_8_70_sources 0 4 2 217337212426286881 217337212426286881 217337212426286881 endpoint_8_70_p4 endpoint_8_70_w4
private theorem endpoint_8_70_w6 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 6 1 217337212426286881 = some 217337212426286881 := by decide +kernel
private theorem endpoint_8_70_p7 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 7 217337212426286881 = some 217337212426286881 :=
  join_receipt_window endpoint_8_70_flag endpoint_8_70_sources 0 6 1 217337212426286881 217337212426286881 217337212426286881 endpoint_8_70_p6 endpoint_8_70_w6
def endpoint_8_70 : CertifiedEndpoint :=
  ⟨⟨8, 70, 2837⟩, 217337212426286881, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_8_70_flag endpoint_8_70_sources 7 217337212426286881 217337212426286881 rfl endpoint_8_70_base endpoint_8_70_p7) (by decide)⟩
private def endpoint_8_71_flag : Flag := ⟨8, 71, 2776⟩
private def endpoint_8_71_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_8_71_base : receiptBase endpoint_8_71_flag endpoint_8_71_sources = some 216904368379277621 := by decide +kernel
private theorem endpoint_8_71_w0 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 2 216904368379277621 = some 216904368379277621 := by decide +kernel
private theorem endpoint_8_71_w2 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 2 2 216904368379277621 = some 216904368379277621 := by decide +kernel
private theorem endpoint_8_71_p4 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 4 216904368379277621 = some 216904368379277621 :=
  join_receipt_window endpoint_8_71_flag endpoint_8_71_sources 0 2 2 216904368379277621 216904368379277621 216904368379277621 endpoint_8_71_w0 endpoint_8_71_w2
private theorem endpoint_8_71_w4 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 4 2 216904368379277621 = some 216904368379277621 := by decide +kernel
private theorem endpoint_8_71_p6 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 6 216904368379277621 = some 216904368379277621 :=
  join_receipt_window endpoint_8_71_flag endpoint_8_71_sources 0 4 2 216904368379277621 216904368379277621 216904368379277621 endpoint_8_71_p4 endpoint_8_71_w4
private theorem endpoint_8_71_w6 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 6 1 216904368379277621 = some 216904368379277621 := by decide +kernel
private theorem endpoint_8_71_p7 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 7 216904368379277621 = some 216904368379277621 :=
  join_receipt_window endpoint_8_71_flag endpoint_8_71_sources 0 6 1 216904368379277621 216904368379277621 216904368379277621 endpoint_8_71_p6 endpoint_8_71_w6
def endpoint_8_71 : CertifiedEndpoint :=
  ⟨⟨8, 71, 2776⟩, 216904368379277621, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_8_71_flag endpoint_8_71_sources 7 216904368379277621 216904368379277621 rfl endpoint_8_71_base endpoint_8_71_p7) (by decide)⟩
private def endpoint_8_72_flag : Flag := ⟨8, 72, 2712⟩
private def endpoint_8_72_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_8_72_base : receiptBase endpoint_8_72_flag endpoint_8_72_sources = some 215992650533599504 := by decide +kernel
private theorem endpoint_8_72_w0 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 2 215992650533599504 = some 215992650533599504 := by decide +kernel
private theorem endpoint_8_72_w2 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 2 2 215992650533599504 = some 215992650533599504 := by decide +kernel
private theorem endpoint_8_72_p4 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 4 215992650533599504 = some 215992650533599504 :=
  join_receipt_window endpoint_8_72_flag endpoint_8_72_sources 0 2 2 215992650533599504 215992650533599504 215992650533599504 endpoint_8_72_w0 endpoint_8_72_w2
private theorem endpoint_8_72_w4 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 4 2 215992650533599504 = some 215992650533599504 := by decide +kernel
private theorem endpoint_8_72_p6 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 6 215992650533599504 = some 215992650533599504 :=
  join_receipt_window endpoint_8_72_flag endpoint_8_72_sources 0 4 2 215992650533599504 215992650533599504 215992650533599504 endpoint_8_72_p4 endpoint_8_72_w4
private theorem endpoint_8_72_w6 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 6 1 215992650533599504 = some 215992650533599504 := by decide +kernel
private theorem endpoint_8_72_p7 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 7 215992650533599504 = some 215992650533599504 :=
  join_receipt_window endpoint_8_72_flag endpoint_8_72_sources 0 6 1 215992650533599504 215992650533599504 215992650533599504 endpoint_8_72_p6 endpoint_8_72_w6
def endpoint_8_72 : CertifiedEndpoint :=
  ⟨⟨8, 72, 2712⟩, 215992650533599504, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_8_72_flag endpoint_8_72_sources 7 215992650533599504 215992650533599504 rfl endpoint_8_72_base endpoint_8_72_p7) (by decide)⟩
private def endpoint_8_73_flag : Flag := ⟨8, 73, 2645⟩
private def endpoint_8_73_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_8_73_base : receiptBase endpoint_8_73_flag endpoint_8_73_sources = some 213322772834980745 := by decide +kernel
private theorem endpoint_8_73_w0 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 2 213322772834980745 = some 213322772834980745 := by decide +kernel
private theorem endpoint_8_73_w2 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 2 2 213322772834980745 = some 213322772834980745 := by decide +kernel
private theorem endpoint_8_73_p4 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 4 213322772834980745 = some 213322772834980745 :=
  join_receipt_window endpoint_8_73_flag endpoint_8_73_sources 0 2 2 213322772834980745 213322772834980745 213322772834980745 endpoint_8_73_w0 endpoint_8_73_w2
private theorem endpoint_8_73_w4 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 4 2 213322772834980745 = some 213322772834980745 := by decide +kernel
private theorem endpoint_8_73_p6 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 6 213322772834980745 = some 213322772834980745 :=
  join_receipt_window endpoint_8_73_flag endpoint_8_73_sources 0 4 2 213322772834980745 213322772834980745 213322772834980745 endpoint_8_73_p4 endpoint_8_73_w4
private theorem endpoint_8_73_w6 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 6 1 213322772834980745 = some 213322772834980745 := by decide +kernel
private theorem endpoint_8_73_p7 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 7 213322772834980745 = some 213322772834980745 :=
  join_receipt_window endpoint_8_73_flag endpoint_8_73_sources 0 6 1 213322772834980745 213322772834980745 213322772834980745 endpoint_8_73_p6 endpoint_8_73_w6
def endpoint_8_73 : CertifiedEndpoint :=
  ⟨⟨8, 73, 2645⟩, 213322772834980745, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_8_73_flag endpoint_8_73_sources 7 213322772834980745 213322772834980745 rfl endpoint_8_73_base endpoint_8_73_p7) (by decide)⟩
private def endpoint_8_74_flag : Flag := ⟨8, 74, 2575⟩
private def endpoint_8_74_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_8_74_base : receiptBase endpoint_8_74_flag endpoint_8_74_sources = some 210275399241404854 := by decide +kernel
private theorem endpoint_8_74_w0 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 2 210275399241404854 = some 210275399241404854 := by decide +kernel
private theorem endpoint_8_74_w2 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 2 2 210275399241404854 = some 210275399241404854 := by decide +kernel
private theorem endpoint_8_74_p4 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 4 210275399241404854 = some 210275399241404854 :=
  join_receipt_window endpoint_8_74_flag endpoint_8_74_sources 0 2 2 210275399241404854 210275399241404854 210275399241404854 endpoint_8_74_w0 endpoint_8_74_w2
private theorem endpoint_8_74_w4 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 4 2 210275399241404854 = some 210275399241404854 := by decide +kernel
private theorem endpoint_8_74_p6 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 6 210275399241404854 = some 210275399241404854 :=
  join_receipt_window endpoint_8_74_flag endpoint_8_74_sources 0 4 2 210275399241404854 210275399241404854 210275399241404854 endpoint_8_74_p4 endpoint_8_74_w4
private theorem endpoint_8_74_w6 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 6 1 210275399241404854 = some 210275399241404854 := by decide +kernel
private theorem endpoint_8_74_p7 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 7 210275399241404854 = some 210275399241404854 :=
  join_receipt_window endpoint_8_74_flag endpoint_8_74_sources 0 6 1 210275399241404854 210275399241404854 210275399241404854 endpoint_8_74_p6 endpoint_8_74_w6
def endpoint_8_74 : CertifiedEndpoint :=
  ⟨⟨8, 74, 2575⟩, 210275399241404854, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_8_74_flag endpoint_8_74_sources 7 210275399241404854 210275399241404854 rfl endpoint_8_74_base endpoint_8_74_p7) (by decide)⟩

def endpointBlock05 : List CertifiedEndpoint := [
  endpoint_7_40, endpoint_7_41, endpoint_7_42, endpoint_7_43, endpoint_7_44, endpoint_7_45, endpoint_7_46,
  endpoint_7_47, endpoint_7_48, endpoint_7_49, endpoint_7_50, endpoint_7_51, endpoint_7_52, endpoint_7_53,
  endpoint_7_54, endpoint_7_55, endpoint_7_56, endpoint_7_57, endpoint_7_58, endpoint_7_59, endpoint_7_60,
  endpoint_7_61, endpoint_7_62, endpoint_7_63, endpoint_7_64, endpoint_7_65, endpoint_7_66, endpoint_7_67,
  endpoint_7_68, endpoint_7_69, endpoint_7_70, endpoint_7_71, endpoint_7_72, endpoint_7_73, endpoint_7_74,
  endpoint_7_75, endpoint_7_76, endpoint_7_77, endpoint_7_78, endpoint_7_79, endpoint_7_80, endpoint_7_81,
  endpoint_7_82, endpoint_7_83, endpoint_7_84, endpoint_7_85, endpoint_7_86, endpoint_7_87, endpoint_7_88,
  endpoint_7_89, endpoint_7_90, endpoint_7_91, endpoint_7_92, endpoint_7_93, endpoint_7_94, endpoint_7_95,
  endpoint_7_96, endpoint_7_97, endpoint_7_98, endpoint_7_99, endpoint_8_8, endpoint_8_9, endpoint_8_10,
  endpoint_8_11, endpoint_8_12, endpoint_8_13, endpoint_8_14, endpoint_8_15, endpoint_8_16, endpoint_8_17,
  endpoint_8_18, endpoint_8_19, endpoint_8_20, endpoint_8_21, endpoint_8_22, endpoint_8_23, endpoint_8_24,
  endpoint_8_25, endpoint_8_26, endpoint_8_27, endpoint_8_28, endpoint_8_29, endpoint_8_30, endpoint_8_31,
  endpoint_8_32, endpoint_8_33, endpoint_8_34, endpoint_8_35, endpoint_8_36, endpoint_8_37, endpoint_8_38,
  endpoint_8_39, endpoint_8_40, endpoint_8_41, endpoint_8_42, endpoint_8_43, endpoint_8_44, endpoint_8_45,
  endpoint_8_46, endpoint_8_47, endpoint_8_48, endpoint_8_49, endpoint_8_50, endpoint_8_51, endpoint_8_52,
  endpoint_8_53, endpoint_8_54, endpoint_8_55, endpoint_8_56, endpoint_8_57, endpoint_8_58, endpoint_8_59,
  endpoint_8_60, endpoint_8_61, endpoint_8_62, endpoint_8_63, endpoint_8_64, endpoint_8_65, endpoint_8_66,
  endpoint_8_67, endpoint_8_68, endpoint_8_69, endpoint_8_70, endpoint_8_71, endpoint_8_72, endpoint_8_73,
  endpoint_8_74
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
