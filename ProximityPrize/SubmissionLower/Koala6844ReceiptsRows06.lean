import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_8_75_flag : Flag := ⟨8, 75, 2503⟩
private def endpoint_8_75_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_8_75_base : receiptBase endpoint_8_75_flag endpoint_8_75_sources = some 211002544580185592 := by decide +kernel
private theorem endpoint_8_75_w0 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 2 211002544580185592 = some 211002544580185592 := by decide +kernel
private theorem endpoint_8_75_w2 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 2 2 211002544580185592 = some 211002544580185592 := by decide +kernel
private theorem endpoint_8_75_p4 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 4 211002544580185592 = some 211002544580185592 :=
  join_receipt_window endpoint_8_75_flag endpoint_8_75_sources 0 2 2 211002544580185592 211002544580185592 211002544580185592 endpoint_8_75_w0 endpoint_8_75_w2
private theorem endpoint_8_75_w4 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 4 2 211002544580185592 = some 211002544580185592 := by decide +kernel
private theorem endpoint_8_75_p6 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 6 211002544580185592 = some 211002544580185592 :=
  join_receipt_window endpoint_8_75_flag endpoint_8_75_sources 0 4 2 211002544580185592 211002544580185592 211002544580185592 endpoint_8_75_p4 endpoint_8_75_w4
private theorem endpoint_8_75_w6 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 6 1 211002544580185592 = some 211002544580185592 := by decide +kernel
private theorem endpoint_8_75_p7 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 7 211002544580185592 = some 211002544580185592 :=
  join_receipt_window endpoint_8_75_flag endpoint_8_75_sources 0 6 1 211002544580185592 211002544580185592 211002544580185592 endpoint_8_75_p6 endpoint_8_75_w6
def endpoint_8_75 : CertifiedEndpoint :=
  ⟨⟨8, 75, 2503⟩, 211002544580185592, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_8_75_flag endpoint_8_75_sources 7 211002544580185592 211002544580185592 rfl endpoint_8_75_base endpoint_8_75_p7) (by decide)⟩
private def endpoint_8_76_flag : Flag := ⟨8, 76, 2428⟩
private def endpoint_8_76_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_8_76_base : receiptBase endpoint_8_76_flag endpoint_8_76_sources = some 207225783093765741 := by decide +kernel
private theorem endpoint_8_76_w0 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 2 207225783093765741 = some 207225783093765741 := by decide +kernel
private theorem endpoint_8_76_w2 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 2 2 207225783093765741 = some 207225783093765741 := by decide +kernel
private theorem endpoint_8_76_p4 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 4 207225783093765741 = some 207225783093765741 :=
  join_receipt_window endpoint_8_76_flag endpoint_8_76_sources 0 2 2 207225783093765741 207225783093765741 207225783093765741 endpoint_8_76_w0 endpoint_8_76_w2
private theorem endpoint_8_76_w4 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 4 2 207225783093765741 = some 207225783093765741 := by decide +kernel
private theorem endpoint_8_76_p6 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 6 207225783093765741 = some 207225783093765741 :=
  join_receipt_window endpoint_8_76_flag endpoint_8_76_sources 0 4 2 207225783093765741 207225783093765741 207225783093765741 endpoint_8_76_p4 endpoint_8_76_w4
private theorem endpoint_8_76_w6 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 6 1 207225783093765741 = some 207225783093765741 := by decide +kernel
private theorem endpoint_8_76_p7 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 7 207225783093765741 = some 207225783093765741 :=
  join_receipt_window endpoint_8_76_flag endpoint_8_76_sources 0 6 1 207225783093765741 207225783093765741 207225783093765741 endpoint_8_76_p6 endpoint_8_76_w6
def endpoint_8_76 : CertifiedEndpoint :=
  ⟨⟨8, 76, 2428⟩, 207225783093765741, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_8_76_flag endpoint_8_76_sources 7 207225783093765741 207225783093765741 rfl endpoint_8_76_base endpoint_8_76_p7) (by decide)⟩
private def endpoint_8_77_flag : Flag := ⟨8, 77, 2351⟩
private def endpoint_8_77_sources : Sources := ⟨contact11, contact11, contact13⟩
private theorem endpoint_8_77_base : receiptBase endpoint_8_77_flag endpoint_8_77_sources = some 203171169660847402 := by decide +kernel
private theorem endpoint_8_77_w0 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 2 203171169660847402 = some 203171169660847402 := by decide +kernel
private theorem endpoint_8_77_w2 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 2 2 203171169660847402 = some 203171169660847402 := by decide +kernel
private theorem endpoint_8_77_p4 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 4 203171169660847402 = some 203171169660847402 :=
  join_receipt_window endpoint_8_77_flag endpoint_8_77_sources 0 2 2 203171169660847402 203171169660847402 203171169660847402 endpoint_8_77_w0 endpoint_8_77_w2
private theorem endpoint_8_77_w4 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 4 2 203171169660847402 = some 203171169660847402 := by decide +kernel
private theorem endpoint_8_77_p6 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 6 203171169660847402 = some 203171169660847402 :=
  join_receipt_window endpoint_8_77_flag endpoint_8_77_sources 0 4 2 203171169660847402 203171169660847402 203171169660847402 endpoint_8_77_p4 endpoint_8_77_w4
private theorem endpoint_8_77_w6 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 6 1 203171169660847402 = some 203171169660847402 := by decide +kernel
private theorem endpoint_8_77_p7 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 7 203171169660847402 = some 203171169660847402 :=
  join_receipt_window endpoint_8_77_flag endpoint_8_77_sources 0 6 1 203171169660847402 203171169660847402 203171169660847402 endpoint_8_77_p6 endpoint_8_77_w6
def endpoint_8_77 : CertifiedEndpoint :=
  ⟨⟨8, 77, 2351⟩, 203171169660847402, .terminal ⟨contact11, contact11, contact13⟩ (finish_receipt_window endpoint_8_77_flag endpoint_8_77_sources 7 203171169660847402 203171169660847402 rfl endpoint_8_77_base endpoint_8_77_p7) (by decide)⟩
private def endpoint_8_78_flag : Flag := ⟨8, 78, 2271⟩
private def endpoint_8_78_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_8_78_base : receiptBase endpoint_8_78_flag endpoint_8_78_sources = some 200608440997605618 := by decide +kernel
private theorem endpoint_8_78_w0 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 2 200608440997605618 = some 200608440997605618 := by decide +kernel
private theorem endpoint_8_78_w2 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 2 2 200608440997605618 = some 200608440997605618 := by decide +kernel
private theorem endpoint_8_78_p4 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 4 200608440997605618 = some 200608440997605618 :=
  join_receipt_window endpoint_8_78_flag endpoint_8_78_sources 0 2 2 200608440997605618 200608440997605618 200608440997605618 endpoint_8_78_w0 endpoint_8_78_w2
private theorem endpoint_8_78_w4 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 4 2 200608440997605618 = some 200608440997605618 := by decide +kernel
private theorem endpoint_8_78_p6 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 6 200608440997605618 = some 200608440997605618 :=
  join_receipt_window endpoint_8_78_flag endpoint_8_78_sources 0 4 2 200608440997605618 200608440997605618 200608440997605618 endpoint_8_78_p4 endpoint_8_78_w4
private theorem endpoint_8_78_w6 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 6 1 200608440997605618 = some 200608440997605618 := by decide +kernel
private theorem endpoint_8_78_p7 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 7 200608440997605618 = some 200608440997605618 :=
  join_receipt_window endpoint_8_78_flag endpoint_8_78_sources 0 6 1 200608440997605618 200608440997605618 200608440997605618 endpoint_8_78_p6 endpoint_8_78_w6
def endpoint_8_78 : CertifiedEndpoint :=
  ⟨⟨8, 78, 2271⟩, 200608440997605618, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_8_78_flag endpoint_8_78_sources 7 200608440997605618 200608440997605618 rfl endpoint_8_78_base endpoint_8_78_p7) (by decide)⟩
private def endpoint_8_79_flag : Flag := ⟨8, 79, 2188⟩
private def endpoint_8_79_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_8_79_base : receiptBase endpoint_8_79_flag endpoint_8_79_sources = some 195560525916755699 := by decide +kernel
private theorem endpoint_8_79_w0 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 2 195560525916755699 = some 195560525916755699 := by decide +kernel
private theorem endpoint_8_79_w2 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 2 2 195560525916755699 = some 195560525916755699 := by decide +kernel
private theorem endpoint_8_79_p4 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 4 195560525916755699 = some 195560525916755699 :=
  join_receipt_window endpoint_8_79_flag endpoint_8_79_sources 0 2 2 195560525916755699 195560525916755699 195560525916755699 endpoint_8_79_w0 endpoint_8_79_w2
private theorem endpoint_8_79_w4 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 4 2 195560525916755699 = some 195560525916755699 := by decide +kernel
private theorem endpoint_8_79_p6 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 6 195560525916755699 = some 195560525916755699 :=
  join_receipt_window endpoint_8_79_flag endpoint_8_79_sources 0 4 2 195560525916755699 195560525916755699 195560525916755699 endpoint_8_79_p4 endpoint_8_79_w4
private theorem endpoint_8_79_w6 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 6 1 195560525916755699 = some 195560525916755699 := by decide +kernel
private theorem endpoint_8_79_p7 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 7 195560525916755699 = some 195560525916755699 :=
  join_receipt_window endpoint_8_79_flag endpoint_8_79_sources 0 6 1 195560525916755699 195560525916755699 195560525916755699 endpoint_8_79_p6 endpoint_8_79_w6
def endpoint_8_79 : CertifiedEndpoint :=
  ⟨⟨8, 79, 2188⟩, 195560525916755699, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_8_79_flag endpoint_8_79_sources 7 195560525916755699 195560525916755699 rfl endpoint_8_79_base endpoint_8_79_p7) (by decide)⟩
private def endpoint_8_80_flag : Flag := ⟨8, 80, 2102⟩
private def endpoint_8_80_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_8_80_base : receiptBase endpoint_8_80_flag endpoint_8_80_sources = some 190074900841876871 := by decide +kernel
private theorem endpoint_8_80_w0 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 2 190074900841876871 = some 190074900841876871 := by decide +kernel
private theorem endpoint_8_80_w2 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 2 2 190074900841876871 = some 190074900841876871 := by decide +kernel
private theorem endpoint_8_80_p4 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 4 190074900841876871 = some 190074900841876871 :=
  join_receipt_window endpoint_8_80_flag endpoint_8_80_sources 0 2 2 190074900841876871 190074900841876871 190074900841876871 endpoint_8_80_w0 endpoint_8_80_w2
private theorem endpoint_8_80_w4 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 4 2 190074900841876871 = some 190074900841876871 := by decide +kernel
private theorem endpoint_8_80_p6 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 6 190074900841876871 = some 190074900841876871 :=
  join_receipt_window endpoint_8_80_flag endpoint_8_80_sources 0 4 2 190074900841876871 190074900841876871 190074900841876871 endpoint_8_80_p4 endpoint_8_80_w4
private theorem endpoint_8_80_w6 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 6 1 190074900841876871 = some 190074900841876871 := by decide +kernel
private theorem endpoint_8_80_p7 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 7 190074900841876871 = some 190074900841876871 :=
  join_receipt_window endpoint_8_80_flag endpoint_8_80_sources 0 6 1 190074900841876871 190074900841876871 190074900841876871 endpoint_8_80_p6 endpoint_8_80_w6
def endpoint_8_80 : CertifiedEndpoint :=
  ⟨⟨8, 80, 2102⟩, 190074900841876871, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_8_80_flag endpoint_8_80_sources 7 190074900841876871 190074900841876871 rfl endpoint_8_80_base endpoint_8_80_p7) (by decide)⟩
private def endpoint_8_81_flag : Flag := ⟨8, 81, 2014⟩
private def endpoint_8_81_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_8_81_base : receiptBase endpoint_8_81_flag endpoint_8_81_sources = some 186258210154456185 := by decide +kernel
private theorem endpoint_8_81_w0 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 2 186258210154456185 = some 186258210154456185 := by decide +kernel
private theorem endpoint_8_81_w2 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 2 2 186258210154456185 = some 186258210154456185 := by decide +kernel
private theorem endpoint_8_81_p4 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 4 186258210154456185 = some 186258210154456185 :=
  join_receipt_window endpoint_8_81_flag endpoint_8_81_sources 0 2 2 186258210154456185 186258210154456185 186258210154456185 endpoint_8_81_w0 endpoint_8_81_w2
private theorem endpoint_8_81_w4 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 4 2 186258210154456185 = some 186258210154456185 := by decide +kernel
private theorem endpoint_8_81_p6 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 6 186258210154456185 = some 186258210154456185 :=
  join_receipt_window endpoint_8_81_flag endpoint_8_81_sources 0 4 2 186258210154456185 186258210154456185 186258210154456185 endpoint_8_81_p4 endpoint_8_81_w4
private theorem endpoint_8_81_w6 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 6 1 186258210154456185 = some 186258210154456185 := by decide +kernel
private theorem endpoint_8_81_p7 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 7 186258210154456185 = some 186258210154456185 :=
  join_receipt_window endpoint_8_81_flag endpoint_8_81_sources 0 6 1 186258210154456185 186258210154456185 186258210154456185 endpoint_8_81_p6 endpoint_8_81_w6
def endpoint_8_81 : CertifiedEndpoint :=
  ⟨⟨8, 81, 2014⟩, 186258210154456185, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_8_81_flag endpoint_8_81_sources 7 186258210154456185 186258210154456185 rfl endpoint_8_81_base endpoint_8_81_p7) (by decide)⟩
private def endpoint_8_82_flag : Flag := ⟨8, 82, 1923⟩
private def endpoint_8_82_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_8_82_base : receiptBase endpoint_8_82_flag endpoint_8_82_sources = some 181883597836462386 := by decide +kernel
private theorem endpoint_8_82_w0 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 2 181883597836462386 = some 181883597836462386 := by decide +kernel
private theorem endpoint_8_82_w2 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 2 2 181883597836462386 = some 181883597836462386 := by decide +kernel
private theorem endpoint_8_82_p4 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 4 181883597836462386 = some 181883597836462386 :=
  join_receipt_window endpoint_8_82_flag endpoint_8_82_sources 0 2 2 181883597836462386 181883597836462386 181883597836462386 endpoint_8_82_w0 endpoint_8_82_w2
private theorem endpoint_8_82_w4 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 4 2 181883597836462386 = some 181883597836462386 := by decide +kernel
private theorem endpoint_8_82_p6 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 6 181883597836462386 = some 181883597836462386 :=
  join_receipt_window endpoint_8_82_flag endpoint_8_82_sources 0 4 2 181883597836462386 181883597836462386 181883597836462386 endpoint_8_82_p4 endpoint_8_82_w4
private theorem endpoint_8_82_w6 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 6 1 181883597836462386 = some 181883597836462386 := by decide +kernel
private theorem endpoint_8_82_p7 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 7 181883597836462386 = some 181883597836462386 :=
  join_receipt_window endpoint_8_82_flag endpoint_8_82_sources 0 6 1 181883597836462386 181883597836462386 181883597836462386 endpoint_8_82_p6 endpoint_8_82_w6
def endpoint_8_82 : CertifiedEndpoint :=
  ⟨⟨8, 82, 1923⟩, 181883597836462386, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_8_82_flag endpoint_8_82_sources 7 181883597836462386 181883597836462386 rfl endpoint_8_82_base endpoint_8_82_p7) (by decide)⟩
private def endpoint_8_83_flag : Flag := ⟨8, 83, 1830⟩
private def endpoint_8_83_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_8_83_base : receiptBase endpoint_8_83_flag endpoint_8_83_sources = some 175028382489124618 := by decide +kernel
private theorem endpoint_8_83_w0 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 0 2 175028382489124618 = some 175028382489124618 := by decide +kernel
private theorem endpoint_8_83_w2 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 2 2 175028382489124618 = some 175028382489124618 := by decide +kernel
private theorem endpoint_8_83_p4 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 0 4 175028382489124618 = some 175028382489124618 :=
  join_receipt_window endpoint_8_83_flag endpoint_8_83_sources 0 2 2 175028382489124618 175028382489124618 175028382489124618 endpoint_8_83_w0 endpoint_8_83_w2
private theorem endpoint_8_83_w4 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 4 2 175028382489124618 = some 175028382489124618 := by decide +kernel
private theorem endpoint_8_83_p6 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 0 6 175028382489124618 = some 175028382489124618 :=
  join_receipt_window endpoint_8_83_flag endpoint_8_83_sources 0 4 2 175028382489124618 175028382489124618 175028382489124618 endpoint_8_83_p4 endpoint_8_83_w4
private theorem endpoint_8_83_w6 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 6 1 175028382489124618 = some 175028382489124618 := by decide +kernel
private theorem endpoint_8_83_p7 : receiptWindow endpoint_8_83_flag endpoint_8_83_sources 0 7 175028382489124618 = some 175028382489124618 :=
  join_receipt_window endpoint_8_83_flag endpoint_8_83_sources 0 6 1 175028382489124618 175028382489124618 175028382489124618 endpoint_8_83_p6 endpoint_8_83_w6
def endpoint_8_83 : CertifiedEndpoint :=
  ⟨⟨8, 83, 1830⟩, 175028382489124618, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_8_83_flag endpoint_8_83_sources 7 175028382489124618 175028382489124618 rfl endpoint_8_83_base endpoint_8_83_p7) (by decide)⟩
private def endpoint_8_84_flag : Flag := ⟨8, 84, 1733⟩
private def endpoint_8_84_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_8_84_base : receiptBase endpoint_8_84_flag endpoint_8_84_sources = some 167593313592254159 := by decide +kernel
private theorem endpoint_8_84_w0 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 0 2 167593313592254159 = some 167593313592254159 := by decide +kernel
private theorem endpoint_8_84_w2 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 2 2 167593313592254159 = some 167593313592254159 := by decide +kernel
private theorem endpoint_8_84_p4 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 0 4 167593313592254159 = some 167593313592254159 :=
  join_receipt_window endpoint_8_84_flag endpoint_8_84_sources 0 2 2 167593313592254159 167593313592254159 167593313592254159 endpoint_8_84_w0 endpoint_8_84_w2
private theorem endpoint_8_84_w4 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 4 2 167593313592254159 = some 167593313592254159 := by decide +kernel
private theorem endpoint_8_84_p6 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 0 6 167593313592254159 = some 167593313592254159 :=
  join_receipt_window endpoint_8_84_flag endpoint_8_84_sources 0 4 2 167593313592254159 167593313592254159 167593313592254159 endpoint_8_84_p4 endpoint_8_84_w4
private theorem endpoint_8_84_w6 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 6 1 167593313592254159 = some 167593313592254159 := by decide +kernel
private theorem endpoint_8_84_p7 : receiptWindow endpoint_8_84_flag endpoint_8_84_sources 0 7 167593313592254159 = some 167593313592254159 :=
  join_receipt_window endpoint_8_84_flag endpoint_8_84_sources 0 6 1 167593313592254159 167593313592254159 167593313592254159 endpoint_8_84_p6 endpoint_8_84_w6
def endpoint_8_84 : CertifiedEndpoint :=
  ⟨⟨8, 84, 1733⟩, 167593313592254159, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_8_84_flag endpoint_8_84_sources 7 167593313592254159 167593313592254159 rfl endpoint_8_84_base endpoint_8_84_p7) (by decide)⟩
def endpoint_8_85 : CertifiedEndpoint :=
  ⟨⟨8, 85, 1634⟩, 248387607751941271, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_86 : CertifiedEndpoint :=
  ⟨⟨8, 86, 1532⟩, 235254302379357464, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_87 : CertifiedEndpoint :=
  ⟨⟨8, 87, 1428⟩, 221402671265407777, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_88 : CertifiedEndpoint :=
  ⟨⟨8, 88, 1321⟩, 206658952791752483, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_89 : CertifiedEndpoint :=
  ⟨⟨8, 89, 1211⟩, 191005674589060808, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_90 : CertifiedEndpoint :=
  ⟨⟨8, 90, 1098⟩, 174425364288001978, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_91 : CertifiedEndpoint :=
  ⟨⟨8, 91, 983⟩, 157068487014474688, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_92 : CertifiedEndpoint :=
  ⟨⟨8, 92, 865⟩, 138753515652658867, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_93 : CertifiedEndpoint :=
  ⟨⟨8, 93, 744⟩, 119462977833223741, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_94 : CertifiedEndpoint :=
  ⟨⟨8, 94, 621⟩, 99353162805178263, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_95 : CertifiedEndpoint :=
  ⟨⟨8, 95, 495⟩, 78236719329592104, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_96 : CertifiedEndpoint :=
  ⟨⟨8, 96, 366⟩, 56096175037134490, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_97 : CertifiedEndpoint :=
  ⟨⟨8, 97, 234⟩, 32914057558474647, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_98 : CertifiedEndpoint :=
  ⟨⟨8, 98, 100⟩, 8854421640101872, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_9 : CertifiedEndpoint :=
  ⟨⟨9, 9, 4487⟩, 52760679822749100, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_10 : CertifiedEndpoint :=
  ⟨⟨9, 10, 4468⟩, 55714679102138156, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_11 : CertifiedEndpoint :=
  ⟨⟨9, 11, 4450⟩, 58654788120238285, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_12 : CertifiedEndpoint :=
  ⟨⟨9, 12, 4432⟩, 68138159940501556, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_13 : CertifiedEndpoint :=
  ⟨⟨9, 13, 4413⟩, 77522564604259514, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_14 : CertifiedEndpoint :=
  ⟨⟨9, 14, 4395⟩, 86841005522072435, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_15 : CertifiedEndpoint :=
  ⟨⟨9, 15, 4376⟩, 96056081125981367, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_16 : CertifiedEndpoint :=
  ⟨⟨9, 16, 4357⟩, 105185392660616117, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_17 : CertifiedEndpoint :=
  ⟨⟨9, 17, 4338⟩, 114228940125976685, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_18 : CertifiedEndpoint :=
  ⟨⟨9, 18, 4318⟩, 123158126883936574, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_19 : CertifiedEndpoint :=
  ⟨⟨9, 19, 4299⟩, 132027947132049440, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_20 : CertifiedEndpoint :=
  ⟨⟨9, 20, 4279⟩, 140779008515362951, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_21 : CertifiedEndpoint :=
  ⟨⟨9, 21, 4259⟩, 149439907672003604, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_22 : CertifiedEndpoint :=
  ⟨⟨9, 22, 4239⟩, 158010644601971399, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_23 : CertifiedEndpoint :=
  ⟨⟨9, 23, 4218⟩, 166451627273643149, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_24 : CertifiedEndpoint :=
  ⟨⟨9, 24, 4198⟩, 174839840671565890, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_25 : CertifiedEndpoint :=
  ⟨⟨9, 25, 4177⟩, 183093901653793910, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_26 : CertifiedEndpoint :=
  ⟨⟨9, 26, 4156⟩, 191253402251950396, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_27 : CertifiedEndpoint :=
  ⟨⟨9, 27, 4135⟩, 199318342466035348, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_28 : CertifiedEndpoint :=
  ⟨⟨9, 28, 4113⟩, 207238134870928889, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_29 : CertifiedEndpoint :=
  ⟨⟨9, 29, 4092⟩, 215111755238171435, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_30 : CertifiedEndpoint :=
  ⟨⟨9, 30, 4070⟩, 222835829638823894, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_31 : CertifiedEndpoint :=
  ⟨⟨9, 31, 4048⟩, 230460945498006143, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_32 : CertifiedEndpoint :=
  ⟨⟨9, 32, 4025⟩, 237927719075800953, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_33 : CertifiedEndpoint :=
  ⟨⟨9, 33, 4002⟩, 245291135954726877, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_34 : CertifiedEndpoint :=
  ⟨⟨9, 34, 3979⟩, 252551196134783915, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_35 : CertifiedEndpoint :=
  ⟨⟨9, 35, 3956⟩, 259707899615972067, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_9_36_flag : Flag := ⟨9, 36, 3932⟩
private def endpoint_9_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_36_base : receiptBase endpoint_9_36_flag endpoint_9_36_sources = some 175635917339723971 := by decide +kernel
private theorem endpoint_9_36_w0 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 2 175635917339723971 = some 175635917339723971 := by decide +kernel
private theorem endpoint_9_36_w2 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 2 2 175635917339723971 = some 175635917339723971 := by decide +kernel
private theorem endpoint_9_36_p4 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 4 175635917339723971 = some 175635917339723971 :=
  join_receipt_window endpoint_9_36_flag endpoint_9_36_sources 0 2 2 175635917339723971 175635917339723971 175635917339723971 endpoint_9_36_w0 endpoint_9_36_w2
private theorem endpoint_9_36_w4 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 4 2 175635917339723971 = some 175635917339723971 := by decide +kernel
private theorem endpoint_9_36_p6 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 6 175635917339723971 = some 175635917339723971 :=
  join_receipt_window endpoint_9_36_flag endpoint_9_36_sources 0 4 2 175635917339723971 175635917339723971 175635917339723971 endpoint_9_36_p4 endpoint_9_36_w4
private theorem endpoint_9_36_w6 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 6 2 175635917339723971 = some 175635917339723971 := by decide +kernel
private theorem endpoint_9_36_p8 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 8 175635917339723971 = some 175635917339723971 :=
  join_receipt_window endpoint_9_36_flag endpoint_9_36_sources 0 6 2 175635917339723971 175635917339723971 175635917339723971 endpoint_9_36_p6 endpoint_9_36_w6
def endpoint_9_36 : CertifiedEndpoint :=
  ⟨⟨9, 36, 3932⟩, 175635917339723971, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_36_flag endpoint_9_36_sources 8 175635917339723971 175635917339723971 rfl endpoint_9_36_base endpoint_9_36_p8) (by decide)⟩
private def endpoint_9_37_flag : Flag := ⟨9, 37, 3908⟩
private def endpoint_9_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_37_base : receiptBase endpoint_9_37_flag endpoint_9_37_sources = some 178609418018348985 := by decide +kernel
private theorem endpoint_9_37_w0 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 2 178609418018348985 = some 178609418018348985 := by decide +kernel
private theorem endpoint_9_37_w2 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 2 2 178609418018348985 = some 178609418018348985 := by decide +kernel
private theorem endpoint_9_37_p4 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 4 178609418018348985 = some 178609418018348985 :=
  join_receipt_window endpoint_9_37_flag endpoint_9_37_sources 0 2 2 178609418018348985 178609418018348985 178609418018348985 endpoint_9_37_w0 endpoint_9_37_w2
private theorem endpoint_9_37_w4 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 4 2 178609418018348985 = some 178609418018348985 := by decide +kernel
private theorem endpoint_9_37_p6 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 6 178609418018348985 = some 178609418018348985 :=
  join_receipt_window endpoint_9_37_flag endpoint_9_37_sources 0 4 2 178609418018348985 178609418018348985 178609418018348985 endpoint_9_37_p4 endpoint_9_37_w4
private theorem endpoint_9_37_w6 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 6 2 178609418018348985 = some 178609418018348985 := by decide +kernel
private theorem endpoint_9_37_p8 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 8 178609418018348985 = some 178609418018348985 :=
  join_receipt_window endpoint_9_37_flag endpoint_9_37_sources 0 6 2 178609418018348985 178609418018348985 178609418018348985 endpoint_9_37_p6 endpoint_9_37_w6
def endpoint_9_37 : CertifiedEndpoint :=
  ⟨⟨9, 37, 3908⟩, 178609418018348985, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_37_flag endpoint_9_37_sources 8 178609418018348985 178609418018348985 rfl endpoint_9_37_base endpoint_9_37_p8) (by decide)⟩
private def endpoint_9_38_flag : Flag := ⟨9, 38, 3884⟩
private def endpoint_9_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_38_base : receiptBase endpoint_9_38_flag endpoint_9_38_sources = some 181533179080548171 := by decide +kernel
private theorem endpoint_9_38_w0 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 2 181533179080548171 = some 181533179080548171 := by decide +kernel
private theorem endpoint_9_38_w2 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 2 2 181533179080548171 = some 181533179080548171 := by decide +kernel
private theorem endpoint_9_38_p4 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 4 181533179080548171 = some 181533179080548171 :=
  join_receipt_window endpoint_9_38_flag endpoint_9_38_sources 0 2 2 181533179080548171 181533179080548171 181533179080548171 endpoint_9_38_w0 endpoint_9_38_w2
private theorem endpoint_9_38_w4 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 4 2 181533179080548171 = some 181533179080548171 := by decide +kernel
private theorem endpoint_9_38_p6 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 6 181533179080548171 = some 181533179080548171 :=
  join_receipt_window endpoint_9_38_flag endpoint_9_38_sources 0 4 2 181533179080548171 181533179080548171 181533179080548171 endpoint_9_38_p4 endpoint_9_38_w4
private theorem endpoint_9_38_w6 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 6 2 181533179080548171 = some 181533179080548171 := by decide +kernel
private theorem endpoint_9_38_p8 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 8 181533179080548171 = some 181533179080548171 :=
  join_receipt_window endpoint_9_38_flag endpoint_9_38_sources 0 6 2 181533179080548171 181533179080548171 181533179080548171 endpoint_9_38_p6 endpoint_9_38_w6
def endpoint_9_38 : CertifiedEndpoint :=
  ⟨⟨9, 38, 3884⟩, 181533179080548171, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_38_flag endpoint_9_38_sources 8 181533179080548171 181533179080548171 rfl endpoint_9_38_base endpoint_9_38_p8) (by decide)⟩
private def endpoint_9_39_flag : Flag := ⟨9, 39, 3859⟩
private def endpoint_9_39_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_39_base : receiptBase endpoint_9_39_flag endpoint_9_39_sources = some 184360102576015915 := by decide +kernel
private theorem endpoint_9_39_w0 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 2 184360102576015915 = some 184360102576015915 := by decide +kernel
private theorem endpoint_9_39_w2 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 2 2 184360102576015915 = some 184360102576015915 := by decide +kernel
private theorem endpoint_9_39_p4 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 4 184360102576015915 = some 184360102576015915 :=
  join_receipt_window endpoint_9_39_flag endpoint_9_39_sources 0 2 2 184360102576015915 184360102576015915 184360102576015915 endpoint_9_39_w0 endpoint_9_39_w2
private theorem endpoint_9_39_w4 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 4 2 184360102576015915 = some 184360102576015915 := by decide +kernel
private theorem endpoint_9_39_p6 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 6 184360102576015915 = some 184360102576015915 :=
  join_receipt_window endpoint_9_39_flag endpoint_9_39_sources 0 4 2 184360102576015915 184360102576015915 184360102576015915 endpoint_9_39_p4 endpoint_9_39_w4
private theorem endpoint_9_39_w6 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 6 2 184360102576015915 = some 184360102576015915 := by decide +kernel
private theorem endpoint_9_39_p8 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 8 184360102576015915 = some 184360102576015915 :=
  join_receipt_window endpoint_9_39_flag endpoint_9_39_sources 0 6 2 184360102576015915 184360102576015915 184360102576015915 endpoint_9_39_p6 endpoint_9_39_w6
def endpoint_9_39 : CertifiedEndpoint :=
  ⟨⟨9, 39, 3859⟩, 184360102576015915, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_39_flag endpoint_9_39_sources 8 184360102576015915 184360102576015915 rfl endpoint_9_39_base endpoint_9_39_p8) (by decide)⟩
private def endpoint_9_40_flag : Flag := ⟨9, 40, 3834⟩
private def endpoint_9_40_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_40_base : receiptBase endpoint_9_40_flag endpoint_9_40_sources = some 187135256450289634 := by decide +kernel
private theorem endpoint_9_40_w0 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 2 187135256450289634 = some 187135256450289634 := by decide +kernel
private theorem endpoint_9_40_w2 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 2 2 187135256450289634 = some 187135256450289634 := by decide +kernel
private theorem endpoint_9_40_p4 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 4 187135256450289634 = some 187135256450289634 :=
  join_receipt_window endpoint_9_40_flag endpoint_9_40_sources 0 2 2 187135256450289634 187135256450289634 187135256450289634 endpoint_9_40_w0 endpoint_9_40_w2
private theorem endpoint_9_40_w4 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 4 2 187135256450289634 = some 187135256450289634 := by decide +kernel
private theorem endpoint_9_40_p6 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 6 187135256450289634 = some 187135256450289634 :=
  join_receipt_window endpoint_9_40_flag endpoint_9_40_sources 0 4 2 187135256450289634 187135256450289634 187135256450289634 endpoint_9_40_p4 endpoint_9_40_w4
private theorem endpoint_9_40_w6 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 6 2 187135256450289634 = some 187135256450289634 := by decide +kernel
private theorem endpoint_9_40_p8 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 8 187135256450289634 = some 187135256450289634 :=
  join_receipt_window endpoint_9_40_flag endpoint_9_40_sources 0 6 2 187135256450289634 187135256450289634 187135256450289634 endpoint_9_40_p6 endpoint_9_40_w6
def endpoint_9_40 : CertifiedEndpoint :=
  ⟨⟨9, 40, 3834⟩, 187135256450289634, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_40_flag endpoint_9_40_sources 8 187135256450289634 187135256450289634 rfl endpoint_9_40_base endpoint_9_40_p8) (by decide)⟩
private def endpoint_9_41_flag : Flag := ⟨9, 41, 3809⟩
private def endpoint_9_41_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_41_base : receiptBase endpoint_9_41_flag endpoint_9_41_sources = some 190313791173711702 := by decide +kernel
private theorem endpoint_9_41_w0 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 2 190313791173711702 = some 190313791173711702 := by decide +kernel
private theorem endpoint_9_41_w2 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 2 2 190313791173711702 = some 190313791173711702 := by decide +kernel
private theorem endpoint_9_41_p4 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 4 190313791173711702 = some 190313791173711702 :=
  join_receipt_window endpoint_9_41_flag endpoint_9_41_sources 0 2 2 190313791173711702 190313791173711702 190313791173711702 endpoint_9_41_w0 endpoint_9_41_w2
private theorem endpoint_9_41_w4 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 4 2 190313791173711702 = some 190313791173711702 := by decide +kernel
private theorem endpoint_9_41_p6 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 6 190313791173711702 = some 190313791173711702 :=
  join_receipt_window endpoint_9_41_flag endpoint_9_41_sources 0 4 2 190313791173711702 190313791173711702 190313791173711702 endpoint_9_41_p4 endpoint_9_41_w4
private theorem endpoint_9_41_w6 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 6 2 190313791173711702 = some 190313791173711702 := by decide +kernel
private theorem endpoint_9_41_p8 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 8 190313791173711702 = some 190313791173711702 :=
  join_receipt_window endpoint_9_41_flag endpoint_9_41_sources 0 6 2 190313791173711702 190313791173711702 190313791173711702 endpoint_9_41_p6 endpoint_9_41_w6
def endpoint_9_41 : CertifiedEndpoint :=
  ⟨⟨9, 41, 3809⟩, 190313791173711702, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_41_flag endpoint_9_41_sources 8 190313791173711702 190313791173711702 rfl endpoint_9_41_base endpoint_9_41_p8) (by decide)⟩
private def endpoint_9_42_flag : Flag := ⟨9, 42, 3783⟩
private def endpoint_9_42_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_42_base : receiptBase endpoint_9_42_flag endpoint_9_42_sources = some 192907077576917663 := by decide +kernel
private theorem endpoint_9_42_w0 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 2 192907077576917663 = some 192907077576917663 := by decide +kernel
private theorem endpoint_9_42_w2 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 2 2 192907077576917663 = some 192907077576917663 := by decide +kernel
private theorem endpoint_9_42_p4 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 4 192907077576917663 = some 192907077576917663 :=
  join_receipt_window endpoint_9_42_flag endpoint_9_42_sources 0 2 2 192907077576917663 192907077576917663 192907077576917663 endpoint_9_42_w0 endpoint_9_42_w2
private theorem endpoint_9_42_w4 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 4 2 192907077576917663 = some 192907077576917663 := by decide +kernel
private theorem endpoint_9_42_p6 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 6 192907077576917663 = some 192907077576917663 :=
  join_receipt_window endpoint_9_42_flag endpoint_9_42_sources 0 4 2 192907077576917663 192907077576917663 192907077576917663 endpoint_9_42_p4 endpoint_9_42_w4
private theorem endpoint_9_42_w6 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 6 2 192907077576917663 = some 192907077576917663 := by decide +kernel
private theorem endpoint_9_42_p8 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 8 192907077576917663 = some 192907077576917663 :=
  join_receipt_window endpoint_9_42_flag endpoint_9_42_sources 0 6 2 192907077576917663 192907077576917663 192907077576917663 endpoint_9_42_p6 endpoint_9_42_w6
def endpoint_9_42 : CertifiedEndpoint :=
  ⟨⟨9, 42, 3783⟩, 192907077576917663, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_42_flag endpoint_9_42_sources 8 192907077576917663 192907077576917663 rfl endpoint_9_42_base endpoint_9_42_p8) (by decide)⟩
private def endpoint_9_43_flag : Flag := ⟨9, 43, 3757⟩
private def endpoint_9_43_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_43_base : receiptBase endpoint_9_43_flag endpoint_9_43_sources = some 195446807292579167 := by decide +kernel
private theorem endpoint_9_43_w0 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 2 195446807292579167 = some 195446807292579167 := by decide +kernel
private theorem endpoint_9_43_w2 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 2 2 195446807292579167 = some 195446807292579167 := by decide +kernel
private theorem endpoint_9_43_p4 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 4 195446807292579167 = some 195446807292579167 :=
  join_receipt_window endpoint_9_43_flag endpoint_9_43_sources 0 2 2 195446807292579167 195446807292579167 195446807292579167 endpoint_9_43_w0 endpoint_9_43_w2
private theorem endpoint_9_43_w4 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 4 2 195446807292579167 = some 195446807292579167 := by decide +kernel
private theorem endpoint_9_43_p6 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 6 195446807292579167 = some 195446807292579167 :=
  join_receipt_window endpoint_9_43_flag endpoint_9_43_sources 0 4 2 195446807292579167 195446807292579167 195446807292579167 endpoint_9_43_p4 endpoint_9_43_w4
private theorem endpoint_9_43_w6 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 6 2 195446807292579167 = some 195446807292579167 := by decide +kernel
private theorem endpoint_9_43_p8 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 8 195446807292579167 = some 195446807292579167 :=
  join_receipt_window endpoint_9_43_flag endpoint_9_43_sources 0 6 2 195446807292579167 195446807292579167 195446807292579167 endpoint_9_43_p6 endpoint_9_43_w6
def endpoint_9_43 : CertifiedEndpoint :=
  ⟨⟨9, 43, 3757⟩, 195446807292579167, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_43_flag endpoint_9_43_sources 8 195446807292579167 195446807292579167 rfl endpoint_9_43_base endpoint_9_43_p8) (by decide)⟩
private def endpoint_9_44_flag : Flag := ⟨9, 44, 3730⟩
private def endpoint_9_44_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_44_base : receiptBase endpoint_9_44_flag endpoint_9_44_sources = some 197880631993632062 := by decide +kernel
private theorem endpoint_9_44_w0 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 2 197880631993632062 = some 197880631993632062 := by decide +kernel
private theorem endpoint_9_44_w2 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 2 2 197880631993632062 = some 197880631993632062 := by decide +kernel
private theorem endpoint_9_44_p4 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 4 197880631993632062 = some 197880631993632062 :=
  join_receipt_window endpoint_9_44_flag endpoint_9_44_sources 0 2 2 197880631993632062 197880631993632062 197880631993632062 endpoint_9_44_w0 endpoint_9_44_w2
private theorem endpoint_9_44_w4 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 4 2 197880631993632062 = some 197880631993632062 := by decide +kernel
private theorem endpoint_9_44_p6 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 6 197880631993632062 = some 197880631993632062 :=
  join_receipt_window endpoint_9_44_flag endpoint_9_44_sources 0 4 2 197880631993632062 197880631993632062 197880631993632062 endpoint_9_44_p4 endpoint_9_44_w4
private theorem endpoint_9_44_w6 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 6 2 197880631993632062 = some 197880631993632062 := by decide +kernel
private theorem endpoint_9_44_p8 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 8 197880631993632062 = some 197880631993632062 :=
  join_receipt_window endpoint_9_44_flag endpoint_9_44_sources 0 6 2 197880631993632062 197880631993632062 197880631993632062 endpoint_9_44_p6 endpoint_9_44_w6
def endpoint_9_44 : CertifiedEndpoint :=
  ⟨⟨9, 44, 3730⟩, 197880631993632062, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_44_flag endpoint_9_44_sources 8 197880631993632062 197880631993632062 rfl endpoint_9_44_base endpoint_9_44_p8) (by decide)⟩
private def endpoint_9_45_flag : Flag := ⟨9, 45, 3703⟩
private def endpoint_9_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_45_base : receiptBase endpoint_9_45_flag endpoint_9_45_sources = some 200258879000063350 := by decide +kernel
private theorem endpoint_9_45_w0 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 2 200258879000063350 = some 200258879000063350 := by decide +kernel
private theorem endpoint_9_45_w2 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 2 2 200258879000063350 = some 200258879000063350 := by decide +kernel
private theorem endpoint_9_45_p4 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 4 200258879000063350 = some 200258879000063350 :=
  join_receipt_window endpoint_9_45_flag endpoint_9_45_sources 0 2 2 200258879000063350 200258879000063350 200258879000063350 endpoint_9_45_w0 endpoint_9_45_w2
private theorem endpoint_9_45_w4 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 4 2 200258879000063350 = some 200258879000063350 := by decide +kernel
private theorem endpoint_9_45_p6 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 6 200258879000063350 = some 200258879000063350 :=
  join_receipt_window endpoint_9_45_flag endpoint_9_45_sources 0 4 2 200258879000063350 200258879000063350 200258879000063350 endpoint_9_45_p4 endpoint_9_45_w4
private theorem endpoint_9_45_w6 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 6 2 200258879000063350 = some 200258879000063350 := by decide +kernel
private theorem endpoint_9_45_p8 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 8 200258879000063350 = some 200258879000063350 :=
  join_receipt_window endpoint_9_45_flag endpoint_9_45_sources 0 6 2 200258879000063350 200258879000063350 200258879000063350 endpoint_9_45_p6 endpoint_9_45_w6
def endpoint_9_45 : CertifiedEndpoint :=
  ⟨⟨9, 45, 3703⟩, 200258879000063350, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_45_flag endpoint_9_45_sources 8 200258879000063350 200258879000063350 rfl endpoint_9_45_base endpoint_9_45_p8) (by decide)⟩
private def endpoint_9_46_flag : Flag := ⟨9, 46, 3675⟩
private def endpoint_9_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_46_base : receiptBase endpoint_9_46_flag endpoint_9_46_sources = some 202527178977731732 := by decide +kernel
private theorem endpoint_9_46_w0 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 2 202527178977731732 = some 202527178977731732 := by decide +kernel
private theorem endpoint_9_46_w2 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 2 2 202527178977731732 = some 202527178977731732 := by decide +kernel
private theorem endpoint_9_46_p4 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 4 202527178977731732 = some 202527178977731732 :=
  join_receipt_window endpoint_9_46_flag endpoint_9_46_sources 0 2 2 202527178977731732 202527178977731732 202527178977731732 endpoint_9_46_w0 endpoint_9_46_w2
private theorem endpoint_9_46_w4 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 4 2 202527178977731732 = some 202527178977731732 := by decide +kernel
private theorem endpoint_9_46_p6 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 6 202527178977731732 = some 202527178977731732 :=
  join_receipt_window endpoint_9_46_flag endpoint_9_46_sources 0 4 2 202527178977731732 202527178977731732 202527178977731732 endpoint_9_46_p4 endpoint_9_46_w4
private theorem endpoint_9_46_w6 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 6 2 202527178977731732 = some 202527178977731732 := by decide +kernel
private theorem endpoint_9_46_p8 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 8 202527178977731732 = some 202527178977731732 :=
  join_receipt_window endpoint_9_46_flag endpoint_9_46_sources 0 6 2 202527178977731732 202527178977731732 202527178977731732 endpoint_9_46_p6 endpoint_9_46_w6
def endpoint_9_46 : CertifiedEndpoint :=
  ⟨⟨9, 46, 3675⟩, 202527178977731732, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_46_flag endpoint_9_46_sources 8 202527178977731732 202527178977731732 rfl endpoint_9_46_base endpoint_9_46_p8) (by decide)⟩
private def endpoint_9_47_flag : Flag := ⟨9, 47, 3647⟩
private def endpoint_9_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_47_base : receiptBase endpoint_9_47_flag endpoint_9_47_sources = some 204737880253701357 := by decide +kernel
private theorem endpoint_9_47_w0 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 2 204737880253701357 = some 204737880253701357 := by decide +kernel
private theorem endpoint_9_47_w2 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 2 2 204737880253701357 = some 204737880253701357 := by decide +kernel
private theorem endpoint_9_47_p4 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 4 204737880253701357 = some 204737880253701357 :=
  join_receipt_window endpoint_9_47_flag endpoint_9_47_sources 0 2 2 204737880253701357 204737880253701357 204737880253701357 endpoint_9_47_w0 endpoint_9_47_w2
private theorem endpoint_9_47_w4 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 4 2 204737880253701357 = some 204737880253701357 := by decide +kernel
private theorem endpoint_9_47_p6 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 6 204737880253701357 = some 204737880253701357 :=
  join_receipt_window endpoint_9_47_flag endpoint_9_47_sources 0 4 2 204737880253701357 204737880253701357 204737880253701357 endpoint_9_47_p4 endpoint_9_47_w4
private theorem endpoint_9_47_w6 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 6 2 204737880253701357 = some 204737880253701357 := by decide +kernel
private theorem endpoint_9_47_p8 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 8 204737880253701357 = some 204737880253701357 :=
  join_receipt_window endpoint_9_47_flag endpoint_9_47_sources 0 6 2 204737880253701357 204737880253701357 204737880253701357 endpoint_9_47_p6 endpoint_9_47_w6
def endpoint_9_47 : CertifiedEndpoint :=
  ⟨⟨9, 47, 3647⟩, 204737880253701357, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_47_flag endpoint_9_47_sources 8 204737880253701357 204737880253701357 rfl endpoint_9_47_base endpoint_9_47_p8) (by decide)⟩
private def endpoint_9_48_flag : Flag := ⟨9, 48, 3618⟩
private def endpoint_9_48_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_48_base : receiptBase endpoint_9_48_flag endpoint_9_48_sources = some 206834592486753776 := by decide +kernel
private theorem endpoint_9_48_w0 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 2 206834592486753776 = some 206834592486753776 := by decide +kernel
private theorem endpoint_9_48_w2 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 2 2 206834592486753776 = some 206834592486753776 := by decide +kernel
private theorem endpoint_9_48_p4 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 4 206834592486753776 = some 206834592486753776 :=
  join_receipt_window endpoint_9_48_flag endpoint_9_48_sources 0 2 2 206834592486753776 206834592486753776 206834592486753776 endpoint_9_48_w0 endpoint_9_48_w2
private theorem endpoint_9_48_w4 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 4 2 206834592486753776 = some 206834592486753776 := by decide +kernel
private theorem endpoint_9_48_p6 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 6 206834592486753776 = some 206834592486753776 :=
  join_receipt_window endpoint_9_48_flag endpoint_9_48_sources 0 4 2 206834592486753776 206834592486753776 206834592486753776 endpoint_9_48_p4 endpoint_9_48_w4
private theorem endpoint_9_48_w6 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 6 2 206834592486753776 = some 206834592486753776 := by decide +kernel
private theorem endpoint_9_48_p8 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 8 206834592486753776 = some 206834592486753776 :=
  join_receipt_window endpoint_9_48_flag endpoint_9_48_sources 0 6 2 206834592486753776 206834592486753776 206834592486753776 endpoint_9_48_p6 endpoint_9_48_w6
def endpoint_9_48 : CertifiedEndpoint :=
  ⟨⟨9, 48, 3618⟩, 206834592486753776, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_48_flag endpoint_9_48_sources 8 206834592486753776 206834592486753776 rfl endpoint_9_48_base endpoint_9_48_p8) (by decide)⟩
private def endpoint_9_49_flag : Flag := ⟨9, 49, 3589⟩
private def endpoint_9_49_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_49_base : receiptBase endpoint_9_49_flag endpoint_9_49_sources = some 208871685011030290 := by decide +kernel
private theorem endpoint_9_49_w0 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 2 208871685011030290 = some 208871685011030290 := by decide +kernel
private theorem endpoint_9_49_w2 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 2 2 208871685011030290 = some 208871685011030290 := by decide +kernel
private theorem endpoint_9_49_p4 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 4 208871685011030290 = some 208871685011030290 :=
  join_receipt_window endpoint_9_49_flag endpoint_9_49_sources 0 2 2 208871685011030290 208871685011030290 208871685011030290 endpoint_9_49_w0 endpoint_9_49_w2
private theorem endpoint_9_49_w4 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 4 2 208871685011030290 = some 208871685011030290 := by decide +kernel
private theorem endpoint_9_49_p6 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 6 208871685011030290 = some 208871685011030290 :=
  join_receipt_window endpoint_9_49_flag endpoint_9_49_sources 0 4 2 208871685011030290 208871685011030290 208871685011030290 endpoint_9_49_p4 endpoint_9_49_w4
private theorem endpoint_9_49_w6 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 6 2 208871685011030290 = some 208871685011030290 := by decide +kernel
private theorem endpoint_9_49_p8 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 8 208871685011030290 = some 208871685011030290 :=
  join_receipt_window endpoint_9_49_flag endpoint_9_49_sources 0 6 2 208871685011030290 208871685011030290 208871685011030290 endpoint_9_49_p6 endpoint_9_49_w6
def endpoint_9_49 : CertifiedEndpoint :=
  ⟨⟨9, 49, 3589⟩, 208871685011030290, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_49_flag endpoint_9_49_sources 8 208871685011030290 208871685011030290 rfl endpoint_9_49_base endpoint_9_49_p8) (by decide)⟩
private def endpoint_9_50_flag : Flag := ⟨9, 50, 3559⟩
private def endpoint_9_50_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_50_base : receiptBase endpoint_9_50_flag endpoint_9_50_sources = some 210790746478235299 := by decide +kernel
private theorem endpoint_9_50_w0 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 2 210790746478235299 = some 210790746478235299 := by decide +kernel
private theorem endpoint_9_50_w2 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 2 2 210790746478235299 = some 210790746478235299 := by decide +kernel
private theorem endpoint_9_50_p4 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 4 210790746478235299 = some 210790746478235299 :=
  join_receipt_window endpoint_9_50_flag endpoint_9_50_sources 0 2 2 210790746478235299 210790746478235299 210790746478235299 endpoint_9_50_w0 endpoint_9_50_w2
private theorem endpoint_9_50_w4 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 4 2 210790746478235299 = some 210790746478235299 := by decide +kernel
private theorem endpoint_9_50_p6 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 6 210790746478235299 = some 210790746478235299 :=
  join_receipt_window endpoint_9_50_flag endpoint_9_50_sources 0 4 2 210790746478235299 210790746478235299 210790746478235299 endpoint_9_50_p4 endpoint_9_50_w4
private theorem endpoint_9_50_w6 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 6 2 210790746478235299 = some 210790746478235299 := by decide +kernel
private theorem endpoint_9_50_p8 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 8 210790746478235299 = some 210790746478235299 :=
  join_receipt_window endpoint_9_50_flag endpoint_9_50_sources 0 6 2 210790746478235299 210790746478235299 210790746478235299 endpoint_9_50_p6 endpoint_9_50_w6
def endpoint_9_50 : CertifiedEndpoint :=
  ⟨⟨9, 50, 3559⟩, 210790746478235299, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_50_flag endpoint_9_50_sources 8 210790746478235299 210790746478235299 rfl endpoint_9_50_base endpoint_9_50_p8) (by decide)⟩
private def endpoint_9_51_flag : Flag := ⟨9, 51, 3529⟩
private def endpoint_9_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_51_base : receiptBase endpoint_9_51_flag endpoint_9_51_sources = some 212648167229587254 := by decide +kernel
private theorem endpoint_9_51_w0 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 2 212648167229587254 = some 212648167229587254 := by decide +kernel
private theorem endpoint_9_51_w2 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 2 2 212648167229587254 = some 212648167229587254 := by decide +kernel
private theorem endpoint_9_51_p4 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 4 212648167229587254 = some 212648167229587254 :=
  join_receipt_window endpoint_9_51_flag endpoint_9_51_sources 0 2 2 212648167229587254 212648167229587254 212648167229587254 endpoint_9_51_w0 endpoint_9_51_w2
private theorem endpoint_9_51_w4 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 4 2 212648167229587254 = some 212648167229587254 := by decide +kernel
private theorem endpoint_9_51_p6 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 6 212648167229587254 = some 212648167229587254 :=
  join_receipt_window endpoint_9_51_flag endpoint_9_51_sources 0 4 2 212648167229587254 212648167229587254 212648167229587254 endpoint_9_51_p4 endpoint_9_51_w4
private theorem endpoint_9_51_w6 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 6 2 212648167229587254 = some 212648167229587254 := by decide +kernel
private theorem endpoint_9_51_p8 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 8 212648167229587254 = some 212648167229587254 :=
  join_receipt_window endpoint_9_51_flag endpoint_9_51_sources 0 6 2 212648167229587254 212648167229587254 212648167229587254 endpoint_9_51_p6 endpoint_9_51_w6
def endpoint_9_51 : CertifiedEndpoint :=
  ⟨⟨9, 51, 3529⟩, 212648167229587254, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_51_flag endpoint_9_51_sources 8 212648167229587254 212648167229587254 rfl endpoint_9_51_base endpoint_9_51_p8) (by decide)⟩
private def endpoint_9_52_flag : Flag := ⟨9, 52, 3497⟩
private def endpoint_9_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_52_base : receiptBase endpoint_9_52_flag endpoint_9_52_sources = some 214323082554340657 := by decide +kernel
private theorem endpoint_9_52_w0 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 2 214323082554340657 = some 214323082554340657 := by decide +kernel
private theorem endpoint_9_52_w2 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 2 2 214323082554340657 = some 214323082554340657 := by decide +kernel
private theorem endpoint_9_52_p4 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 4 214323082554340657 = some 214323082554340657 :=
  join_receipt_window endpoint_9_52_flag endpoint_9_52_sources 0 2 2 214323082554340657 214323082554340657 214323082554340657 endpoint_9_52_w0 endpoint_9_52_w2
private theorem endpoint_9_52_w4 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 4 2 214323082554340657 = some 214323082554340657 := by decide +kernel
private theorem endpoint_9_52_p6 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 6 214323082554340657 = some 214323082554340657 :=
  join_receipt_window endpoint_9_52_flag endpoint_9_52_sources 0 4 2 214323082554340657 214323082554340657 214323082554340657 endpoint_9_52_p4 endpoint_9_52_w4
private theorem endpoint_9_52_w6 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 6 2 214323082554340657 = some 214323082554340657 := by decide +kernel
private theorem endpoint_9_52_p8 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 8 214323082554340657 = some 214323082554340657 :=
  join_receipt_window endpoint_9_52_flag endpoint_9_52_sources 0 6 2 214323082554340657 214323082554340657 214323082554340657 endpoint_9_52_p6 endpoint_9_52_w6
def endpoint_9_52 : CertifiedEndpoint :=
  ⟨⟨9, 52, 3497⟩, 214323082554340657, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_52_flag endpoint_9_52_sources 8 214323082554340657 214323082554340657 rfl endpoint_9_52_base endpoint_9_52_p8) (by decide)⟩
private def endpoint_9_53_flag : Flag := ⟨9, 53, 3465⟩
private def endpoint_9_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_53_base : receiptBase endpoint_9_53_flag endpoint_9_53_sources = some 215932315149086707 := by decide +kernel
private theorem endpoint_9_53_w0 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 2 215932315149086707 = some 215932315149086707 := by decide +kernel
private theorem endpoint_9_53_w2 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 2 2 215932315149086707 = some 215932315149086707 := by decide +kernel
private theorem endpoint_9_53_p4 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 4 215932315149086707 = some 215932315149086707 :=
  join_receipt_window endpoint_9_53_flag endpoint_9_53_sources 0 2 2 215932315149086707 215932315149086707 215932315149086707 endpoint_9_53_w0 endpoint_9_53_w2
private theorem endpoint_9_53_w4 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 4 2 215932315149086707 = some 215932315149086707 := by decide +kernel
private theorem endpoint_9_53_p6 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 6 215932315149086707 = some 215932315149086707 :=
  join_receipt_window endpoint_9_53_flag endpoint_9_53_sources 0 4 2 215932315149086707 215932315149086707 215932315149086707 endpoint_9_53_p4 endpoint_9_53_w4
private theorem endpoint_9_53_w6 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 6 2 215932315149086707 = some 215932315149086707 := by decide +kernel
private theorem endpoint_9_53_p8 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 8 215932315149086707 = some 215932315149086707 :=
  join_receipt_window endpoint_9_53_flag endpoint_9_53_sources 0 6 2 215932315149086707 215932315149086707 215932315149086707 endpoint_9_53_p6 endpoint_9_53_w6
def endpoint_9_53 : CertifiedEndpoint :=
  ⟨⟨9, 53, 3465⟩, 215932315149086707, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_53_flag endpoint_9_53_sources 8 215932315149086707 215932315149086707 rfl endpoint_9_53_base endpoint_9_53_p8) (by decide)⟩
private def endpoint_9_54_flag : Flag := ⟨9, 54, 3433⟩
private def endpoint_9_54_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_54_base : receiptBase endpoint_9_54_flag endpoint_9_54_sources = some 217475865013825403 := by decide +kernel
private theorem endpoint_9_54_w0 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 2 217475865013825403 = some 217475865013825403 := by decide +kernel
private theorem endpoint_9_54_w2 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 2 2 217475865013825403 = some 217475865013825403 := by decide +kernel
private theorem endpoint_9_54_p4 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 4 217475865013825403 = some 217475865013825403 :=
  join_receipt_window endpoint_9_54_flag endpoint_9_54_sources 0 2 2 217475865013825403 217475865013825403 217475865013825403 endpoint_9_54_w0 endpoint_9_54_w2
private theorem endpoint_9_54_w4 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 4 2 217475865013825403 = some 217475865013825403 := by decide +kernel
private theorem endpoint_9_54_p6 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 6 217475865013825403 = some 217475865013825403 :=
  join_receipt_window endpoint_9_54_flag endpoint_9_54_sources 0 4 2 217475865013825403 217475865013825403 217475865013825403 endpoint_9_54_p4 endpoint_9_54_w4
private theorem endpoint_9_54_w6 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 6 2 217475865013825403 = some 217475865013825403 := by decide +kernel
private theorem endpoint_9_54_p8 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 8 217475865013825403 = some 217475865013825403 :=
  join_receipt_window endpoint_9_54_flag endpoint_9_54_sources 0 6 2 217475865013825403 217475865013825403 217475865013825403 endpoint_9_54_p6 endpoint_9_54_w6
def endpoint_9_54 : CertifiedEndpoint :=
  ⟨⟨9, 54, 3433⟩, 217475865013825403, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_54_flag endpoint_9_54_sources 8 217475865013825403 217475865013825403 rfl endpoint_9_54_base endpoint_9_54_p8) (by decide)⟩
private def endpoint_9_55_flag : Flag := ⟨9, 55, 3399⟩
private def endpoint_9_55_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_9_55_base : receiptBase endpoint_9_55_flag endpoint_9_55_sources = some 219519034918080347 := by decide +kernel
private theorem endpoint_9_55_w0 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 2 219519034918080347 = some 219519034918080347 := by decide +kernel
private theorem endpoint_9_55_w2 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 2 2 219519034918080347 = some 219519034918080347 := by decide +kernel
private theorem endpoint_9_55_p4 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 4 219519034918080347 = some 219519034918080347 :=
  join_receipt_window endpoint_9_55_flag endpoint_9_55_sources 0 2 2 219519034918080347 219519034918080347 219519034918080347 endpoint_9_55_w0 endpoint_9_55_w2
private theorem endpoint_9_55_w4 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 4 2 219519034918080347 = some 219519034918080347 := by decide +kernel
private theorem endpoint_9_55_p6 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 6 219519034918080347 = some 219519034918080347 :=
  join_receipt_window endpoint_9_55_flag endpoint_9_55_sources 0 4 2 219519034918080347 219519034918080347 219519034918080347 endpoint_9_55_p4 endpoint_9_55_w4
private theorem endpoint_9_55_w6 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 6 2 219519034918080347 = some 219519034918080347 := by decide +kernel
private theorem endpoint_9_55_p8 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 8 219519034918080347 = some 219519034918080347 :=
  join_receipt_window endpoint_9_55_flag endpoint_9_55_sources 0 6 2 219519034918080347 219519034918080347 219519034918080347 endpoint_9_55_p6 endpoint_9_55_w6
def endpoint_9_55 : CertifiedEndpoint :=
  ⟨⟨9, 55, 3399⟩, 219519034918080347, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_9_55_flag endpoint_9_55_sources 8 219519034918080347 219519034918080347 rfl endpoint_9_55_base endpoint_9_55_p8) (by decide)⟩
private def endpoint_9_56_flag : Flag := ⟨9, 56, 3364⟩
private def endpoint_9_56_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_9_56_base : receiptBase endpoint_9_56_flag endpoint_9_56_sources = some 220743209160410804 := by decide +kernel
private theorem endpoint_9_56_w0 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 2 220743209160410804 = some 220743209160410804 := by decide +kernel
private theorem endpoint_9_56_w2 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 2 2 220743209160410804 = some 220743209160410804 := by decide +kernel
private theorem endpoint_9_56_p4 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 4 220743209160410804 = some 220743209160410804 :=
  join_receipt_window endpoint_9_56_flag endpoint_9_56_sources 0 2 2 220743209160410804 220743209160410804 220743209160410804 endpoint_9_56_w0 endpoint_9_56_w2
private theorem endpoint_9_56_w4 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 4 2 220743209160410804 = some 220743209160410804 := by decide +kernel
private theorem endpoint_9_56_p6 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 6 220743209160410804 = some 220743209160410804 :=
  join_receipt_window endpoint_9_56_flag endpoint_9_56_sources 0 4 2 220743209160410804 220743209160410804 220743209160410804 endpoint_9_56_p4 endpoint_9_56_w4
private theorem endpoint_9_56_w6 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 6 2 220743209160410804 = some 220743209160410804 := by decide +kernel
private theorem endpoint_9_56_p8 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 8 220743209160410804 = some 220743209160410804 :=
  join_receipt_window endpoint_9_56_flag endpoint_9_56_sources 0 6 2 220743209160410804 220743209160410804 220743209160410804 endpoint_9_56_p6 endpoint_9_56_w6
def endpoint_9_56 : CertifiedEndpoint :=
  ⟨⟨9, 56, 3364⟩, 220743209160410804, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_9_56_flag endpoint_9_56_sources 8 220743209160410804 220743209160410804 rfl endpoint_9_56_base endpoint_9_56_p8) (by decide)⟩
private def endpoint_9_57_flag : Flag := ⟨9, 57, 3329⟩
private def endpoint_9_57_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_9_57_base : receiptBase endpoint_9_57_flag endpoint_9_57_sources = some 221895313626017225 := by decide +kernel
private theorem endpoint_9_57_w0 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 2 221895313626017225 = some 221895313626017225 := by decide +kernel
private theorem endpoint_9_57_w2 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 2 2 221895313626017225 = some 221895313626017225 := by decide +kernel
private theorem endpoint_9_57_p4 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 4 221895313626017225 = some 221895313626017225 :=
  join_receipt_window endpoint_9_57_flag endpoint_9_57_sources 0 2 2 221895313626017225 221895313626017225 221895313626017225 endpoint_9_57_w0 endpoint_9_57_w2
private theorem endpoint_9_57_w4 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 4 2 221895313626017225 = some 221895313626017225 := by decide +kernel
private theorem endpoint_9_57_p6 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 6 221895313626017225 = some 221895313626017225 :=
  join_receipt_window endpoint_9_57_flag endpoint_9_57_sources 0 4 2 221895313626017225 221895313626017225 221895313626017225 endpoint_9_57_p4 endpoint_9_57_w4
private theorem endpoint_9_57_w6 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 6 2 221895313626017225 = some 221895313626017225 := by decide +kernel
private theorem endpoint_9_57_p8 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 8 221895313626017225 = some 221895313626017225 :=
  join_receipt_window endpoint_9_57_flag endpoint_9_57_sources 0 6 2 221895313626017225 221895313626017225 221895313626017225 endpoint_9_57_p6 endpoint_9_57_w6
def endpoint_9_57 : CertifiedEndpoint :=
  ⟨⟨9, 57, 3329⟩, 221895313626017225, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_9_57_flag endpoint_9_57_sources 8 221895313626017225 221895313626017225 rfl endpoint_9_57_base endpoint_9_57_p8) (by decide)⟩
private def endpoint_9_58_flag : Flag := ⟨9, 58, 3292⟩
private def endpoint_9_58_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_9_58_base : receiptBase endpoint_9_58_flag endpoint_9_58_sources = some 222914674328728921 := by decide +kernel
private theorem endpoint_9_58_w0 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 2 222914674328728921 = some 222914674328728921 := by decide +kernel
private theorem endpoint_9_58_w2 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 2 2 222914674328728921 = some 222914674328728921 := by decide +kernel
private theorem endpoint_9_58_p4 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 4 222914674328728921 = some 222914674328728921 :=
  join_receipt_window endpoint_9_58_flag endpoint_9_58_sources 0 2 2 222914674328728921 222914674328728921 222914674328728921 endpoint_9_58_w0 endpoint_9_58_w2
private theorem endpoint_9_58_w4 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 4 2 222914674328728921 = some 222914674328728921 := by decide +kernel
private theorem endpoint_9_58_p6 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 6 222914674328728921 = some 222914674328728921 :=
  join_receipt_window endpoint_9_58_flag endpoint_9_58_sources 0 4 2 222914674328728921 222914674328728921 222914674328728921 endpoint_9_58_p4 endpoint_9_58_w4
private theorem endpoint_9_58_w6 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 6 2 222914674328728921 = some 222914674328728921 := by decide +kernel
private theorem endpoint_9_58_p8 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 8 222914674328728921 = some 222914674328728921 :=
  join_receipt_window endpoint_9_58_flag endpoint_9_58_sources 0 6 2 222914674328728921 222914674328728921 222914674328728921 endpoint_9_58_p6 endpoint_9_58_w6
def endpoint_9_58 : CertifiedEndpoint :=
  ⟨⟨9, 58, 3292⟩, 222914674328728921, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_9_58_flag endpoint_9_58_sources 8 222914674328728921 222914674328728921 rfl endpoint_9_58_base endpoint_9_58_p8) (by decide)⟩
private def endpoint_9_59_flag : Flag := ⟨9, 59, 3254⟩
private def endpoint_9_59_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_59_base : receiptBase endpoint_9_59_flag endpoint_9_59_sources = some 225864402736689041 := by decide +kernel
private theorem endpoint_9_59_w0 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 2 225864402736689041 = some 225864402736689041 := by decide +kernel
private theorem endpoint_9_59_w2 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 2 2 225864402736689041 = some 225864402736689041 := by decide +kernel
private theorem endpoint_9_59_p4 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 4 225864402736689041 = some 225864402736689041 :=
  join_receipt_window endpoint_9_59_flag endpoint_9_59_sources 0 2 2 225864402736689041 225864402736689041 225864402736689041 endpoint_9_59_w0 endpoint_9_59_w2
private theorem endpoint_9_59_w4 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 4 2 225864402736689041 = some 225864402736689041 := by decide +kernel
private theorem endpoint_9_59_p6 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 6 225864402736689041 = some 225864402736689041 :=
  join_receipt_window endpoint_9_59_flag endpoint_9_59_sources 0 4 2 225864402736689041 225864402736689041 225864402736689041 endpoint_9_59_p4 endpoint_9_59_w4
private theorem endpoint_9_59_w6 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 6 2 225864402736689041 = some 225864402736689041 := by decide +kernel
private theorem endpoint_9_59_p8 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 8 225864402736689041 = some 225864402736689041 :=
  join_receipt_window endpoint_9_59_flag endpoint_9_59_sources 0 6 2 225864402736689041 225864402736689041 225864402736689041 endpoint_9_59_p6 endpoint_9_59_w6
def endpoint_9_59 : CertifiedEndpoint :=
  ⟨⟨9, 59, 3254⟩, 225864402736689041, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_59_flag endpoint_9_59_sources 8 225864402736689041 225864402736689041 rfl endpoint_9_59_base endpoint_9_59_p8) (by decide)⟩
private def endpoint_9_60_flag : Flag := ⟨9, 60, 3215⟩
private def endpoint_9_60_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_60_base : receiptBase endpoint_9_60_flag endpoint_9_60_sources = some 226488372798272523 := by decide +kernel
private theorem endpoint_9_60_w0 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 2 226488372798272523 = some 226488372798272523 := by decide +kernel
private theorem endpoint_9_60_w2 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 2 2 226488372798272523 = some 226488372798272523 := by decide +kernel
private theorem endpoint_9_60_p4 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 4 226488372798272523 = some 226488372798272523 :=
  join_receipt_window endpoint_9_60_flag endpoint_9_60_sources 0 2 2 226488372798272523 226488372798272523 226488372798272523 endpoint_9_60_w0 endpoint_9_60_w2
private theorem endpoint_9_60_w4 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 4 2 226488372798272523 = some 226488372798272523 := by decide +kernel
private theorem endpoint_9_60_p6 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 6 226488372798272523 = some 226488372798272523 :=
  join_receipt_window endpoint_9_60_flag endpoint_9_60_sources 0 4 2 226488372798272523 226488372798272523 226488372798272523 endpoint_9_60_p4 endpoint_9_60_w4
private theorem endpoint_9_60_w6 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 6 2 226488372798272523 = some 226488372798272523 := by decide +kernel
private theorem endpoint_9_60_p8 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 8 226488372798272523 = some 226488372798272523 :=
  join_receipt_window endpoint_9_60_flag endpoint_9_60_sources 0 6 2 226488372798272523 226488372798272523 226488372798272523 endpoint_9_60_p6 endpoint_9_60_w6
def endpoint_9_60 : CertifiedEndpoint :=
  ⟨⟨9, 60, 3215⟩, 226488372798272523, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_60_flag endpoint_9_60_sources 8 226488372798272523 226488372798272523 rfl endpoint_9_60_base endpoint_9_60_p8) (by decide)⟩
private def endpoint_9_61_flag : Flag := ⟨9, 61, 3175⟩
private def endpoint_9_61_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_61_base : receiptBase endpoint_9_61_flag endpoint_9_61_sources = some 226961149375493270 := by decide +kernel
private theorem endpoint_9_61_w0 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 2 226961149375493270 = some 226961149375493270 := by decide +kernel
private theorem endpoint_9_61_w2 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 2 2 226961149375493270 = some 226961149375493270 := by decide +kernel
private theorem endpoint_9_61_p4 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 4 226961149375493270 = some 226961149375493270 :=
  join_receipt_window endpoint_9_61_flag endpoint_9_61_sources 0 2 2 226961149375493270 226961149375493270 226961149375493270 endpoint_9_61_w0 endpoint_9_61_w2
private theorem endpoint_9_61_w4 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 4 2 226961149375493270 = some 226961149375493270 := by decide +kernel
private theorem endpoint_9_61_p6 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 6 226961149375493270 = some 226961149375493270 :=
  join_receipt_window endpoint_9_61_flag endpoint_9_61_sources 0 4 2 226961149375493270 226961149375493270 226961149375493270 endpoint_9_61_p4 endpoint_9_61_w4
private theorem endpoint_9_61_w6 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 6 2 226961149375493270 = some 226961149375493270 := by decide +kernel
private theorem endpoint_9_61_p8 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 8 226961149375493270 = some 226961149375493270 :=
  join_receipt_window endpoint_9_61_flag endpoint_9_61_sources 0 6 2 226961149375493270 226961149375493270 226961149375493270 endpoint_9_61_p6 endpoint_9_61_w6
def endpoint_9_61 : CertifiedEndpoint :=
  ⟨⟨9, 61, 3175⟩, 226961149375493270, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_61_flag endpoint_9_61_sources 8 226961149375493270 226961149375493270 rfl endpoint_9_61_base endpoint_9_61_p8) (by decide)⟩
private def endpoint_9_62_flag : Flag := ⟨9, 62, 3133⟩
private def endpoint_9_62_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_62_base : receiptBase endpoint_9_62_flag endpoint_9_62_sources = some 227208001405324188 := by decide +kernel
private theorem endpoint_9_62_w0 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 2 227208001405324188 = some 227208001405324188 := by decide +kernel
private theorem endpoint_9_62_w2 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 2 2 227208001405324188 = some 227208001405324188 := by decide +kernel
private theorem endpoint_9_62_p4 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 4 227208001405324188 = some 227208001405324188 :=
  join_receipt_window endpoint_9_62_flag endpoint_9_62_sources 0 2 2 227208001405324188 227208001405324188 227208001405324188 endpoint_9_62_w0 endpoint_9_62_w2
private theorem endpoint_9_62_w4 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 4 2 227208001405324188 = some 227208001405324188 := by decide +kernel
private theorem endpoint_9_62_p6 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 6 227208001405324188 = some 227208001405324188 :=
  join_receipt_window endpoint_9_62_flag endpoint_9_62_sources 0 4 2 227208001405324188 227208001405324188 227208001405324188 endpoint_9_62_p4 endpoint_9_62_w4
private theorem endpoint_9_62_w6 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 6 2 227208001405324188 = some 227208001405324188 := by decide +kernel
private theorem endpoint_9_62_p8 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 8 227208001405324188 = some 227208001405324188 :=
  join_receipt_window endpoint_9_62_flag endpoint_9_62_sources 0 6 2 227208001405324188 227208001405324188 227208001405324188 endpoint_9_62_p6 endpoint_9_62_w6
def endpoint_9_62 : CertifiedEndpoint :=
  ⟨⟨9, 62, 3133⟩, 227208001405324188, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_62_flag endpoint_9_62_sources 8 227208001405324188 227208001405324188 rfl endpoint_9_62_base endpoint_9_62_p8) (by decide)⟩
private def endpoint_9_63_flag : Flag := ⟨9, 63, 3089⟩
private def endpoint_9_63_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_63_base : receiptBase endpoint_9_63_flag endpoint_9_63_sources = some 227222811894058425 := by decide +kernel
private theorem endpoint_9_63_w0 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 2 227222811894058425 = some 227222811894058425 := by decide +kernel
private theorem endpoint_9_63_w2 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 2 2 227222811894058425 = some 227222811894058425 := by decide +kernel
private theorem endpoint_9_63_p4 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 4 227222811894058425 = some 227222811894058425 :=
  join_receipt_window endpoint_9_63_flag endpoint_9_63_sources 0 2 2 227222811894058425 227222811894058425 227222811894058425 endpoint_9_63_w0 endpoint_9_63_w2
private theorem endpoint_9_63_w4 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 4 2 227222811894058425 = some 227222811894058425 := by decide +kernel
private theorem endpoint_9_63_p6 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 6 227222811894058425 = some 227222811894058425 :=
  join_receipt_window endpoint_9_63_flag endpoint_9_63_sources 0 4 2 227222811894058425 227222811894058425 227222811894058425 endpoint_9_63_p4 endpoint_9_63_w4
private theorem endpoint_9_63_w6 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 6 2 227222811894058425 = some 227222811894058425 := by decide +kernel
private theorem endpoint_9_63_p8 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 8 227222811894058425 = some 227222811894058425 :=
  join_receipt_window endpoint_9_63_flag endpoint_9_63_sources 0 6 2 227222811894058425 227222811894058425 227222811894058425 endpoint_9_63_p6 endpoint_9_63_w6
def endpoint_9_63 : CertifiedEndpoint :=
  ⟨⟨9, 63, 3089⟩, 227222811894058425, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_63_flag endpoint_9_63_sources 8 227222811894058425 227222811894058425 rfl endpoint_9_63_base endpoint_9_63_p8) (by decide)⟩
private def endpoint_9_64_flag : Flag := ⟨9, 64, 3043⟩
private def endpoint_9_64_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_9_64_base : receiptBase endpoint_9_64_flag endpoint_9_64_sources = some 228297586894400230 := by decide +kernel
private theorem endpoint_9_64_w0 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 2 228297586894400230 = some 228297586894400230 := by decide +kernel
private theorem endpoint_9_64_w2 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 2 2 228297586894400230 = some 228297586894400230 := by decide +kernel
private theorem endpoint_9_64_p4 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 4 228297586894400230 = some 228297586894400230 :=
  join_receipt_window endpoint_9_64_flag endpoint_9_64_sources 0 2 2 228297586894400230 228297586894400230 228297586894400230 endpoint_9_64_w0 endpoint_9_64_w2
private theorem endpoint_9_64_w4 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 4 2 228297586894400230 = some 228297586894400230 := by decide +kernel
private theorem endpoint_9_64_p6 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 6 228297586894400230 = some 228297586894400230 :=
  join_receipt_window endpoint_9_64_flag endpoint_9_64_sources 0 4 2 228297586894400230 228297586894400230 228297586894400230 endpoint_9_64_p4 endpoint_9_64_w4
private theorem endpoint_9_64_w6 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 6 2 228297586894400230 = some 228297586894400230 := by decide +kernel
private theorem endpoint_9_64_p8 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 8 228297586894400230 = some 228297586894400230 :=
  join_receipt_window endpoint_9_64_flag endpoint_9_64_sources 0 6 2 228297586894400230 228297586894400230 228297586894400230 endpoint_9_64_p6 endpoint_9_64_w6
def endpoint_9_64 : CertifiedEndpoint :=
  ⟨⟨9, 64, 3043⟩, 228297586894400230, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_9_64_flag endpoint_9_64_sources 8 228297586894400230 228297586894400230 rfl endpoint_9_64_base endpoint_9_64_p8) (by decide)⟩
private def endpoint_9_65_flag : Flag := ⟨9, 65, 2995⟩
private def endpoint_9_65_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_9_65_base : receiptBase endpoint_9_65_flag endpoint_9_65_sources = some 227829413337616673 := by decide +kernel
private theorem endpoint_9_65_w0 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 2 227829413337616673 = some 227829413337616673 := by decide +kernel
private theorem endpoint_9_65_w2 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 2 2 227829413337616673 = some 227829413337616673 := by decide +kernel
private theorem endpoint_9_65_p4 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 4 227829413337616673 = some 227829413337616673 :=
  join_receipt_window endpoint_9_65_flag endpoint_9_65_sources 0 2 2 227829413337616673 227829413337616673 227829413337616673 endpoint_9_65_w0 endpoint_9_65_w2
private theorem endpoint_9_65_w4 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 4 2 227829413337616673 = some 227829413337616673 := by decide +kernel
private theorem endpoint_9_65_p6 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 6 227829413337616673 = some 227829413337616673 :=
  join_receipt_window endpoint_9_65_flag endpoint_9_65_sources 0 4 2 227829413337616673 227829413337616673 227829413337616673 endpoint_9_65_p4 endpoint_9_65_w4
private theorem endpoint_9_65_w6 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 6 2 227829413337616673 = some 227829413337616673 := by decide +kernel
private theorem endpoint_9_65_p8 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 8 227829413337616673 = some 227829413337616673 :=
  join_receipt_window endpoint_9_65_flag endpoint_9_65_sources 0 6 2 227829413337616673 227829413337616673 227829413337616673 endpoint_9_65_p6 endpoint_9_65_w6
def endpoint_9_65 : CertifiedEndpoint :=
  ⟨⟨9, 65, 2995⟩, 227829413337616673, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_9_65_flag endpoint_9_65_sources 8 227829413337616673 227829413337616673 rfl endpoint_9_65_base endpoint_9_65_p8) (by decide)⟩
private def endpoint_9_66_flag : Flag := ⟨9, 66, 2944⟩
private def endpoint_9_66_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_9_66_base : receiptBase endpoint_9_66_flag endpoint_9_66_sources = some 228379746668465238 := by decide +kernel
private theorem endpoint_9_66_w0 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 2 228379746668465238 = some 228379746668465238 := by decide +kernel
private theorem endpoint_9_66_w2 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 2 2 228379746668465238 = some 228379746668465238 := by decide +kernel
private theorem endpoint_9_66_p4 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 4 228379746668465238 = some 228379746668465238 :=
  join_receipt_window endpoint_9_66_flag endpoint_9_66_sources 0 2 2 228379746668465238 228379746668465238 228379746668465238 endpoint_9_66_w0 endpoint_9_66_w2
private theorem endpoint_9_66_w4 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 4 2 228379746668465238 = some 228379746668465238 := by decide +kernel
private theorem endpoint_9_66_p6 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 6 228379746668465238 = some 228379746668465238 :=
  join_receipt_window endpoint_9_66_flag endpoint_9_66_sources 0 4 2 228379746668465238 228379746668465238 228379746668465238 endpoint_9_66_p4 endpoint_9_66_w4
private theorem endpoint_9_66_w6 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 6 2 228379746668465238 = some 228379746668465238 := by decide +kernel
private theorem endpoint_9_66_p8 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 8 228379746668465238 = some 228379746668465238 :=
  join_receipt_window endpoint_9_66_flag endpoint_9_66_sources 0 6 2 228379746668465238 228379746668465238 228379746668465238 endpoint_9_66_p6 endpoint_9_66_w6
def endpoint_9_66 : CertifiedEndpoint :=
  ⟨⟨9, 66, 2944⟩, 228379746668465238, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_9_66_flag endpoint_9_66_sources 8 228379746668465238 228379746668465238 rfl endpoint_9_66_base endpoint_9_66_p8) (by decide)⟩
private def endpoint_9_67_flag : Flag := ⟨9, 67, 2891⟩
private def endpoint_9_67_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_9_67_base : receiptBase endpoint_9_67_flag endpoint_9_67_sources = some 227318529260150948 := by decide +kernel
private theorem endpoint_9_67_w0 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 2 227318529260150948 = some 227318529260150948 := by decide +kernel
private theorem endpoint_9_67_w2 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 2 2 227318529260150948 = some 227318529260150948 := by decide +kernel
private theorem endpoint_9_67_p4 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 4 227318529260150948 = some 227318529260150948 :=
  join_receipt_window endpoint_9_67_flag endpoint_9_67_sources 0 2 2 227318529260150948 227318529260150948 227318529260150948 endpoint_9_67_w0 endpoint_9_67_w2
private theorem endpoint_9_67_w4 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 4 2 227318529260150948 = some 227318529260150948 := by decide +kernel
private theorem endpoint_9_67_p6 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 6 227318529260150948 = some 227318529260150948 :=
  join_receipt_window endpoint_9_67_flag endpoint_9_67_sources 0 4 2 227318529260150948 227318529260150948 227318529260150948 endpoint_9_67_p4 endpoint_9_67_w4
private theorem endpoint_9_67_w6 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 6 2 227318529260150948 = some 227318529260150948 := by decide +kernel
private theorem endpoint_9_67_p8 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 8 227318529260150948 = some 227318529260150948 :=
  join_receipt_window endpoint_9_67_flag endpoint_9_67_sources 0 6 2 227318529260150948 227318529260150948 227318529260150948 endpoint_9_67_p6 endpoint_9_67_w6
def endpoint_9_67 : CertifiedEndpoint :=
  ⟨⟨9, 67, 2891⟩, 227318529260150948, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_9_67_flag endpoint_9_67_sources 8 227318529260150948 227318529260150948 rfl endpoint_9_67_base endpoint_9_67_p8) (by decide)⟩
private def endpoint_9_68_flag : Flag := ⟨9, 68, 2835⟩
private def endpoint_9_68_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_9_68_base : receiptBase endpoint_9_68_flag endpoint_9_68_sources = some 227293512554425268 := by decide +kernel
private theorem endpoint_9_68_w0 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 2 227293512554425268 = some 227293512554425268 := by decide +kernel
private theorem endpoint_9_68_w2 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 2 2 227293512554425268 = some 227293512554425268 := by decide +kernel
private theorem endpoint_9_68_p4 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 4 227293512554425268 = some 227293512554425268 :=
  join_receipt_window endpoint_9_68_flag endpoint_9_68_sources 0 2 2 227293512554425268 227293512554425268 227293512554425268 endpoint_9_68_w0 endpoint_9_68_w2
private theorem endpoint_9_68_w4 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 4 2 227293512554425268 = some 227293512554425268 := by decide +kernel
private theorem endpoint_9_68_p6 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 6 227293512554425268 = some 227293512554425268 :=
  join_receipt_window endpoint_9_68_flag endpoint_9_68_sources 0 4 2 227293512554425268 227293512554425268 227293512554425268 endpoint_9_68_p4 endpoint_9_68_w4
private theorem endpoint_9_68_w6 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 6 2 227293512554425268 = some 227293512554425268 := by decide +kernel
private theorem endpoint_9_68_p8 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 8 227293512554425268 = some 227293512554425268 :=
  join_receipt_window endpoint_9_68_flag endpoint_9_68_sources 0 6 2 227293512554425268 227293512554425268 227293512554425268 endpoint_9_68_p6 endpoint_9_68_w6
def endpoint_9_68 : CertifiedEndpoint :=
  ⟨⟨9, 68, 2835⟩, 227293512554425268, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_9_68_flag endpoint_9_68_sources 8 227293512554425268 227293512554425268 rfl endpoint_9_68_base endpoint_9_68_p8) (by decide)⟩
private def endpoint_9_69_flag : Flag := ⟨9, 69, 2776⟩
private def endpoint_9_69_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_9_69_base : receiptBase endpoint_9_69_flag endpoint_9_69_sources = some 226928529086588715 := by decide +kernel
private theorem endpoint_9_69_w0 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 2 226928529086588715 = some 226928529086588715 := by decide +kernel
private theorem endpoint_9_69_w2 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 2 2 226928529086588715 = some 226928529086588715 := by decide +kernel
private theorem endpoint_9_69_p4 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 4 226928529086588715 = some 226928529086588715 :=
  join_receipt_window endpoint_9_69_flag endpoint_9_69_sources 0 2 2 226928529086588715 226928529086588715 226928529086588715 endpoint_9_69_w0 endpoint_9_69_w2
private theorem endpoint_9_69_w4 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 4 2 226928529086588715 = some 226928529086588715 := by decide +kernel
private theorem endpoint_9_69_p6 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 6 226928529086588715 = some 226928529086588715 :=
  join_receipt_window endpoint_9_69_flag endpoint_9_69_sources 0 4 2 226928529086588715 226928529086588715 226928529086588715 endpoint_9_69_p4 endpoint_9_69_w4
private theorem endpoint_9_69_w6 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 6 2 226928529086588715 = some 226928529086588715 := by decide +kernel
private theorem endpoint_9_69_p8 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 8 226928529086588715 = some 226928529086588715 :=
  join_receipt_window endpoint_9_69_flag endpoint_9_69_sources 0 6 2 226928529086588715 226928529086588715 226928529086588715 endpoint_9_69_p6 endpoint_9_69_w6
def endpoint_9_69 : CertifiedEndpoint :=
  ⟨⟨9, 69, 2776⟩, 226928529086588715, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_9_69_flag endpoint_9_69_sources 8 226928529086588715 226928529086588715 rfl endpoint_9_69_base endpoint_9_69_p8) (by decide)⟩
private def endpoint_9_70_flag : Flag := ⟨9, 70, 2715⟩
private def endpoint_9_70_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_9_70_base : receiptBase endpoint_9_70_flag endpoint_9_70_sources = some 226150668695884189 := by decide +kernel
private theorem endpoint_9_70_w0 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 2 226150668695884189 = some 226150668695884189 := by decide +kernel
private theorem endpoint_9_70_w2 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 2 2 226150668695884189 = some 226150668695884189 := by decide +kernel
private theorem endpoint_9_70_p4 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 4 226150668695884189 = some 226150668695884189 :=
  join_receipt_window endpoint_9_70_flag endpoint_9_70_sources 0 2 2 226150668695884189 226150668695884189 226150668695884189 endpoint_9_70_w0 endpoint_9_70_w2
private theorem endpoint_9_70_w4 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 4 2 226150668695884189 = some 226150668695884189 := by decide +kernel
private theorem endpoint_9_70_p6 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 6 226150668695884189 = some 226150668695884189 :=
  join_receipt_window endpoint_9_70_flag endpoint_9_70_sources 0 4 2 226150668695884189 226150668695884189 226150668695884189 endpoint_9_70_p4 endpoint_9_70_w4
private theorem endpoint_9_70_w6 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 6 2 226150668695884189 = some 226150668695884189 := by decide +kernel
private theorem endpoint_9_70_p8 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 8 226150668695884189 = some 226150668695884189 :=
  join_receipt_window endpoint_9_70_flag endpoint_9_70_sources 0 6 2 226150668695884189 226150668695884189 226150668695884189 endpoint_9_70_p6 endpoint_9_70_w6
def endpoint_9_70 : CertifiedEndpoint :=
  ⟨⟨9, 70, 2715⟩, 226150668695884189, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_9_70_flag endpoint_9_70_sources 8 226150668695884189 226150668695884189 rfl endpoint_9_70_base endpoint_9_70_p8) (by decide)⟩
private def endpoint_9_71_flag : Flag := ⟨9, 71, 2652⟩
private def endpoint_9_71_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_9_71_base : receiptBase endpoint_9_71_flag endpoint_9_71_sources = some 223769400208513182 := by decide +kernel
private theorem endpoint_9_71_w0 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 2 223769400208513182 = some 223769400208513182 := by decide +kernel
private theorem endpoint_9_71_w2 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 2 2 223769400208513182 = some 223769400208513182 := by decide +kernel
private theorem endpoint_9_71_p4 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 4 223769400208513182 = some 223769400208513182 :=
  join_receipt_window endpoint_9_71_flag endpoint_9_71_sources 0 2 2 223769400208513182 223769400208513182 223769400208513182 endpoint_9_71_w0 endpoint_9_71_w2
private theorem endpoint_9_71_w4 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 4 2 223769400208513182 = some 223769400208513182 := by decide +kernel
private theorem endpoint_9_71_p6 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 6 223769400208513182 = some 223769400208513182 :=
  join_receipt_window endpoint_9_71_flag endpoint_9_71_sources 0 4 2 223769400208513182 223769400208513182 223769400208513182 endpoint_9_71_p4 endpoint_9_71_w4
private theorem endpoint_9_71_w6 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 6 2 223769400208513182 = some 223769400208513182 := by decide +kernel
private theorem endpoint_9_71_p8 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 8 223769400208513182 = some 223769400208513182 :=
  join_receipt_window endpoint_9_71_flag endpoint_9_71_sources 0 6 2 223769400208513182 223769400208513182 223769400208513182 endpoint_9_71_p6 endpoint_9_71_w6
def endpoint_9_71 : CertifiedEndpoint :=
  ⟨⟨9, 71, 2652⟩, 223769400208513182, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_9_71_flag endpoint_9_71_sources 8 223769400208513182 223769400208513182 rfl endpoint_9_71_base endpoint_9_71_p8) (by decide)⟩
private def endpoint_9_72_flag : Flag := ⟨9, 72, 2585⟩
private def endpoint_9_72_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_9_72_base : receiptBase endpoint_9_72_flag endpoint_9_72_sources = some 220914195400271549 := by decide +kernel
private theorem endpoint_9_72_w0 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 2 220914195400271549 = some 220914195400271549 := by decide +kernel
private theorem endpoint_9_72_w2 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 2 2 220914195400271549 = some 220914195400271549 := by decide +kernel
private theorem endpoint_9_72_p4 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 4 220914195400271549 = some 220914195400271549 :=
  join_receipt_window endpoint_9_72_flag endpoint_9_72_sources 0 2 2 220914195400271549 220914195400271549 220914195400271549 endpoint_9_72_w0 endpoint_9_72_w2
private theorem endpoint_9_72_w4 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 4 2 220914195400271549 = some 220914195400271549 := by decide +kernel
private theorem endpoint_9_72_p6 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 6 220914195400271549 = some 220914195400271549 :=
  join_receipt_window endpoint_9_72_flag endpoint_9_72_sources 0 4 2 220914195400271549 220914195400271549 220914195400271549 endpoint_9_72_p4 endpoint_9_72_w4
private theorem endpoint_9_72_w6 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 6 2 220914195400271549 = some 220914195400271549 := by decide +kernel
private theorem endpoint_9_72_p8 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 8 220914195400271549 = some 220914195400271549 :=
  join_receipt_window endpoint_9_72_flag endpoint_9_72_sources 0 6 2 220914195400271549 220914195400271549 220914195400271549 endpoint_9_72_p6 endpoint_9_72_w6
def endpoint_9_72 : CertifiedEndpoint :=
  ⟨⟨9, 72, 2585⟩, 220914195400271549, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_9_72_flag endpoint_9_72_sources 8 220914195400271549 220914195400271549 rfl endpoint_9_72_base endpoint_9_72_p8) (by decide)⟩
private def endpoint_9_73_flag : Flag := ⟨9, 73, 2517⟩
private def endpoint_9_73_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_9_73_base : receiptBase endpoint_9_73_flag endpoint_9_73_sources = some 222299156562870471 := by decide +kernel
private theorem endpoint_9_73_w0 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 2 222299156562870471 = some 222299156562870471 := by decide +kernel
private theorem endpoint_9_73_w2 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 2 2 222299156562870471 = some 222299156562870471 := by decide +kernel
private theorem endpoint_9_73_p4 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 4 222299156562870471 = some 222299156562870471 :=
  join_receipt_window endpoint_9_73_flag endpoint_9_73_sources 0 2 2 222299156562870471 222299156562870471 222299156562870471 endpoint_9_73_w0 endpoint_9_73_w2
private theorem endpoint_9_73_w4 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 4 2 222299156562870471 = some 222299156562870471 := by decide +kernel
private theorem endpoint_9_73_p6 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 6 222299156562870471 = some 222299156562870471 :=
  join_receipt_window endpoint_9_73_flag endpoint_9_73_sources 0 4 2 222299156562870471 222299156562870471 222299156562870471 endpoint_9_73_p4 endpoint_9_73_w4
private theorem endpoint_9_73_w6 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 6 2 222299156562870471 = some 222299156562870471 := by decide +kernel
private theorem endpoint_9_73_p8 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 8 222299156562870471 = some 222299156562870471 :=
  join_receipt_window endpoint_9_73_flag endpoint_9_73_sources 0 6 2 222299156562870471 222299156562870471 222299156562870471 endpoint_9_73_p6 endpoint_9_73_w6
def endpoint_9_73 : CertifiedEndpoint :=
  ⟨⟨9, 73, 2517⟩, 222299156562870471, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_9_73_flag endpoint_9_73_sources 8 222299156562870471 222299156562870471 rfl endpoint_9_73_base endpoint_9_73_p8) (by decide)⟩
private def endpoint_9_74_flag : Flag := ⟨9, 74, 2445⟩
private def endpoint_9_74_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_9_74_base : receiptBase endpoint_9_74_flag endpoint_9_74_sources = some 218689719043102336 := by decide +kernel
private theorem endpoint_9_74_w0 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 2 218689719043102336 = some 218689719043102336 := by decide +kernel
private theorem endpoint_9_74_w2 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 2 2 218689719043102336 = some 218689719043102336 := by decide +kernel
private theorem endpoint_9_74_p4 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 4 218689719043102336 = some 218689719043102336 :=
  join_receipt_window endpoint_9_74_flag endpoint_9_74_sources 0 2 2 218689719043102336 218689719043102336 218689719043102336 endpoint_9_74_w0 endpoint_9_74_w2
private theorem endpoint_9_74_w4 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 4 2 218689719043102336 = some 218689719043102336 := by decide +kernel
private theorem endpoint_9_74_p6 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 6 218689719043102336 = some 218689719043102336 :=
  join_receipt_window endpoint_9_74_flag endpoint_9_74_sources 0 4 2 218689719043102336 218689719043102336 218689719043102336 endpoint_9_74_p4 endpoint_9_74_w4
private theorem endpoint_9_74_w6 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 6 2 218689719043102336 = some 218689719043102336 := by decide +kernel
private theorem endpoint_9_74_p8 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 8 218689719043102336 = some 218689719043102336 :=
  join_receipt_window endpoint_9_74_flag endpoint_9_74_sources 0 6 2 218689719043102336 218689719043102336 218689719043102336 endpoint_9_74_p6 endpoint_9_74_w6
def endpoint_9_74 : CertifiedEndpoint :=
  ⟨⟨9, 74, 2445⟩, 218689719043102336, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_9_74_flag endpoint_9_74_sources 8 218689719043102336 218689719043102336 rfl endpoint_9_74_base endpoint_9_74_p8) (by decide)⟩
private def endpoint_9_75_flag : Flag := ⟨9, 75, 2371⟩
private def endpoint_9_75_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_9_75_base : receiptBase endpoint_9_75_flag endpoint_9_75_sources = some 214747933719093336 := by decide +kernel
private theorem endpoint_9_75_w0 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 2 214747933719093336 = some 214747933719093336 := by decide +kernel
private theorem endpoint_9_75_w2 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 2 2 214747933719093336 = some 214747933719093336 := by decide +kernel
private theorem endpoint_9_75_p4 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 4 214747933719093336 = some 214747933719093336 :=
  join_receipt_window endpoint_9_75_flag endpoint_9_75_sources 0 2 2 214747933719093336 214747933719093336 214747933719093336 endpoint_9_75_w0 endpoint_9_75_w2
private theorem endpoint_9_75_w4 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 4 2 214747933719093336 = some 214747933719093336 := by decide +kernel
private theorem endpoint_9_75_p6 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 6 214747933719093336 = some 214747933719093336 :=
  join_receipt_window endpoint_9_75_flag endpoint_9_75_sources 0 4 2 214747933719093336 214747933719093336 214747933719093336 endpoint_9_75_p4 endpoint_9_75_w4
private theorem endpoint_9_75_w6 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 6 2 214747933719093336 = some 214747933719093336 := by decide +kernel
private theorem endpoint_9_75_p8 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 8 214747933719093336 = some 214747933719093336 :=
  join_receipt_window endpoint_9_75_flag endpoint_9_75_sources 0 6 2 214747933719093336 214747933719093336 214747933719093336 endpoint_9_75_p6 endpoint_9_75_w6
def endpoint_9_75 : CertifiedEndpoint :=
  ⟨⟨9, 75, 2371⟩, 214747933719093336, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_9_75_flag endpoint_9_75_sources 8 214747933719093336 214747933719093336 rfl endpoint_9_75_base endpoint_9_75_p8) (by decide)⟩
private def endpoint_9_76_flag : Flag := ⟨9, 76, 2294⟩
private def endpoint_9_76_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_9_76_base : receiptBase endpoint_9_76_flag endpoint_9_76_sources = some 212294555967146934 := by decide +kernel
private theorem endpoint_9_76_w0 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 2 212294555967146934 = some 212294555967146934 := by decide +kernel
private theorem endpoint_9_76_w2 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 2 2 212294555967146934 = some 212294555967146934 := by decide +kernel
private theorem endpoint_9_76_p4 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 4 212294555967146934 = some 212294555967146934 :=
  join_receipt_window endpoint_9_76_flag endpoint_9_76_sources 0 2 2 212294555967146934 212294555967146934 212294555967146934 endpoint_9_76_w0 endpoint_9_76_w2
private theorem endpoint_9_76_w4 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 4 2 212294555967146934 = some 212294555967146934 := by decide +kernel
private theorem endpoint_9_76_p6 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 6 212294555967146934 = some 212294555967146934 :=
  join_receipt_window endpoint_9_76_flag endpoint_9_76_sources 0 4 2 212294555967146934 212294555967146934 212294555967146934 endpoint_9_76_p4 endpoint_9_76_w4
private theorem endpoint_9_76_w6 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 6 2 212294555967146934 = some 212294555967146934 := by decide +kernel
private theorem endpoint_9_76_p8 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 8 212294555967146934 = some 212294555967146934 :=
  join_receipt_window endpoint_9_76_flag endpoint_9_76_sources 0 6 2 212294555967146934 212294555967146934 212294555967146934 endpoint_9_76_p6 endpoint_9_76_w6
def endpoint_9_76 : CertifiedEndpoint :=
  ⟨⟨9, 76, 2294⟩, 212294555967146934, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_9_76_flag endpoint_9_76_sources 8 212294555967146934 212294555967146934 rfl endpoint_9_76_base endpoint_9_76_p8) (by decide)⟩
private def endpoint_9_77_flag : Flag := ⟨9, 77, 2214⟩
private def endpoint_9_77_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_9_77_base : receiptBase endpoint_9_77_flag endpoint_9_77_sources = some 207369834786056186 := by decide +kernel
private theorem endpoint_9_77_w0 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 2 207369834786056186 = some 207369834786056186 := by decide +kernel
private theorem endpoint_9_77_w2 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 2 2 207369834786056186 = some 207369834786056186 := by decide +kernel
private theorem endpoint_9_77_p4 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 4 207369834786056186 = some 207369834786056186 :=
  join_receipt_window endpoint_9_77_flag endpoint_9_77_sources 0 2 2 207369834786056186 207369834786056186 207369834786056186 endpoint_9_77_w0 endpoint_9_77_w2
private theorem endpoint_9_77_w4 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 4 2 207369834786056186 = some 207369834786056186 := by decide +kernel
private theorem endpoint_9_77_p6 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 6 207369834786056186 = some 207369834786056186 :=
  join_receipt_window endpoint_9_77_flag endpoint_9_77_sources 0 4 2 207369834786056186 207369834786056186 207369834786056186 endpoint_9_77_p4 endpoint_9_77_w4
private theorem endpoint_9_77_w6 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 6 2 207369834786056186 = some 207369834786056186 := by decide +kernel
private theorem endpoint_9_77_p8 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 8 207369834786056186 = some 207369834786056186 :=
  join_receipt_window endpoint_9_77_flag endpoint_9_77_sources 0 6 2 207369834786056186 207369834786056186 207369834786056186 endpoint_9_77_p6 endpoint_9_77_w6
def endpoint_9_77 : CertifiedEndpoint :=
  ⟨⟨9, 77, 2214⟩, 207369834786056186, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_9_77_flag endpoint_9_77_sources 8 207369834786056186 207369834786056186 rfl endpoint_9_77_base endpoint_9_77_p8) (by decide)⟩
private def endpoint_9_78_flag : Flag := ⟨9, 78, 2132⟩
private def endpoint_9_78_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_9_78_base : receiptBase endpoint_9_78_flag endpoint_9_78_sources = some 202083528775653016 := by decide +kernel
private theorem endpoint_9_78_w0 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 2 202083528775653016 = some 202083528775653016 := by decide +kernel
private theorem endpoint_9_78_w2 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 2 2 202083528775653016 = some 202083528775653016 := by decide +kernel
private theorem endpoint_9_78_p4 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 4 202083528775653016 = some 202083528775653016 :=
  join_receipt_window endpoint_9_78_flag endpoint_9_78_sources 0 2 2 202083528775653016 202083528775653016 202083528775653016 endpoint_9_78_w0 endpoint_9_78_w2
private theorem endpoint_9_78_w4 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 4 2 202083528775653016 = some 202083528775653016 := by decide +kernel
private theorem endpoint_9_78_p6 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 6 202083528775653016 = some 202083528775653016 :=
  join_receipt_window endpoint_9_78_flag endpoint_9_78_sources 0 4 2 202083528775653016 202083528775653016 202083528775653016 endpoint_9_78_p4 endpoint_9_78_w4
private theorem endpoint_9_78_w6 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 6 2 202083528775653016 = some 202083528775653016 := by decide +kernel
private theorem endpoint_9_78_p8 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 8 202083528775653016 = some 202083528775653016 :=
  join_receipt_window endpoint_9_78_flag endpoint_9_78_sources 0 6 2 202083528775653016 202083528775653016 202083528775653016 endpoint_9_78_p6 endpoint_9_78_w6
def endpoint_9_78 : CertifiedEndpoint :=
  ⟨⟨9, 78, 2132⟩, 202083528775653016, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_9_78_flag endpoint_9_78_sources 8 202083528775653016 202083528775653016 rfl endpoint_9_78_base endpoint_9_78_p8) (by decide)⟩
private def endpoint_9_79_flag : Flag := ⟨9, 79, 2047⟩
private def endpoint_9_79_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_9_79_base : receiptBase endpoint_9_79_flag endpoint_9_79_sources = some 198285549678438552 := by decide +kernel
private theorem endpoint_9_79_w0 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 2 198285549678438552 = some 198285549678438552 := by decide +kernel
private theorem endpoint_9_79_w2 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 2 2 198285549678438552 = some 198285549678438552 := by decide +kernel
private theorem endpoint_9_79_p4 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 4 198285549678438552 = some 198285549678438552 :=
  join_receipt_window endpoint_9_79_flag endpoint_9_79_sources 0 2 2 198285549678438552 198285549678438552 198285549678438552 endpoint_9_79_w0 endpoint_9_79_w2
private theorem endpoint_9_79_w4 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 4 2 198285549678438552 = some 198285549678438552 := by decide +kernel
private theorem endpoint_9_79_p6 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 6 198285549678438552 = some 198285549678438552 :=
  join_receipt_window endpoint_9_79_flag endpoint_9_79_sources 0 4 2 198285549678438552 198285549678438552 198285549678438552 endpoint_9_79_p4 endpoint_9_79_w4
private theorem endpoint_9_79_w6 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 6 2 198285549678438552 = some 198285549678438552 := by decide +kernel
private theorem endpoint_9_79_p8 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 8 198285549678438552 = some 198285549678438552 :=
  join_receipt_window endpoint_9_79_flag endpoint_9_79_sources 0 6 2 198285549678438552 198285549678438552 198285549678438552 endpoint_9_79_p6 endpoint_9_79_w6
def endpoint_9_79 : CertifiedEndpoint :=
  ⟨⟨9, 79, 2047⟩, 198285549678438552, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_9_79_flag endpoint_9_79_sources 8 198285549678438552 198285549678438552 rfl endpoint_9_79_base endpoint_9_79_p8) (by decide)⟩
private def endpoint_9_80_flag : Flag := ⟨9, 80, 1960⟩
private def endpoint_9_80_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_80_base : receiptBase endpoint_9_80_flag endpoint_9_80_sources = some 194053120697039905 := by decide +kernel
private theorem endpoint_9_80_w0 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 2 194053120697039905 = some 194053120697039905 := by decide +kernel
private theorem endpoint_9_80_w2 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 2 2 194053120697039905 = some 194053120697039905 := by decide +kernel
private theorem endpoint_9_80_p4 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 4 194053120697039905 = some 194053120697039905 :=
  join_receipt_window endpoint_9_80_flag endpoint_9_80_sources 0 2 2 194053120697039905 194053120697039905 194053120697039905 endpoint_9_80_w0 endpoint_9_80_w2
private theorem endpoint_9_80_w4 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 4 2 194053120697039905 = some 194053120697039905 := by decide +kernel
private theorem endpoint_9_80_p6 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 6 194053120697039905 = some 194053120697039905 :=
  join_receipt_window endpoint_9_80_flag endpoint_9_80_sources 0 4 2 194053120697039905 194053120697039905 194053120697039905 endpoint_9_80_p4 endpoint_9_80_w4
private theorem endpoint_9_80_w6 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 6 2 194053120697039905 = some 194053120697039905 := by decide +kernel
private theorem endpoint_9_80_p8 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 8 194053120697039905 = some 194053120697039905 :=
  join_receipt_window endpoint_9_80_flag endpoint_9_80_sources 0 6 2 194053120697039905 194053120697039905 194053120697039905 endpoint_9_80_p6 endpoint_9_80_w6
def endpoint_9_80 : CertifiedEndpoint :=
  ⟨⟨9, 80, 1960⟩, 194053120697039905, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_80_flag endpoint_9_80_sources 8 194053120697039905 194053120697039905 rfl endpoint_9_80_base endpoint_9_80_p8) (by decide)⟩
private def endpoint_9_81_flag : Flag := ⟨9, 81, 1870⟩
private def endpoint_9_81_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_81_base : receiptBase endpoint_9_81_flag endpoint_9_81_sources = some 187272260433182256 := by decide +kernel
private theorem endpoint_9_81_w0 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 2 187272260433182256 = some 187272260433182256 := by decide +kernel
private theorem endpoint_9_81_w2 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 2 2 187272260433182256 = some 187272260433182256 := by decide +kernel
private theorem endpoint_9_81_p4 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 4 187272260433182256 = some 187272260433182256 :=
  join_receipt_window endpoint_9_81_flag endpoint_9_81_sources 0 2 2 187272260433182256 187272260433182256 187272260433182256 endpoint_9_81_w0 endpoint_9_81_w2
private theorem endpoint_9_81_w4 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 4 2 187272260433182256 = some 187272260433182256 := by decide +kernel
private theorem endpoint_9_81_p6 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 6 187272260433182256 = some 187272260433182256 :=
  join_receipt_window endpoint_9_81_flag endpoint_9_81_sources 0 4 2 187272260433182256 187272260433182256 187272260433182256 endpoint_9_81_p4 endpoint_9_81_w4
private theorem endpoint_9_81_w6 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 6 2 187272260433182256 = some 187272260433182256 := by decide +kernel
private theorem endpoint_9_81_p8 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 8 187272260433182256 = some 187272260433182256 :=
  join_receipt_window endpoint_9_81_flag endpoint_9_81_sources 0 6 2 187272260433182256 187272260433182256 187272260433182256 endpoint_9_81_p6 endpoint_9_81_w6
def endpoint_9_81 : CertifiedEndpoint :=
  ⟨⟨9, 81, 1870⟩, 187272260433182256, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_81_flag endpoint_9_81_sources 8 187272260433182256 187272260433182256 rfl endpoint_9_81_base endpoint_9_81_p8) (by decide)⟩
private def endpoint_9_82_flag : Flag := ⟨9, 82, 1777⟩
private def endpoint_9_82_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_82_base : receiptBase endpoint_9_82_flag endpoint_9_82_sources = some 179988318035126564 := by decide +kernel
private theorem endpoint_9_82_w0 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 2 179988318035126564 = some 179988318035126564 := by decide +kernel
private theorem endpoint_9_82_w2 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 2 2 179988318035126564 = some 179988318035126564 := by decide +kernel
private theorem endpoint_9_82_p4 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 4 179988318035126564 = some 179988318035126564 :=
  join_receipt_window endpoint_9_82_flag endpoint_9_82_sources 0 2 2 179988318035126564 179988318035126564 179988318035126564 endpoint_9_82_w0 endpoint_9_82_w2
private theorem endpoint_9_82_w4 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 4 2 179988318035126564 = some 179988318035126564 := by decide +kernel
private theorem endpoint_9_82_p6 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 6 179988318035126564 = some 179988318035126564 :=
  join_receipt_window endpoint_9_82_flag endpoint_9_82_sources 0 4 2 179988318035126564 179988318035126564 179988318035126564 endpoint_9_82_p4 endpoint_9_82_w4
private theorem endpoint_9_82_w6 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 6 2 179988318035126564 = some 179988318035126564 := by decide +kernel
private theorem endpoint_9_82_p8 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 8 179988318035126564 = some 179988318035126564 :=
  join_receipt_window endpoint_9_82_flag endpoint_9_82_sources 0 6 2 179988318035126564 179988318035126564 179988318035126564 endpoint_9_82_p6 endpoint_9_82_w6
def endpoint_9_82 : CertifiedEndpoint :=
  ⟨⟨9, 82, 1777⟩, 179988318035126564, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_82_flag endpoint_9_82_sources 8 179988318035126564 179988318035126564 rfl endpoint_9_82_base endpoint_9_82_p8) (by decide)⟩
private def endpoint_9_83_flag : Flag := ⟨9, 83, 1681⟩
private def endpoint_9_83_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_83_base : receiptBase endpoint_9_83_flag endpoint_9_83_sources = some 172191267956078112 := by decide +kernel
private theorem endpoint_9_83_w0 : receiptWindow endpoint_9_83_flag endpoint_9_83_sources 0 2 172191267956078112 = some 172191267956078112 := by decide +kernel
private theorem endpoint_9_83_w2 : receiptWindow endpoint_9_83_flag endpoint_9_83_sources 2 2 172191267956078112 = some 172191267956078112 := by decide +kernel
private theorem endpoint_9_83_p4 : receiptWindow endpoint_9_83_flag endpoint_9_83_sources 0 4 172191267956078112 = some 172191267956078112 :=
  join_receipt_window endpoint_9_83_flag endpoint_9_83_sources 0 2 2 172191267956078112 172191267956078112 172191267956078112 endpoint_9_83_w0 endpoint_9_83_w2
private theorem endpoint_9_83_w4 : receiptWindow endpoint_9_83_flag endpoint_9_83_sources 4 2 172191267956078112 = some 172191267956078112 := by decide +kernel
private theorem endpoint_9_83_p6 : receiptWindow endpoint_9_83_flag endpoint_9_83_sources 0 6 172191267956078112 = some 172191267956078112 :=
  join_receipt_window endpoint_9_83_flag endpoint_9_83_sources 0 4 2 172191267956078112 172191267956078112 172191267956078112 endpoint_9_83_p4 endpoint_9_83_w4
private theorem endpoint_9_83_w6 : receiptWindow endpoint_9_83_flag endpoint_9_83_sources 6 2 172191267956078112 = some 172191267956078112 := by decide +kernel
private theorem endpoint_9_83_p8 : receiptWindow endpoint_9_83_flag endpoint_9_83_sources 0 8 172191267956078112 = some 172191267956078112 :=
  join_receipt_window endpoint_9_83_flag endpoint_9_83_sources 0 6 2 172191267956078112 172191267956078112 172191267956078112 endpoint_9_83_p6 endpoint_9_83_w6
def endpoint_9_83 : CertifiedEndpoint :=
  ⟨⟨9, 83, 1681⟩, 172191267956078112, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_83_flag endpoint_9_83_sources 8 172191267956078112 172191267956078112 rfl endpoint_9_83_base endpoint_9_83_p8) (by decide)⟩
private def endpoint_9_84_flag : Flag := ⟨9, 84, 1583⟩
private def endpoint_9_84_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_84_base : receiptBase endpoint_9_84_flag endpoint_9_84_sources = some 163973798298083179 := by decide +kernel
private theorem endpoint_9_84_w0 : receiptWindow endpoint_9_84_flag endpoint_9_84_sources 0 2 163973798298083179 = some 163973798298083179 := by decide +kernel
private theorem endpoint_9_84_w2 : receiptWindow endpoint_9_84_flag endpoint_9_84_sources 2 2 163973798298083179 = some 163973798298083179 := by decide +kernel
private theorem endpoint_9_84_p4 : receiptWindow endpoint_9_84_flag endpoint_9_84_sources 0 4 163973798298083179 = some 163973798298083179 :=
  join_receipt_window endpoint_9_84_flag endpoint_9_84_sources 0 2 2 163973798298083179 163973798298083179 163973798298083179 endpoint_9_84_w0 endpoint_9_84_w2
private theorem endpoint_9_84_w4 : receiptWindow endpoint_9_84_flag endpoint_9_84_sources 4 2 163973798298083179 = some 163973798298083179 := by decide +kernel
private theorem endpoint_9_84_p6 : receiptWindow endpoint_9_84_flag endpoint_9_84_sources 0 6 163973798298083179 = some 163973798298083179 :=
  join_receipt_window endpoint_9_84_flag endpoint_9_84_sources 0 4 2 163973798298083179 163973798298083179 163973798298083179 endpoint_9_84_p4 endpoint_9_84_w4
private theorem endpoint_9_84_w6 : receiptWindow endpoint_9_84_flag endpoint_9_84_sources 6 2 163973798298083179 = some 163973798298083179 := by decide +kernel
private theorem endpoint_9_84_p8 : receiptWindow endpoint_9_84_flag endpoint_9_84_sources 0 8 163973798298083179 = some 163973798298083179 :=
  join_receipt_window endpoint_9_84_flag endpoint_9_84_sources 0 6 2 163973798298083179 163973798298083179 163973798298083179 endpoint_9_84_p6 endpoint_9_84_w6
def endpoint_9_84 : CertifiedEndpoint :=
  ⟨⟨9, 84, 1583⟩, 163973798298083179, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_84_flag endpoint_9_84_sources 8 163973798298083179 163973798298083179 rfl endpoint_9_84_base endpoint_9_84_p8) (by decide)⟩
def endpoint_9_85 : CertifiedEndpoint :=
  ⟨⟨9, 85, 1482⟩, 252825460477192685, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_86 : CertifiedEndpoint :=
  ⟨⟨9, 86, 1379⟩, 237548672943625659, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_87 : CertifiedEndpoint :=
  ⟨⟨9, 87, 1272⟩, 221095343845772391, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_88 : CertifiedEndpoint :=
  ⟨⟨9, 88, 1163⟩, 203804148533401139, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_89 : CertifiedEndpoint :=
  ⟨⟨9, 89, 1052⟩, 185661892534315875, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_90 : CertifiedEndpoint :=
  ⟨⟨9, 90, 937⟩, 166281520767362905, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_91 : CertifiedEndpoint :=
  ⟨⟨9, 91, 820⟩, 146014903054506515, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_92 : CertifiedEndpoint :=
  ⟨⟨9, 92, 700⟩, 124657516461673168, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_93 : CertifiedEndpoint :=
  ⟨⟨9, 93, 578⟩, 102383096821145669, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_94 : CertifiedEndpoint :=
  ⟨⟨9, 94, 452⟩, 78786996422175620, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_95 : CertifiedEndpoint :=
  ⟨⟨9, 95, 325⟩, 54436603414297534, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_96 : CertifiedEndpoint :=
  ⟨⟨9, 96, 194⟩, 28724946231388814, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_10 : CertifiedEndpoint :=
  ⟨⟨10, 10, 4386⟩, 62959083722445946, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_11 : CertifiedEndpoint :=
  ⟨⟨10, 11, 4368⟩, 66180184827402748, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_12 : CertifiedEndpoint :=
  ⟨⟨10, 12, 4349⟩, 69356548390061039, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_13 : CertifiedEndpoint :=
  ⟨⟨10, 13, 4330⟩, 79660132672757155, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_14 : CertifiedEndpoint :=
  ⟨⟨10, 14, 4311⟩, 89867902417338261, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_15 : CertifiedEndpoint :=
  ⟨⟨10, 15, 4292⟩, 99979857623804357, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_16 : CertifiedEndpoint :=
  ⟨⟨10, 16, 4273⟩, 109995998292155443, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_17 : CertifiedEndpoint :=
  ⟨⟨10, 17, 4253⟩, 119888062799709558, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_18 : CertifiedEndpoint :=
  ⟨⟨10, 18, 4234⟩, 129710117608802034, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_19 : CertifiedEndpoint :=
  ⟨⟨10, 19, 4214⟩, 139403182691040359, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_20 : CertifiedEndpoint :=
  ⟨⟨10, 20, 4194⟩, 148995519669106494, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_21 : CertifiedEndpoint :=
  ⟨⟨10, 21, 4174⟩, 158487128543000439, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_22 : CertifiedEndpoint :=
  ⟨⟨10, 22, 4153⟩, 167837463774897283, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_23 : CertifiedEndpoint :=
  ⟨⟨10, 23, 4133⟩, 177125159657418258, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_24 : CertifiedEndpoint :=
  ⟨⟨10, 24, 4112⟩, 186266668331884952, .intrinsic (by decide +kernel) (by decide)⟩

def endpointBlock06 : List CertifiedEndpoint := [
  endpoint_8_75, endpoint_8_76, endpoint_8_77, endpoint_8_78, endpoint_8_79, endpoint_8_80, endpoint_8_81,
  endpoint_8_82, endpoint_8_83, endpoint_8_84, endpoint_8_85, endpoint_8_86, endpoint_8_87, endpoint_8_88,
  endpoint_8_89, endpoint_8_90, endpoint_8_91, endpoint_8_92, endpoint_8_93, endpoint_8_94, endpoint_8_95,
  endpoint_8_96, endpoint_8_97, endpoint_8_98, endpoint_9_9, endpoint_9_10, endpoint_9_11, endpoint_9_12,
  endpoint_9_13, endpoint_9_14, endpoint_9_15, endpoint_9_16, endpoint_9_17, endpoint_9_18, endpoint_9_19,
  endpoint_9_20, endpoint_9_21, endpoint_9_22, endpoint_9_23, endpoint_9_24, endpoint_9_25, endpoint_9_26,
  endpoint_9_27, endpoint_9_28, endpoint_9_29, endpoint_9_30, endpoint_9_31, endpoint_9_32, endpoint_9_33,
  endpoint_9_34, endpoint_9_35, endpoint_9_36, endpoint_9_37, endpoint_9_38, endpoint_9_39, endpoint_9_40,
  endpoint_9_41, endpoint_9_42, endpoint_9_43, endpoint_9_44, endpoint_9_45, endpoint_9_46, endpoint_9_47,
  endpoint_9_48, endpoint_9_49, endpoint_9_50, endpoint_9_51, endpoint_9_52, endpoint_9_53, endpoint_9_54,
  endpoint_9_55, endpoint_9_56, endpoint_9_57, endpoint_9_58, endpoint_9_59, endpoint_9_60, endpoint_9_61,
  endpoint_9_62, endpoint_9_63, endpoint_9_64, endpoint_9_65, endpoint_9_66, endpoint_9_67, endpoint_9_68,
  endpoint_9_69, endpoint_9_70, endpoint_9_71, endpoint_9_72, endpoint_9_73, endpoint_9_74, endpoint_9_75,
  endpoint_9_76, endpoint_9_77, endpoint_9_78, endpoint_9_79, endpoint_9_80, endpoint_9_81, endpoint_9_82,
  endpoint_9_83, endpoint_9_84, endpoint_9_85, endpoint_9_86, endpoint_9_87, endpoint_9_88, endpoint_9_89,
  endpoint_9_90, endpoint_9_91, endpoint_9_92, endpoint_9_93, endpoint_9_94, endpoint_9_95, endpoint_9_96,
  endpoint_10_10, endpoint_10_11, endpoint_10_12, endpoint_10_13, endpoint_10_14, endpoint_10_15, endpoint_10_16,
  endpoint_10_17, endpoint_10_18, endpoint_10_19, endpoint_10_20, endpoint_10_21, endpoint_10_22, endpoint_10_23,
  endpoint_10_24
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
