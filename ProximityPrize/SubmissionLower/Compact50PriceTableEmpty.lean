import ProximityPrize.SubmissionLower.Pr657PaidEmptyTop1
import ProximityPrize.SubmissionLower.Pr657PaidEmptyTop5
import ProximityPrize.SubmissionLower.Pr657PaidEmptyTop9
import ProximityPrize.SubmissionLower.Pr657PaidEmptyTop13
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableEmpty
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)

theorem price (top : ℕ) (htop : top ≤ 14) (a : Shape) (ha : Valid a)
    (hc:InBox ((start .empty).plus a) (fullCap top)):Covered top .empty a:=by
  change 0+a.b≤137 ∧ 0+a.j≤56 ∧ 0+a.t≤top at hc
  obtain ⟨hb,hj,ht⟩:=hc
  have ht0:=ha.1
  have hb' : a.b≤137:=by omega
  have hj' : a.j≤56:=by omega
  have h:a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 ∨ a.t=13 ∨ a.t=14:=by omega
  rcases h with e1 | e2 | e3 | e4 | e5 | e6 | e7 | e8 | e9 | e10 | e11 | e12 | e13 | e14
  · exact covered_mono (Pr657PaidEmptyTop1.price a ha e1 hb' hj') (by simpa only [start, e1] using ht) htop
  · exact covered_mono (Pr657PaidEmptyTop2.price a ha e2 hb' hj') (by simpa only [start, e2] using ht) htop
  · exact covered_mono (Pr657PaidEmptyTop3.price a ha e3 hb' hj') (by simpa only [start, e3] using ht) htop
  · exact covered_mono (Pr657PaidEmptyTop4.price a ha e4 hb' hj') (by simpa only [start, e4] using ht) htop
  · exact covered_mono (Pr657PaidEmptyTop5.price a ha e5 hb' hj') (by simpa only [start, e5] using ht) htop
  · exact covered_mono (Pr657PaidEmptyTop6.price a ha e6 hb' hj') (by simpa only [start, e6] using ht) htop
  · exact covered_mono (Pr657PaidEmptyTop7.price a ha e7 hb' hj') (by simpa only [start, e7] using ht) htop
  · exact covered_mono (Pr657PaidEmptyTop8.price a ha e8 hb' hj') (by simpa only [start, e8] using ht) htop
  · exact covered_mono (Pr657PaidEmptyTop9.price a ha e9 hb' hj') (by simpa only [start, e9] using ht) htop
  · exact covered_mono (Pr657PaidEmptyTop10.price a ha e10 hb' hj') (by simpa only [start, e10] using ht) htop
  · exact covered_mono (Pr657PaidEmptyTop11.price a ha e11 hb' hj') (by simpa only [start, e11] using ht) htop
  · exact covered_mono (Pr657PaidEmptyTop12.price a ha e12 hb' hj') (by simpa only [start, e12] using ht) htop
  · exact covered_mono (Pr657PaidEmptyTop13.price a ha e13 hb' hj') (by simpa only [start, e13] using ht) htop
  · exact covered_mono (Pr657PaidEmptyTop14.price a ha e14 hb' hj') (by simpa only [start, e14] using ht) htop
end Compact50PriceTableEmpty
