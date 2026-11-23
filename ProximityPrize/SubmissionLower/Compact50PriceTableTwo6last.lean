import ProximityPrize.SubmissionLower.Pr657PaidTwo6lastTop1
import ProximityPrize.SubmissionLower.Pr657PaidTwo6lastTop5
import ProximityPrize.SubmissionLower.Pr657PaidTwo6lastTop9
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6last
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)

theorem price (top : ℕ) (htop : top ≤ 14) (a : Shape) (ha : Valid a)
    (hc:InBox ((start .two6last).plus a) (fullCap top)):Covered top .two6last a:=by
  change 17+a.b≤137 ∧ 6+a.j≤56 ∧ 2+a.t≤top at hc
  obtain ⟨hb,hj,ht⟩:=hc
  have ht0:=ha.1
  have hb' : a.b≤120:=by omega
  have hj' : a.j≤50:=by omega
  have h:a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12:=by omega
  rcases h with e1 | e2 | e3 | e4 | e5 | e6 | e7 | e8 | e9 | e10 | e11 | e12
  · exact covered_mono (Pr657PaidTwo6lastTop1.price a ha e1 hb' hj') (by simpa only [start, e1] using ht) htop
  · exact covered_mono (Pr657PaidTwo6lastTop2.price a ha e2 hb' hj') (by simpa only [start, e2] using ht) htop
  · exact covered_mono (Pr657PaidTwo6lastTop3.price a ha e3 hb' hj') (by simpa only [start, e3] using ht) htop
  · exact covered_mono (Pr657PaidTwo6lastTop4.price a ha e4 hb' hj') (by simpa only [start, e4] using ht) htop
  · exact covered_mono (Pr657PaidTwo6lastTop5.price a ha e5 hb' hj') (by simpa only [start, e5] using ht) htop
  · exact covered_mono (Pr657PaidTwo6lastTop6.price a ha e6 hb' hj') (by simpa only [start, e6] using ht) htop
  · exact covered_mono (Pr657PaidTwo6lastTop7.price a ha e7 hb' hj') (by simpa only [start, e7] using ht) htop
  · exact covered_mono (Pr657PaidTwo6lastTop8.price a ha e8 hb' hj') (by simpa only [start, e8] using ht) htop
  · exact covered_mono (Pr657PaidTwo6lastTop9.price a ha e9 hb' hj') (by simpa only [start, e9] using ht) htop
  · exact covered_mono (Pr657PaidTwo6lastTop10.price a ha e10 hb' hj') (by simpa only [start, e10] using ht) htop
  · exact covered_mono (Pr657PaidTwo6lastTop11.price a ha e11 hb' hj') (by simpa only [start, e11] using ht) htop
  · exact covered_mono (Pr657PaidTwo6lastTop12.price a ha e12 hb' hj') (by simpa only [start, e12] using ht) htop
end Compact50PriceTableTwo6last
