import ProximityPrize.SubmissionLower.Pr657PaidTwo6widerTop1
import ProximityPrize.SubmissionLower.Pr657PaidTwo6widerTop5
import ProximityPrize.SubmissionLower.Pr657PaidTwo6widerTop9
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6wider
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)

theorem price (top : ℕ) (htop : top ≤ 14) (a : Shape) (ha : Valid a)
    (hc:InBox ((start .two6wider).plus a) (fullCap top)):Covered top .two6wider a:=by
  change 14+a.b≤137 ∧ 6+a.j≤56 ∧ 2+a.t≤top at hc
  obtain ⟨hb,hj,ht⟩:=hc
  have ht0:=ha.1
  have hb' : a.b≤123:=by omega
  have hj' : a.j≤50:=by omega
  have h:a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12:=by omega
  rcases h with e1 | e2 | e3 | e4 | e5 | e6 | e7 | e8 | e9 | e10 | e11 | e12
  · exact covered_mono (Pr657PaidTwo6widerTop1.price a ha e1 hb' hj') (by simpa only [start, e1] using ht) htop
  · exact covered_mono (Pr657PaidTwo6widerTop2.price a ha e2 hb' hj') (by simpa only [start, e2] using ht) htop
  · exact covered_mono (Pr657PaidTwo6widerTop3.price a ha e3 hb' hj') (by simpa only [start, e3] using ht) htop
  · exact covered_mono (Pr657PaidTwo6widerTop4.price a ha e4 hb' hj') (by simpa only [start, e4] using ht) htop
  · exact covered_mono (Pr657PaidTwo6widerTop5.price a ha e5 hb' hj') (by simpa only [start, e5] using ht) htop
  · exact covered_mono (Pr657PaidTwo6widerTop6.price a ha e6 hb' hj') (by simpa only [start, e6] using ht) htop
  · exact covered_mono (Pr657PaidTwo6widerTop7.price a ha e7 hb' hj') (by simpa only [start, e7] using ht) htop
  · exact covered_mono (Pr657PaidTwo6widerTop8.price a ha e8 hb' hj') (by simpa only [start, e8] using ht) htop
  · exact covered_mono (Pr657PaidTwo6widerTop9.price a ha e9 hb' hj') (by simpa only [start, e9] using ht) htop
  · exact covered_mono (Pr657PaidTwo6widerTop10.price a ha e10 hb' hj') (by simpa only [start, e10] using ht) htop
  · exact covered_mono (Pr657PaidTwo6widerTop11.price a ha e11 hb' hj') (by simpa only [start, e11] using ht) htop
  · exact covered_mono (Pr657PaidTwo6widerTop12.price a ha e12 hb' hj') (by simpa only [start, e12] using ht) htop
end Compact50PriceTableTwo6wider
