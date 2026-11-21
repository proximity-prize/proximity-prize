import ProximityPrize.SubmissionLower.Low52At2390PriceTableEmpty1
import ProximityPrize.SubmissionLower.Low52At2390PriceTableEmpty5
import ProximityPrize.SubmissionLower.Low52At2390PriceTableEmpty8
import ProximityPrize.SubmissionLower.Low52At2390PriceTableEmpty10
import ProximityPrize.SubmissionLower.Low52At2390PriceTableEmpty12

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low52At2390PriceTableEmpty
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low52At2390Price (fullCap)
open Low52At2390PriceCaps (Band start)
open Low52At2390PriceTableBase (Covered)
open Low52At2390PriceTableCover (PaidBatch packedBatch tilesOf checks checks_join Certificate)

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .empty).plus a) (fullCap top)) : Covered top .empty a := by
  change 0+a.b ≤ 127 ∧ 0+a.j ≤ 53 ∧ 0+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 127 := by omega
  have hj' : a.j ≤ 53 := by omega
  have hcases : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 ∨ a.t = 12 ∨ a.t = 13 := by omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · exact Certificate.apply Low52At2390PriceTableEmpty1.Top1.receipt a ha h1 hb' hj' ht htop
  · exact Certificate.apply Low52At2390PriceTableEmpty1.Top2.receipt a ha h2 hb' hj' ht htop
  · exact Certificate.apply Low52At2390PriceTableEmpty1.Top3.receipt a ha h3 hb' hj' ht htop
  · exact Certificate.apply Low52At2390PriceTableEmpty1.Top4.receipt a ha h4 hb' hj' ht htop
  · exact Certificate.apply Low52At2390PriceTableEmpty5.Top5.receipt a ha h5 hb' hj' ht htop
  · exact Certificate.apply Low52At2390PriceTableEmpty5.Top6.receipt a ha h6 hb' hj' ht htop
  · exact Certificate.apply Low52At2390PriceTableEmpty5.Top7.receipt a ha h7 hb' hj' ht htop
  · exact Certificate.apply Low52At2390PriceTableEmpty8.Top8.receipt a ha h8 hb' hj' ht htop
  · exact Certificate.apply Low52At2390PriceTableEmpty8.Top9.receipt a ha h9 hb' hj' ht htop
  · exact Certificate.apply Low52At2390PriceTableEmpty10.Top10.receipt a ha h10 hb' hj' ht htop
  · exact Certificate.apply Low52At2390PriceTableEmpty10.Top11.receipt a ha h11 hb' hj' ht htop
  · exact Certificate.apply Low52At2390PriceTableEmpty12.Top12.receipt a ha h12 hb' hj' ht htop
  · exact Certificate.apply Low52At2390PriceTableEmpty12.Top13.receipt a ha h13 hb' hj' ht htop

end Low52At2390PriceTableEmpty
