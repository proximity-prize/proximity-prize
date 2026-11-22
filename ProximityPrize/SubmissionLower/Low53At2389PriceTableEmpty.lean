import ProximityPrize.SubmissionLower.Low53At2389PriceTableEmpty1
import ProximityPrize.SubmissionLower.Low53At2389PriceTableEmpty2
import ProximityPrize.SubmissionLower.Low53At2389PriceTableEmpty3
import ProximityPrize.SubmissionLower.Low53At2389PriceTableEmpty4
import ProximityPrize.SubmissionLower.Low53At2389PriceTableEmpty5
import ProximityPrize.SubmissionLower.Low53At2389PriceTableEmpty6
import ProximityPrize.SubmissionLower.Low53At2389PriceTableEmpty7
import ProximityPrize.SubmissionLower.Low53At2389PriceTableEmpty8
import ProximityPrize.SubmissionLower.Low53At2389PriceTableEmpty9
import ProximityPrize.SubmissionLower.Low53At2389PriceTableEmpty10
import ProximityPrize.SubmissionLower.Low53At2389PriceTableEmpty11
import ProximityPrize.SubmissionLower.Low53At2389PriceTableEmpty12
import ProximityPrize.SubmissionLower.Low53At2389PriceTableEmpty13

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableEmpty
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .empty).plus a) (fullCap top)) : Covered top .empty a := by
  change 0+a.b ≤ 129 ∧ 0+a.j ≤ 53 ∧ 0+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 129 := by omega
  have hj' : a.j ≤ 53 := by omega
  have hcases : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 ∨ a.t = 12 ∨ a.t = 13 := by omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · exact Certificate.apply Low53At2389PriceTableEmpty1.Top1.receipt a ha h1 hb' hj' ht htop
  · exact Certificate.apply Low53At2389PriceTableEmpty2.Top2.receipt a ha h2 hb' hj' ht htop
  · exact Certificate.apply Low53At2389PriceTableEmpty3.Top3.receipt a ha h3 hb' hj' ht htop
  · exact Certificate.apply Low53At2389PriceTableEmpty4.Top4.receipt a ha h4 hb' hj' ht htop
  · exact Certificate.apply Low53At2389PriceTableEmpty5.Top5.receipt a ha h5 hb' hj' ht htop
  · exact Certificate.apply Low53At2389PriceTableEmpty6.Top6.receipt a ha h6 hb' hj' ht htop
  · exact Certificate.apply Low53At2389PriceTableEmpty7.Top7.receipt a ha h7 hb' hj' ht htop
  · exact Certificate.apply Low53At2389PriceTableEmpty8.Top8.receipt a ha h8 hb' hj' ht htop
  · exact Certificate.apply Low53At2389PriceTableEmpty9.Top9.receipt a ha h9 hb' hj' ht htop
  · exact Certificate.apply Low53At2389PriceTableEmpty10.Top10.receipt a ha h10 hb' hj' ht htop
  · exact Certificate.apply Low53At2389PriceTableEmpty11.Top11.receipt a ha h11 hb' hj' ht htop
  · exact Certificate.apply Low53At2389PriceTableEmpty12.Top12.receipt a ha h12 hb' hj' ht htop
  · exact Certificate.apply Low53At2389PriceTableEmpty13.Top13.receipt a ha h13 hb' hj' ht htop

end Low53At2389PriceTableEmpty
