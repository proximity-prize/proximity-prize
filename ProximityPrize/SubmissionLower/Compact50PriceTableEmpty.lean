import ProximityPrize.SubmissionLower.Compact50PriceTableEmpty1
import ProximityPrize.SubmissionLower.Compact50PriceTableEmpty5
import ProximityPrize.SubmissionLower.Compact50PriceTableEmpty9

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered)

namespace Compact50PriceTableEmpty

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .empty).plus a) (fullCap top)) : Covered top .empty a := by
  change 0+a.b ≤ 122 ∧ 0+a.j ≤ 50 ∧ 0+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 122 := by omega
  have hj' : a.j ≤ 50 := by omega
  have casesTop : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 ∨ a.t = 12 ∨ a.t = 13 := by omega
  rcases casesTop with ht1 | ht2 | ht3 | ht4 | ht5 | ht6 | ht7 | ht8 | ht9 | ht10 | ht11 | ht12 | ht13
  · exact (Compact50PriceTableEmpty1.Top1.exact a ha ht1 hb' hj').trans
      (Final50PriceCaps.allowance_mono .empty (by omega : 1 ≤ top) htop)
  · exact (Compact50PriceTableEmpty1.Top2.exact a ha ht2 hb' hj').trans
      (Final50PriceCaps.allowance_mono .empty (by omega : 2 ≤ top) htop)
  · exact (Compact50PriceTableEmpty1.Top3.exact a ha ht3 hb' hj').trans
      (Final50PriceCaps.allowance_mono .empty (by omega : 3 ≤ top) htop)
  · exact (Compact50PriceTableEmpty1.Top4.exact a ha ht4 hb' hj').trans
      (Final50PriceCaps.allowance_mono .empty (by omega : 4 ≤ top) htop)
  · exact (Compact50PriceTableEmpty5.Top5.exact a ha ht5 hb' hj').trans
      (Final50PriceCaps.allowance_mono .empty (by omega : 5 ≤ top) htop)
  · exact (Compact50PriceTableEmpty5.Top6.exact a ha ht6 hb' hj').trans
      (Final50PriceCaps.allowance_mono .empty (by omega : 6 ≤ top) htop)
  · exact (Compact50PriceTableEmpty5.Top7.exact a ha ht7 hb' hj').trans
      (Final50PriceCaps.allowance_mono .empty (by omega : 7 ≤ top) htop)
  · exact (Compact50PriceTableEmpty5.Top8.exact a ha ht8 hb' hj').trans
      (Final50PriceCaps.allowance_mono .empty (by omega : 8 ≤ top) htop)
  · exact (Compact50PriceTableEmpty9.Top9.exact a ha ht9 hb' hj').trans
      (Final50PriceCaps.allowance_mono .empty (by omega : 9 ≤ top) htop)
  · exact (Compact50PriceTableEmpty9.Top10.exact a ha ht10 hb' hj').trans
      (Final50PriceCaps.allowance_mono .empty (by omega : 10 ≤ top) htop)
  · exact (Compact50PriceTableEmpty9.Top11.exact a ha ht11 hb' hj').trans
      (Final50PriceCaps.allowance_mono .empty (by omega : 11 ≤ top) htop)
  · exact (Compact50PriceTableEmpty9.Top12.exact a ha ht12 hb' hj').trans
      (Final50PriceCaps.allowance_mono .empty (by omega : 12 ≤ top) htop)
  · exact (Compact50PriceTableEmpty9.Top13.exact a ha ht13 hb' hj').trans
      (Final50PriceCaps.allowance_mono .empty (by omega : 13 ≤ top) htop)
end Compact50PriceTableEmpty
