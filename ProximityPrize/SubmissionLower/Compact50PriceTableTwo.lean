import ProximityPrize.SubmissionLower.Compact50PriceTableTwo1
import ProximityPrize.SubmissionLower.Compact50PriceTableTwo6

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered)

namespace Compact50PriceTableTwo

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .two).plus a) (fullCap top)) : Covered top .two a := by
  change 2+a.b ≤ 122 ∧ 6+a.j ≤ 50 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 120 := by omega
  have hj' : a.j ≤ 44 := by omega
  have casesTop : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 := by omega
  rcases casesTop with ht1 | ht2 | ht3 | ht4 | ht5 | ht6 | ht7 | ht8 | ht9 | ht10 | ht11
  · exact (Compact50PriceTableTwo1.Top1.exact a ha ht1 hb' hj').trans
      (Final50PriceCaps.allowance_mono .two (by omega : 3 ≤ top) htop)
  · exact (Compact50PriceTableTwo1.Top2.exact a ha ht2 hb' hj').trans
      (Final50PriceCaps.allowance_mono .two (by omega : 4 ≤ top) htop)
  · exact (Compact50PriceTableTwo1.Top3.exact a ha ht3 hb' hj').trans
      (Final50PriceCaps.allowance_mono .two (by omega : 5 ≤ top) htop)
  · exact (Compact50PriceTableTwo1.Top4.exact a ha ht4 hb' hj').trans
      (Final50PriceCaps.allowance_mono .two (by omega : 6 ≤ top) htop)
  · exact (Compact50PriceTableTwo1.Top5.exact a ha ht5 hb' hj').trans
      (Final50PriceCaps.allowance_mono .two (by omega : 7 ≤ top) htop)
  · exact (Compact50PriceTableTwo6.Top6.exact a ha ht6 hb' hj').trans
      (Final50PriceCaps.allowance_mono .two (by omega : 8 ≤ top) htop)
  · exact (Compact50PriceTableTwo6.Top7.exact a ha ht7 hb' hj').trans
      (Final50PriceCaps.allowance_mono .two (by omega : 9 ≤ top) htop)
  · exact (Compact50PriceTableTwo6.Top8.exact a ha ht8 hb' hj').trans
      (Final50PriceCaps.allowance_mono .two (by omega : 10 ≤ top) htop)
  · exact (Compact50PriceTableTwo6.Top9.exact a ha ht9 hb' hj').trans
      (Final50PriceCaps.allowance_mono .two (by omega : 11 ≤ top) htop)
  · exact (Compact50PriceTableTwo6.Top10.exact a ha ht10 hb' hj').trans
      (Final50PriceCaps.allowance_mono .two (by omega : 12 ≤ top) htop)
  · exact (Compact50PriceTableTwo6.Top11.exact a ha ht11 hb' hj').trans
      (Final50PriceCaps.allowance_mono .two (by omega : 13 ≤ top) htop)
end Compact50PriceTableTwo
