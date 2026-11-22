import ProximityPrize.SubmissionLower.Compact54TilesEmptyPart0
import ProximityPrize.SubmissionLower.Compact54TilesEmptyPart1
import ProximityPrize.SubmissionLower.Compact54TilesEmptyPart2
import ProximityPrize.SubmissionLower.Compact54TilesEmptyPart3
import ProximityPrize.SubmissionLower.Compact54TilesEmptyPart4
import ProximityPrize.SubmissionLower.Compact54TilesEmptyPart5
import ProximityPrize.SubmissionLower.Compact54TilesEmptyPart6
import ProximityPrize.SubmissionLower.Compact54TilesEmptyPart7
import ProximityPrize.SubmissionLower.Compact54TilesEmptyPart8
import ProximityPrize.SubmissionLower.Compact54TilesEmptyPart9
import ProximityPrize.SubmissionLower.Compact54TilesEmptyPart10

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
    (hc : InBox ((start .empty).plus a) (fullCap top)) : Covered top .empty a := by
  change 0+a.b ≤ 132 ∧ 0+a.j ≤ 55 ∧ 0+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 132 := by omega
  have hj' : a.j ≤ 55 := by omega
  have h : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 ∨ a.t=13 ∨ a.t=14 := by omega
  rcases h with e1 | e2 | e3 | e4 | e5 | e6 | e7 | e8 | e9 | e10 | e11 | e12 | e13 | e14
  · exact covered_mono (Top1.exact a ha e1 hb' hj') (by omega) htop
  · exact covered_mono (Top2.exact a ha e2 hb' hj') (by omega) htop
  · exact covered_mono (Top3.exact a ha e3 hb' hj') (by omega) htop
  · exact covered_mono (Top4.exact a ha e4 hb' hj') (by omega) htop
  · exact covered_mono (Top5.exact a ha e5 hb' hj') (by omega) htop
  · exact covered_mono (Top6.exact a ha e6 hb' hj') (by omega) htop
  · exact covered_mono (Top7.exact a ha e7 hb' hj') (by omega) htop
  · exact covered_mono (Top8.exact a ha e8 hb' hj') (by omega) htop
  · exact covered_mono (Top9.exact a ha e9 hb' hj') (by omega) htop
  · exact covered_mono (Top10.exact a ha e10 hb' hj') (by omega) htop
  · exact covered_mono (Top11.exact a ha e11 hb' hj') (by omega) htop
  · exact covered_mono (Top12.exact a ha e12 hb' hj') (by omega) htop
  · exact covered_mono (Top13.exact a ha e13 hb' hj') (by omega) htop
  · exact covered_mono (Top14.exact a ha e14 hb' hj') (by omega) htop
end Compact50PriceTableEmpty
