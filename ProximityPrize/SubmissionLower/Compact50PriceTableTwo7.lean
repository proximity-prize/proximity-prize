import ProximityPrize.SubmissionLower.Compact54TilesTwo7Part0
import ProximityPrize.SubmissionLower.Compact54TilesTwo7Part1

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)

theorem price (top : ℕ) (htop : top ≤ 14) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .two7).plus a) (fullCap top)) : Covered top .two7 a := by
  change 3+a.b ≤ 132 ∧ 7+a.j ≤ 55 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 129 := by omega
  have hj' : a.j ≤ 48 := by omega
  have h : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 := by omega
  rcases h with e1 | e2 | e3 | e4 | e5 | e6 | e7 | e8 | e9 | e10 | e11 | e12
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
end Compact50PriceTableTwo7
