import ProximityPrize.SubmissionLower.Low52At2390PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low52At2390PriceTableOne4
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low52At2390Price (fullCap)
open Low52At2390PriceCaps (Band start)
open Low52At2390PriceTableBase (Covered)
open Low52At2390PriceTableCover (PaidBatch packedBatch tilesOf checks checks_join Certificate)

namespace Top1
private def b0 : PaidBatch .one4 1 := packedBatch [285115908,557746184,1098811912,2990443528,6505271820,6822075924] (by decide +kernel)
private def b1 : PaidBatch .one4 1 := packedBatch [11750454820,13803364104,12825153296,15732750096,14415744900,14973590404] (by decide +kernel)
private def batches : List (PaidBatch .one4 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 125 3 47 = true := by decide +kernel
def receipt : Certificate .one4 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch .one4 2 := packedBatch [2990443528,4076769804,6513661968,13270688280,12287326248,13362024208] (by decide +kernel)
private def b1 : PaidBatch .one4 2 := packedBatch [15732750608,14684180356,15510461316] (by decide +kernel)
private def batches : List (PaidBatch .one4 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 125 6 44 = true := by decide +kernel
def receipt : Certificate .one4 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch .one4 3 := packedBatch [6773707276,7599988244,13279078428,12287327272,13630460176,15736945936] (by decide +kernel)
private def b1 : PaidBatch .one4 3 := packedBatch [14684180868,16047332228] (by decide +kernel)
private def batches : List (PaidBatch .one4 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 125 9 41 = true := by decide +kernel
def receipt : Certificate .one4 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch .one4 4 := packedBatch [11634907152,13014838304,12555796012,13898928916,16278011668,15225246600] (by decide +kernel)
private def b1 : PaidBatch .one4 4 := packedBatch [16047332744] (by decide +kernel)
private def batches : List (PaidBatch .one4 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 125 12 38 = true := by decide +kernel
def receipt : Certificate .one4 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch .one4 5 := packedBatch [11106426388,13560098848,12287361580,13898929428,16282206996,15225247112] (by decide +kernel)
private def b1 : PaidBatch .one4 5 := packedBatch [16315768200] (by decide +kernel)
private def batches : List (PaidBatch .one4 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 125 15 35 = true := by decide +kernel
def receipt : Certificate .one4 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch .one4 6 := packedBatch [10846381080,13295858724,12287362096,14167364884,15745336596,15493682568] (by decide +kernel)
private def b1 : PaidBatch .one4 6 := packedBatch [16584203656] (by decide +kernel)
private def batches : List (PaidBatch .one4 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 125 18 32 = true := by decide +kernel
def receipt : Certificate .one4 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch .one4 7 := packedBatch [11932707356,13572684328,12018927664,13898929940,15749531924,15766312840] (by decide +kernel)
private def b1 : PaidBatch .one4 7 := packedBatch [16315768712] (by decide +kernel)
private def batches : List (PaidBatch .one4 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 125 21 29 = true := by decide +kernel
def receipt : Certificate .one4 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch .one4 8 := packedBatch [9548410912,12018960948,11941097740,13308444428,13898930456,16022162200] (by decide +kernel)
private def b1 : PaidBatch .one4 8 := packedBatch [15497877896,16584204168] (by decide +kernel)
private def batches : List (PaidBatch .one4 8) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 125 24 26 = true := by decide +kernel
def receipt : Certificate .one4 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch .one4 9 := packedBatch [9556833828,11482091060,11949487888,14122140432,13630495512,16026357528] (by decide +kernel)
private def b1 : PaidBatch .one4 9 := packedBatch [15510002568,16038943680,16315769280] (by decide +kernel)
private def batches : List (PaidBatch .one4 9) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 125 27 23 = true := by decide +kernel
def receipt : Certificate .one4 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch .one4 10 := packedBatch [9292594216,11213656120,12226313488,13857900304,13630495512,15757922584] (by decide +kernel)
private def b1 : PaidBatch .one4 10 := packedBatch [15510002568,16038943680,16315769280] (by decide +kernel)
private def batches : List (PaidBatch .one4 10) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 125 30 20 = true := by decide +kernel
def receipt : Certificate .one4 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch .one4 11 := packedBatch [13629538860,14704235796,16282206996,15493682568,17121074568] (by decide +kernel)
private def batches : List (PaidBatch .one4 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 125 33 17 = true := by decide +kernel
def receipt : Certificate .one4 11 := ⟨batches, i33⟩
end Top11

namespace Top12
private def b0 : PaidBatch .one4 12 := packedBatch [12555798576,14435800852,15749531924,16034748296,16584204168] (by decide +kernel)
private def batches : List (PaidBatch .one4 12) := [b0]
private abbrev tiles := tilesOf batches
private theorem i36 : checks tiles 125 36 14 = true := by decide +kernel
def receipt : Certificate .one4 12 := ⟨batches, i36⟩
end Top12

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one4).plus a) (fullCap top)) : Covered top .one4 a := by
  change 2+a.b ≤ 127 ∧ 4+a.j ≤ 53 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 125 := by omega
  have hj' : a.j ≤ 49 := by omega
  have hcases : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 ∨ a.t = 12 := by omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
  · exact Certificate.apply Top1.receipt a ha h1 hb' hj' ht htop
  · exact Certificate.apply Top2.receipt a ha h2 hb' hj' ht htop
  · exact Certificate.apply Top3.receipt a ha h3 hb' hj' ht htop
  · exact Certificate.apply Top4.receipt a ha h4 hb' hj' ht htop
  · exact Certificate.apply Top5.receipt a ha h5 hb' hj' ht htop
  · exact Certificate.apply Top6.receipt a ha h6 hb' hj' ht htop
  · exact Certificate.apply Top7.receipt a ha h7 hb' hj' ht htop
  · exact Certificate.apply Top8.receipt a ha h8 hb' hj' ht htop
  · exact Certificate.apply Top9.receipt a ha h9 hb' hj' ht htop
  · exact Certificate.apply Top10.receipt a ha h10 hb' hj' ht htop
  · exact Certificate.apply Top11.receipt a ha h11 hb' hj' ht htop
  · exact Certificate.apply Top12.receipt a ha h12 hb' hj' ht htop

end Low52At2390PriceTableOne4
