import ProximityPrize.SubmissionLower.Low52At2390PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low52At2390PriceTableOne6
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low52At2390Price (fullCap)
open Low52At2390PriceCaps (Band start)
open Low52At2390PriceTableBase (Covered)
open Low52At2390PriceTableCover (PaidBatch packedBatch tilesOf checks checks_join Certificate)

namespace Top1
private def b0 : PaidBatch .one6 1 := packedBatch [6211667460,7042142732,13530734100,12010501156,15724360976,18186423056] (by decide +kernel)
private def batches : List (PaidBatch .one6 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 125 3 45 = true := by decide +kernel
def receipt : Certificate .one6 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch .one6 2 := packedBatch [6492687368,7050532880,12998058520,12547372580,16265426704,18186423568] (by decide +kernel)
private def batches : List (PaidBatch .one6 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 125 6 42 = true := by decide +kernel
def receipt : Certificate .one6 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch .one6 3 := packedBatch [11890758156,13811754524,12547373608,16269622032,18186424080] (by decide +kernel)
private def batches : List (PaidBatch .one6 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 125 9 39 = true := by decide +kernel
def receipt : Certificate .one6 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch .one6 4 := packedBatch [11093841936,13547514396,12547374120,16001187088,18454859536] (by decide +kernel)
private def batches : List (PaidBatch .one6 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 125 12 36 = true := by decide +kernel
def receipt : Certificate .one6 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch .one6 5 := packedBatch [11911732756,13555904544,12547407916,16005382420,18454860052] (by decide +kernel)
private def batches : List (PaidBatch .one6 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 125 15 33 = true := by decide +kernel
def receipt : Certificate .one6 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch .one6 6 := packedBatch [11651687448,13291664420,12547408428,16546448148,18186425108] (by decide +kernel)
private def batches : List (PaidBatch .one6 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 125 18 30 = true := by decide +kernel
def receipt : Certificate .one6 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch .one6 7 := packedBatch [18668759580,12010538544,16282208020,17917990164] (by decide +kernel)
private def batches : List (PaidBatch .one6 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 125 21 27 = true := by decide +kernel
def receipt : Certificate .one6 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch .one6 8 := packedBatch [17330778144,11742103600,20870777108] (by decide +kernel)
private def batches : List (PaidBatch .one6 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 125 24 24 = true := by decide +kernel
def receipt : Certificate .one6 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch .one6 9 := packedBatch [17339168292,19797036084] (by decide +kernel)
private def batches : List (PaidBatch .one6 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 125 27 21 = true := by decide +kernel
def receipt : Certificate .one6 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch .one6 10 := packedBatch [14157986856,16269622544,19528601360] (by decide +kernel)
private def batches : List (PaidBatch .one6 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 125 30 18 = true := by decide +kernel
def receipt : Certificate .one6 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch .one6 11 := packedBatch [13084279340,16546448148,18454860564] (by decide +kernel)
private def batches : List (PaidBatch .one6 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 125 33 15 = true := by decide +kernel
def receipt : Certificate .one6 11 := ⟨batches, i33⟩
end Top11

namespace Top12
private def b0 : PaidBatch .one6 12 := packedBatch [12010539056,15745337620,17917990164] (by decide +kernel)
private def batches : List (PaidBatch .one6 12) := [b0]
private abbrev tiles := tilesOf batches
private theorem i36 : checks tiles 125 36 12 = true := by decide +kernel
def receipt : Certificate .one6 12 := ⟨batches, i36⟩
end Top12

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one6).plus a) (fullCap top)) : Covered top .one6 a := by
  change 2+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 125 := by omega
  have hj' : a.j ≤ 47 := by omega
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

end Low52At2390PriceTableOne6
