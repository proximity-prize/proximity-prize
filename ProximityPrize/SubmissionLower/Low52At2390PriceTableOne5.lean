import ProximityPrize.SubmissionLower.Low52At2390PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low52At2390PriceTableOne5
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low52At2390Price (fullCap)
open Low52At2390PriceCaps (Band start)
open Low52At2390PriceTableBase (Covered)
open Low52At2390PriceTableCover (PaidBatch packedBatch tilesOf checks checks_join Certificate)

namespace Top1
private def b0 : PaidBatch .one5 1 := packedBatch [826181124,1098811912,3258878984,7042142732,13262298644,12283130916] (by decide +kernel)
private def b1 : PaidBatch .one5 1 := packedBatch [16265426192,17922182416] (by decide +kernel)
private def batches : List (PaidBatch .one5 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 125 3 46 = true := by decide +kernel
def receipt : Certificate .one5 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch .one5 2 := packedBatch [6224251912,7050532880,14075994648,12551567400,16269621520,18190618384] (by decide +kernel)
private def batches : List (PaidBatch .one5 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 125 6 43 = true := by decide +kernel
def receipt : Certificate .one5 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch .one5 3 := packedBatch [11890758156,13543319068,12820003368,14163136272,16269622032,15216856964] (by decide +kernel)
private def b1 : PaidBatch .one5 3 := packedBatch [16580008324] (by decide +kernel)
private def batches : List (PaidBatch .one5 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 125 9 40 = true := by decide +kernel
def receipt : Certificate .one5 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch .one5 4 := packedBatch [12171778064,13551709216,12820037164,14431605012,16273817364,18727489928] (by decide +kernel)
private def batches : List (PaidBatch .one5 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 125 12 37 = true := by decide +kernel
def receipt : Certificate .one5 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch .one5 5 := packedBatch [11643297300,13287469088,12820037676,16546447636,18459054868] (by decide +kernel)
private def batches : List (PaidBatch .one5 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 125 15 34 = true := by decide +kernel
def receipt : Certificate .one5 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch .one5 6 := packedBatch [11383251992,14101165092,12551603248,16550642964,18190619924] (by decide +kernel)
private def batches : List (PaidBatch .one5 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 125 18 31 = true := by decide +kernel
def receipt : Certificate .one5 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch .one5 7 := packedBatch [11391642140,13836924968,12283168304,16282208020,18459055380] (by decide +kernel)
private def batches : List (PaidBatch .one5 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 125 21 28 = true := by decide +kernel
def receipt : Certificate .one5 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch .one5 8 := packedBatch [10085281824,12014766644,12477968652,14113750796,16017967896,18190620440] (by decide +kernel)
private def batches : List (PaidBatch .one5 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 125 24 25 = true := by decide +kernel
def receipt : Certificate .one5 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch .one5 9 := packedBatch [17070732836,11746331700,16559033624,17653750040] (by decide +kernel)
private def batches : List (PaidBatch .one5 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 125 27 22 = true := by decide +kernel
def receipt : Certificate .one5 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch .one5 10 := packedBatch [14699052072,15236878608,17079123216,16294793604,17385315204] (by decide +kernel)
private def batches : List (PaidBatch .one5 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 125 30 19 = true := by decide +kernel
def receipt : Certificate .one5 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch .one5 11 := packedBatch [13625344556,14968476436,16278012692,16026358664,17385315208] (by decide +kernel)
private def batches : List (PaidBatch .one5 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 125 33 16 = true := by decide +kernel
def receipt : Certificate .one5 11 := ⟨batches, i33⟩
end Top11

namespace Top12
private def b0 : PaidBatch .one5 12 := packedBatch [12551604272,16554838292,18190620436] (by decide +kernel)
private def batches : List (PaidBatch .one5 12) := [b0]
private abbrev tiles := tilesOf batches
private theorem i36 : checks tiles 125 36 13 = true := by decide +kernel
def receipt : Certificate .one5 12 := ⟨batches, i36⟩
end Top12

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one5).plus a) (fullCap top)) : Covered top .one5 a := by
  change 2+a.b ≤ 127 ∧ 5+a.j ≤ 53 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 125 := by omega
  have hj' : a.j ≤ 48 := by omega
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

end Low52At2390PriceTableOne5
