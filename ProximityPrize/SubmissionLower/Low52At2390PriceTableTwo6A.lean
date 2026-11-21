import ProximityPrize.SubmissionLower.Low52At2390PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low52At2390PriceTableTwo6A
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low52At2390Price (fullCap)
open Low52At2390PriceCaps (Band start)
open Low52At2390PriceTableBase (Covered)
open Low52At2390PriceTableCover (PaidBatch packedBatch tilesOf checks checks_join Certificate)

namespace Band6
namespace Top1
private def b0 : PaidBatch (.two6 0) 1 := packedBatch [1904117252,3527314440,7847449100,15141346836,13352678436,17603409168] (by decide +kernel)
private def b1 : PaidBatch (.two6 0) 1 := packedBatch [20333906704] (by decide +kernel)
private def batches : List (PaidBatch (.two6 0) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 125 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 0) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 0) 2 := packedBatch [7029558280,7855839248,14608671256,14157985316,18144474896,20333907216] (by decide +kernel)
private def batches : List (PaidBatch (.two6 0) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 125 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 0) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 0) 3 := packedBatch [13232935436,15422367260,13889550888,18148670224,20333907728] (by decide +kernel)
private def batches : List (PaidBatch (.two6 0) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 125 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 0) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 0) 4 := packedBatch [12436019216,15158127132,14157986856,17880235280,20602343184] (by decide +kernel)
private def batches : List (PaidBatch (.two6 0) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 125 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 0) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 0) 5 := packedBatch [13253910036,15166517280,13889585196,17884430612,20602343700] (by decide +kernel)
private def batches : List (PaidBatch (.two6 0) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 125 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 0) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 0) 6 := packedBatch [12993864728,14902277156,13889585708,18425496340,20333908756] (by decide +kernel)
private def batches : List (PaidBatch (.two6 0) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 125 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 0) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 0) 7 := packedBatch [13002254876,15715973160,13352715824,18161256212,19797038356] (by decide +kernel)
private def batches : List (PaidBatch (.two6 0) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 125 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 0) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 0) 8 := packedBatch [19209826336,13084280880,17892821268,20065473812] (by decide +kernel)
private def batches : List (PaidBatch (.two6 0) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 125 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 0) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 0) 9 := packedBatch [19218216484,12815879220,17628581144,19528603416] (by decide +kernel)
private def batches : List (PaidBatch (.two6 0) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 125 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 0) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 0) 10 := packedBatch [15768599592,16843296528,18148670736,18169646980,19260168580] (by decide +kernel)
private def batches : List (PaidBatch (.two6 0) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 125 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 0) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 0) 11 := packedBatch [14694892076,18425496340,20602344212] (by decide +kernel)
private def batches : List (PaidBatch (.two6 0) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 125 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 0) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 0)).plus a) (fullCap top)) : Covered top (.two6 0) a := by
  change 2+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 125 := by omega
  have hj' : a.j ≤ 47 := by omega
  have hcases : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 := by omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
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
end Band6

namespace Band7
namespace Top1
private def b0 : PaidBatch (.two6 1) 1 := packedBatch [1904084484,3527281672,7847416332,14872878612,13084210212,17334940940] (by decide +kernel)
private def b1 : PaidBatch (.two6 1) 1 := packedBatch [20065438476] (by decide +kernel)
private def batches : List (PaidBatch (.two6 1) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 124 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 1) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 1) 2 := packedBatch [7029525512,7855806480,14608638488,13889517092,18144442124,20065438988] (by decide +kernel)
private def batches : List (PaidBatch (.two6 1) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 124 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 1) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 1) 3 := packedBatch [13232902668,15153899036,13889550888,18148637456,20065439504] (by decide +kernel)
private def batches : List (PaidBatch (.two6 1) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 124 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 1) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 1) 4 := packedBatch [12167550992,14889658908,14157986856,17880202512,20602310416] (by decide +kernel)
private def batches : List (PaidBatch (.two6 1) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 124 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 1) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 1) 5 := packedBatch [12985441812,14898049056,13621116972,17615962384,20333875472] (by decide +kernel)
private def batches : List (PaidBatch (.two6 1) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 124 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 1) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 1) 6 := packedBatch [12725396504,14633808932,13621117484,18157028112,20065440528] (by decide +kernel)
private def batches : List (PaidBatch (.two6 1) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 124 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 1) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 1) 7 := packedBatch [11150600732,13352715824,12733786888,15447505160,18161223444,19797005588] (by decide +kernel)
private def batches : List (PaidBatch (.two6 1) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 124 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 1) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 1) 8 := packedBatch [19209793568,13084280880,17624353044,19797005588] (by decide +kernel)
private def batches : List (PaidBatch (.two6 1) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 124 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 1) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 1) 9 := packedBatch [18949748260,12547410996,17628548372,19528570644] (by decide +kernel)
private def batches : List (PaidBatch (.two6 1) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 124 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 1) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 1) 10 := packedBatch [15768599592,18148637968,21407616784] (by decide +kernel)
private def batches : List (PaidBatch (.two6 1) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 124 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 1) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 1) 11 := packedBatch [14426423852,18157028112,20333875984] (by decide +kernel)
private def batches : List (PaidBatch (.two6 1) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 124 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 1) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 1)).plus a) (fullCap top)) : Covered top (.two6 1) a := by
  change 3+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 124 := by omega
  have hj' : a.j ≤ 47 := by omega
  have hcases : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 := by omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
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
end Band7

namespace Band8
namespace Top1
private def b0 : PaidBatch (.two6 2) 1 := packedBatch [7016908292,7847383564,14872845844,13084210212,17334908172,19796970252] (by decide +kernel)
private def batches : List (PaidBatch (.two6 2) 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 123 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 2) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 2) 2 := packedBatch [7029492744,7587338256,14340170264,13889517092,17875973900,20065406220] (by decide +kernel)
private def batches : List (PaidBatch (.two6 2) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 123 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 2) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 2) 3 := packedBatch [13232869900,15153866268,13621082664,17880169228,20065406732] (by decide +kernel)
private def batches : List (PaidBatch (.two6 2) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 123 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 2) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 2) 4 := packedBatch [12167518224,14889626140,13889518632,17611734284,20333842188] (by decide +kernel)
private def batches : List (PaidBatch (.two6 2) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 123 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 2) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 2) 5 := packedBatch [12985409044,14898016288,13621116972,17615929616,20065407248] (by decide +kernel)
private def batches : List (PaidBatch (.two6 2) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 123 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 2) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 2) 6 := packedBatch [12725363736,14633776164,13621117484,18156995344,19796972304] (by decide +kernel)
private def batches : List (PaidBatch (.two6 2) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 123 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 2) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 2) 7 := packedBatch [12733753884,15447472168,13084247600,17892755216,19528537360] (by decide +kernel)
private def batches : List (PaidBatch (.two6 2) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 123 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 2) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 2) 8 := packedBatch [18941325344,13084248112,17355884816,19796972816] (by decide +kernel)
private def batches : List (PaidBatch (.two6 2) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 123 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 2) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 2) 9 := packedBatch [18949715492,12547410996,21944454420] (by decide +kernel)
private def batches : List (PaidBatch (.two6 2) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 123 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 2) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 2) 10 := packedBatch [15768566824,17880169740,21407584012] (by decide +kernel)
private def batches : List (PaidBatch (.two6 2) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 123 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 2) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 2) 11 := packedBatch [14426423852,18156995344,20333843216] (by decide +kernel)
private def batches : List (PaidBatch (.two6 2) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 123 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 2) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 2)).plus a) (fullCap top)) : Covered top (.two6 2) a := by
  change 4+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 123 := by omega
  have hj' : a.j ≤ 47 := by omega
  have hcases : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 := by omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
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
end Band8

namespace Band9
namespace Top1
private def b0 : PaidBatch (.two6 3) 1 := packedBatch [7016875524,7578915340,14604377620,13084177444,17066439944,19528502024] (by decide +kernel)
private def batches : List (PaidBatch (.two6 3) 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 122 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 3) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 3) 2 := packedBatch [7029459976,7587305488,14340137496,13621048868,17875941128,19796937992] (by decide +kernel)
private def batches : List (PaidBatch (.two6 3) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 122 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 3) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 3) 3 := packedBatch [12964401676,14885398044,13621082664,17880136460,19796938508] (by decide +kernel)
private def batches : List (PaidBatch (.two6 3) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 122 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 3) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 3) 4 := packedBatch [12167485456,14621157916,13889518632,17611701516,20333809420] (by decide +kernel)
private def batches : List (PaidBatch (.two6 3) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 122 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 3) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 3) 5 := packedBatch [12716940820,14629548064,13621084204,17347461388,20065374476] (by decide +kernel)
private def batches : List (PaidBatch (.two6 3) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 122 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 3) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 3) 6 := packedBatch [12725330968,14633743396,13621084716,17888527116,19796939532] (by decide +kernel)
private def batches : List (PaidBatch (.two6 3) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 122 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 3) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 3) 7 := packedBatch [20279274012,13084247600,17892722448,19528504592] (by decide +kernel)
private def batches : List (PaidBatch (.two6 3) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 122 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 3) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 3) 8 := packedBatch [18941292576,13084248112,17355852048,19528504592] (by decide +kernel)
private def batches : List (PaidBatch (.two6 3) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 122 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 3) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 3) 9 := packedBatch [18681247268,21675985972] (by decide +kernel)
private def batches : List (PaidBatch (.two6 3) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 122 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 3) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 3) 10 := packedBatch [15768566824,17880136972,21139115788] (by decide +kernel)
private def batches : List (PaidBatch (.two6 3) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 122 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 3) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 3) 11 := packedBatch [14426391084,17888527116,20065374988] (by decide +kernel)
private def batches : List (PaidBatch (.two6 3) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 122 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 3) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 3)).plus a) (fullCap top)) : Covered top (.two6 3) a := by
  change 5+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 122 := by omega
  have hj' : a.j ≤ 47 := by omega
  have hcases : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 := by omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
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
end Band9

namespace Band10
namespace Top1
private def b0 : PaidBatch (.two6 4) 1 := packedBatch [6748407300,7578882572,14604344852,13084177444,16797971720,19528469256] (by decide +kernel)
private def batches : List (PaidBatch (.two6 4) 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 121 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 4) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 4) 2 := packedBatch [15103462408,14071669272,13621048868,17607472904,19528469768] (by decide +kernel)
private def batches : List (PaidBatch (.two6 4) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 121 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 4) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 4) 3 := packedBatch [12964368908,14885365276,13352614440,17611668232,19528470280] (by decide +kernel)
private def batches : List (PaidBatch (.two6 4) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 121 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 4) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 4) 4 := packedBatch [11899017232,14621125148,13621050408,17343233288,20065341192] (by decide +kernel)
private def batches : List (PaidBatch (.two6 4) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 121 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 4) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 4) 5 := packedBatch [12716908052,14629515296,13621084204,17347428620,19796906252] (by decide +kernel)
private def batches : List (PaidBatch (.two6 4) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 121 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 4) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 4) 6 := packedBatch [20807722008,13621084716,17888494348,19528471308] (by decide +kernel)
private def batches : List (PaidBatch (.two6 4) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 121 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 4) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 4) 7 := packedBatch [20279241244,13084214832,17624254220,19260036364] (by decide +kernel)
private def batches : List (PaidBatch (.two6 4) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 121 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 4) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 4) 8 := packedBatch [18672824352,22749694000] (by decide +kernel)
private def batches : List (PaidBatch (.two6 4) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 121 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 4) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 4) 9 := packedBatch [18681214500,21675953204] (by decide +kernel)
private def batches : List (PaidBatch (.two6 4) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 121 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 4) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 4) 10 := packedBatch [15500098600,17611668744,21139083016] (by decide +kernel)
private def batches : List (PaidBatch (.two6 4) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 121 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 4) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 4) 11 := packedBatch [14426391084,17888494348,20065342220] (by decide +kernel)
private def batches : List (PaidBatch (.two6 4) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 121 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 4) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 4)).plus a) (fullCap top)) : Covered top (.two6 4) a := by
  change 6+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 121 := by omega
  have hj' : a.j ≤ 47 := by omega
  have hcases : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 := by omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
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
end Band10


end Low52At2390PriceTableTwo6A
