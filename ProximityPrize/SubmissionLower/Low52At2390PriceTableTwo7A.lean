import ProximityPrize.SubmissionLower.Low52At2390PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low52At2390PriceTableTwo7A
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low52At2390Price (fullCap)
open Low52At2390PriceCaps (Band start)
open Low52At2390PriceTableBase (Covered)
open Low52At2390PriceTableCover (PaidBatch packedBatch tilesOf checks checks_join Certificate)

namespace Band21
namespace Top1
private def b0 : PaidBatch (.two7 0) 1 := packedBatch [10506601988,9722270220,21848005652,19522466340,21402470668,25383809804] (by decide +kernel)
private def b1 : PaidBatch (.two7 0) 1 := packedBatch [23529933184,24893085056] (by decide +kernel)
private def batches : List (PaidBatch (.two7 0) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 124 3 44 = true := by decide +kernel
def receipt : Certificate (.two7 0) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two7 0) 2 := packedBatch [10250750984,11345467408,21319524888,19522467364,21670906636,25388005132] (by decide +kernel)
private def b1 : PaidBatch (.two7 0) 2 := packedBatch [23529933696,25698391424] (by decide +kernel)
private def batches : List (PaidBatch (.two7 0) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 124 6 41 = true := by decide +kernel
def receipt : Certificate (.two7 0) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two7 0) 3 := packedBatch [19406918156,20786849308,20327807016,21939375376,19465648400,22170977040] (by decide +kernel)
private def b1 : PaidBatch (.two7 0) 3 := packedBatch [24339434884,25698391940] (by decide +kernel)
private def batches : List (PaidBatch (.two7 0) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 124 9 38 = true := by decide +kernel
def receipt : Certificate (.two7 0) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two7 0) 4 := packedBatch [17804695568,21600545308,19790937128,21939375888,25933266192,24070999940] (by decide +kernel)
private def b1 : PaidBatch (.two7 0) 4 := packedBatch [25966827396] (by decide +kernel)
private def batches : List (PaidBatch (.two7 0) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 124 12 35 = true := by decide +kernel
def receipt : Certificate (.two7 0) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two7 0) 5 := packedBatch [17276214804,21067869728,19790937644,22476246800,25127960336,24339435396] (by decide +kernel)
private def b1 : PaidBatch (.two7 0) 5 := packedBatch [26235262852] (by decide +kernel)
private def batches : List (PaidBatch (.two7 0) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 124 15 32 = true := by decide +kernel
def receipt : Certificate (.two7 0) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two7 0) 6 := packedBatch [18630976536,21344695332,18985632300,22207811856,24863720208,24880501124] (by decide +kernel)
private def b1 : PaidBatch (.two7 0) 6 := packedBatch [25966827908] (by decide +kernel)
private def batches : List (PaidBatch (.two7 0) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 124 18 29 = true := by decide +kernel
def receipt : Certificate (.two7 0) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two7 0) 7 := packedBatch [15172938268,18985665584,18370931464,20812019976,21670941460,25404785940] (by decide +kernel)
private def b1 : PaidBatch (.two7 0) 7 := packedBatch [24343630724,25966827908] (by decide +kernel)
private def batches : List (PaidBatch (.two7 0) 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 124 21 26 = true := by decide +kernel
def receipt : Certificate (.two7 0) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two7 0) 8 := packedBatch [15181361184,18180360240,18647757068,21894151436,21402506516,25140545812] (by decide +kernel)
private def b1 : PaidBatch (.two7 0) 8 := packedBatch [24355755396,24884696508,25429957564] (by decide +kernel)
private def batches : List (PaidBatch (.two7 0) 8) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 124 24 23 = true := by decide +kernel
def receipt : Certificate (.two7 0) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two7 0) 9 := packedBatch [25656440356,17643489844,21402506516,24603675412,24884696452,25429957508] (by decide +kernel)
private def batches : List (PaidBatch (.two7 0) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 124 27 20 = true := by decide +kernel
def receipt : Certificate (.two7 0) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two7 0) 10 := packedBatch [21669985320,23013117712,25664830736,24339435396,26503698308] (by decide +kernel)
private def batches : List (PaidBatch (.two7 0) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 124 30 17 = true := by decide +kernel
def receipt : Certificate (.two7 0) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two7 0) 11 := packedBatch [19522503212,22476247312,24595284752,24880501124,25966827908] (by decide +kernel)
private def batches : List (PaidBatch (.two7 0) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 124 33 14 = true := by decide +kernel
def receipt : Certificate (.two7 0) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two7 0)).plus a) (fullCap top)) : Covered top (.two7 0) a := by
  change 3+a.b ≤ 127 ∧ 7+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 124 := by omega
  have hj' : a.j ≤ 46 := by omega
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
end Band21

namespace Band22
namespace Top1
private def b0 : PaidBatch (.two7 1) 1 := packedBatch [10238133764,9722237452,21847972884,19522466340,21402470668,25115341580] (by decide +kernel)
private def b1 : PaidBatch (.two7 1) 1 := packedBatch [23261464960,24624616832] (by decide +kernel)
private def batches : List (PaidBatch (.two7 1) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 123 3 44 = true := by decide +kernel
def receipt : Certificate (.two7 1) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two7 1) 2 := packedBatch [10250718216,11345434640,21319492120,19522467364,21670906636,25119536908] (by decide +kernel)
private def b1 : PaidBatch (.two7 1) 2 := packedBatch [23261465472,25429923200] (by decide +kernel)
private def batches : List (PaidBatch (.two7 1) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 123 6 41 = true := by decide +kernel
def receipt : Certificate (.two7 1) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two7 1) 3 := packedBatch [19138449932,20518381084,20059338792,21670907148,25929038092,24070966656] (by decide +kernel)
private def b1 : PaidBatch (.two7 1) 3 := packedBatch [25429923712] (by decide +kernel)
private def batches : List (PaidBatch (.two7 1) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 123 9 38 = true := by decide +kernel
def receipt : Certificate (.two7 1) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two7 1) 4 := packedBatch [17804662800,21600512540,19522468904,21670907660,25664797964,23802531712] (by decide +kernel)
private def b1 : PaidBatch (.two7 1) 4 := packedBatch [25698359168] (by decide +kernel)
private def batches : List (PaidBatch (.two7 1) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 123 12 35 = true := by decide +kernel
def receipt : Certificate (.two7 1) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two7 1) 5 := packedBatch [17007746580,21067836960,19790937644,22207778576,24859492112,24070967168] (by decide +kernel)
private def b1 : PaidBatch (.two7 1) 5 := packedBatch [25966794624] (by decide +kernel)
private def batches : List (PaidBatch (.two7 1) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 123 15 32 = true := by decide +kernel
def receipt : Certificate (.two7 1) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two7 1) 6 := packedBatch [18362508312,21076227108,18985632300,21939343632,24863687440,24612032896] (by decide +kernel)
private def b1 : PaidBatch (.two7 1) 6 := packedBatch [25698359680] (by decide +kernel)
private def batches : List (PaidBatch (.two7 1) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 123 18 29 = true := by decide +kernel
def receipt : Certificate (.two7 1) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two7 1) 7 := packedBatch [15172938268,18717197360,18370898696,20811987208,21402473232,25136317712] (by decide +kernel)
private def b1 : PaidBatch (.two7 1) 7 := packedBatch [27577406336] (by decide +kernel)
private def batches : List (PaidBatch (.two7 1) 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 123 21 26 = true := by decide +kernel
def receipt : Certificate (.two7 1) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two7 1) 8 := packedBatch [14912892960,17911892016,18379288840,21625683208,25140513040,27040535824] (by decide +kernel)
private def batches : List (PaidBatch (.two7 1) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 123 24 23 = true := by decide +kernel
def receipt : Certificate (.two7 1) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two7 1) 9 := packedBatch [25656407588,17643489844,24335207188,27040535828] (by decide +kernel)
private def batches : List (PaidBatch (.two7 1) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 123 27 20 = true := by decide +kernel
def receipt : Certificate (.two7 1) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two7 1) 10 := packedBatch [21401517096,22744649484,25664797964,24070967168,26503665536] (by decide +kernel)
private def batches : List (PaidBatch (.two7 1) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 123 30 17 = true := by decide +kernel
def receipt : Certificate (.two7 1) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two7 1) 11 := packedBatch [19522503212,22207779088,24326816528,24612032896,25698359680] (by decide +kernel)
private def batches : List (PaidBatch (.two7 1) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 123 33 14 = true := by decide +kernel
def receipt : Certificate (.two7 1) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two7 1)).plus a) (fullCap top)) : Covered top (.two7 1) a := by
  change 4+a.b ≤ 127 ∧ 7+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 123 := by omega
  have hj' : a.j ≤ 46 := by omega
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
end Band22

namespace Band23
namespace Top1
private def b0 : PaidBatch (.two7 2) 1 := packedBatch [10238100996,9722204684,21579504660,19253998116,21134002440,24846873352] (by decide +kernel)
private def b1 : PaidBatch (.two7 2) 1 := packedBatch [23261432188,24624584060] (by decide +kernel)
private def batches : List (PaidBatch (.two7 2) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 122 3 44 = true := by decide +kernel
def receipt : Certificate (.two7 2) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two7 2) 2 := packedBatch [10250685448,11076966416,21051023896,19253999140,21402438408,24851068680] (by decide +kernel)
private def b1 : PaidBatch (.two7 2) 2 := packedBatch [28651113340] (by decide +kernel)
private def batches : List (PaidBatch (.two7 2) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 122 6 41 = true := by decide +kernel
def receipt : Certificate (.two7 2) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two7 2) 3 := packedBatch [19138417164,20518348316,20059338792,21670874380,25660569868,28651113852] (by decide +kernel)
private def batches : List (PaidBatch (.two7 2) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 122 9 38 = true := by decide +kernel
def receipt : Certificate (.two7 2) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two7 2) 4 := packedBatch [17536194576,21332044316,19522468904,25396329740,28114243340] (by decide +kernel)
private def batches : List (PaidBatch (.two7 2) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 122 12 35 = true := by decide +kernel
def receipt : Certificate (.two7 2) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two7 2) 5 := packedBatch [17007713812,20799368736,19522469420,24859459340,28651114252] (by decide +kernel)
private def batches : List (PaidBatch (.two7 2) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 122 15 32 = true := by decide +kernel
def receipt : Certificate (.two7 2) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two7 2) 6 := packedBatch [18094040088,20807758884,18717164076,24595219212,28114243852] (by decide +kernel)
private def batches : List (PaidBatch (.two7 2) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 122 18 29 = true := by decide +kernel
def receipt : Certificate (.two7 2) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two7 2) 7 := packedBatch [14904470044,18717197360,27522837252,25136284944,27577373456] (by decide +kernel)
private def batches : List (PaidBatch (.two7 2) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 122 21 26 = true := by decide +kernel
def receipt : Certificate (.two7 2) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two7 2) 8 := packedBatch [26994356256,17911892016,24872044816,26772067600] (by decide +kernel)
private def batches : List (PaidBatch (.two7 2) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 122 24 23 = true := by decide +kernel
def receipt : Certificate (.two7 2) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two7 2) 9 := packedBatch [25387939364,17375021620,24066738960,26772067600] (by decide +kernel)
private def batches : List (PaidBatch (.two7 2) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 122 27 20 = true := by decide +kernel
def receipt : Certificate (.two7 2) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two7 2) 10 := packedBatch [21401517096,22476181260,25396329740,23802498940,26235197308] (by decide +kernel)
private def batches : List (PaidBatch (.two7 2) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 122 30 17 = true := by decide +kernel
def receipt : Certificate (.two7 2) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two7 2) 11 := packedBatch [19254034988,24058348300,28114243852] (by decide +kernel)
private def batches : List (PaidBatch (.two7 2) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 122 33 14 = true := by decide +kernel
def receipt : Certificate (.two7 2) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two7 2)).plus a) (fullCap top)) : Covered top (.two7 2) a := by
  change 5+a.b ≤ 127 ∧ 7+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 122 := by omega
  have hj' : a.j ≤ 46 := by omega
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
end Band23

namespace Band24
namespace Top1
private def b0 : PaidBatch (.two7 3) 1 := packedBatch [10238068228,9453736460,21311036436,19253998116,24578405128,28382644488] (by decide +kernel)
private def batches : List (PaidBatch (.two7 3) 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 121 3 44 = true := by decide +kernel
def receipt : Certificate (.two7 3) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two7 3) 2 := packedBatch [22619655176,20782555672,19253999140,24582600456,28382645000] (by decide +kernel)
private def batches : List (PaidBatch (.two7 3) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 121 6 41 = true := by decide +kernel
def receipt : Certificate (.two7 3) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two7 3) 3 := packedBatch [18869948940,20249880092,19522435112,25392101640,28382645512] (by decide +kernel)
private def batches : List (PaidBatch (.two7 3) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 121 9 38 = true := by decide +kernel
def receipt : Certificate (.two7 3) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two7 3) 4 := packedBatch [17536161808,21063576092,18985565224,25127861512,28114210568] (by decide +kernel)
private def batches : List (PaidBatch (.two7 3) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 121 12 35 = true := by decide +kernel
def receipt : Certificate (.two7 3) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two7 3) 5 := packedBatch [16739245588,20530900512,19522469420,24590991116,28382646028] (by decide +kernel)
private def batches : List (PaidBatch (.two7 3) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 121 15 32 = true := by decide +kernel
def receipt : Certificate (.two7 3) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two7 3) 6 := packedBatch [18094007320,20807726116,18717164076,24326750988,27845775628] (by decide +kernel)
private def batches : List (PaidBatch (.two7 3) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 121 18 29 = true := by decide +kernel
def receipt : Certificate (.two7 3) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two7 3) 7 := packedBatch [27522804252,18448729136,24867816716,27308905228] (by decide +kernel)
private def batches : List (PaidBatch (.two7 3) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 121 21 26 = true := by decide +kernel
def receipt : Certificate (.two7 3) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two7 3) 8 := packedBatch [26994323488,17643423792,24603576588,26503599372] (by decide +kernel)
private def batches : List (PaidBatch (.two7 3) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 121 24 23 = true := by decide +kernel
def receipt : Certificate (.two7 3) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two7 3) 9 := packedBatch [25119471140,17375021620,23798270736,26503599376] (by decide +kernel)
private def batches : List (PaidBatch (.two7 3) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 121 27 20 = true := by decide +kernel
def receipt : Certificate (.two7 3) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two7 3) 10 := packedBatch [21133048872,25127861512,28651081480] (by decide +kernel)
private def batches : List (PaidBatch (.two7 3) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 121 30 17 = true := by decide +kernel
def receipt : Certificate (.two7 3) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two7 3) 11 := packedBatch [19254034988,24058315532,27845775628] (by decide +kernel)
private def batches : List (PaidBatch (.two7 3) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 121 33 14 = true := by decide +kernel
def receipt : Certificate (.two7 3) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two7 3)).plus a) (fullCap top)) : Covered top (.two7 3) a := by
  change 6+a.b ≤ 127 ∧ 7+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 121 := by omega
  have hj' : a.j ≤ 46 := by omega
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
end Band24


end Low52At2390PriceTableTwo7A
