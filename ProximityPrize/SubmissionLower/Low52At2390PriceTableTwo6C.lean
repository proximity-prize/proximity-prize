import ProximityPrize.SubmissionLower.Low52At2390PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low52At2390PriceTableTwo6C
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low52At2390Price (fullCap)
open Low52At2390PriceCaps (Band start)
open Low52At2390PriceTableBase (Covered)
open Low52At2390PriceTableCover (PaidBatch packedBatch tilesOf checks checks_join Certificate)

namespace Band16
namespace Top1
private def b0 : PaidBatch (.two6 10) 1 := packedBatch [10237871620,11068346892,21583470100,18989659172,24850838780,28655078140] (by decide +kernel)
private def batches : List (PaidBatch (.two6 10) 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 115 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 10) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 10) 2 := packedBatch [10250456072,11076737040,20782359064,19794966052,25928775420,28655078652] (by decide +kernel)
private def batches : List (PaidBatch (.two6 10) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 115 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 10) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 10) 3 := packedBatch [18869752332,21864490524,19526531624,25664535292,28655079164] (by decide +kernel)
private def batches : List (PaidBatch (.two6 10) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 115 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 10) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 10) 4 := packedBatch [17535965200,21063379484,19794967592,22211776252,25127664892,24611770216] (by decide +kernel)
private def b1 : PaidBatch (.two6 10) 4 := packedBatch [25702291816] (by decide +kernel)
private def batches : List (PaidBatch (.two6 10) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 115 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 10) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 10) 5 := packedBatch [18353856020,21071769632,19526565932,25131860224,28655079680] (by decide +kernel)
private def batches : List (PaidBatch (.two6 10) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 115 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 10) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 10) 6 := packedBatch [18093810712,20807529508,19526566444,25672925952,28386644736] (by decide +kernel)
private def batches : List (PaidBatch (.two6 10) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 115 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 10) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 10) 7 := packedBatch [18102200860,21621225512,18721261104,25408685824,27849774336] (by decide +kernel)
private def batches : List (PaidBatch (.two6 10) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 115 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 10) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 10) 8 := packedBatch [26994126880,18452826160,24603379968,27849774336] (by decide +kernel)
private def batches : List (PaidBatch (.two6 10) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 115 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 10) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 10) 9 := packedBatch [26734081572,17915989044,24339139844,27312903940] (by decide +kernel)
private def batches : List (PaidBatch (.two6 10) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 115 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 10) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 10) 10 := packedBatch [22210886696,23553953532,25127664892,24880205672,26507598184] (by decide +kernel)
private def batches : List (PaidBatch (.two6 10) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 115 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 10) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 10) 11 := packedBatch [20331872812,25404490496,28386644736] (by decide +kernel)
private def batches : List (PaidBatch (.two6 10) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 115 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 10) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 10)).plus a) (fullCap top)) : Covered top (.two6 10) a := by
  change 12+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 115 := by omega
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
end Band16

namespace Band17
namespace Top1
private def b0 : PaidBatch (.two6 11) 1 := packedBatch [11043145220,12142055948,23462485524,20331803684,22748613368,27266725112] (by decide +kernel)
private def b1 : PaidBatch (.two6 11) 1 := packedBatch [25412848484,26776000356] (by decide +kernel)
private def batches : List (PaidBatch (.two6 11) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 114 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 11) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 11) 2 := packedBatch [11055729672,12150446096,22661374488,21405546020,23285484792,28344661752] (by decide +kernel)
private def b1 : PaidBatch (.two6 11) 2 := packedBatch [25412848996,27581306724] (by decide +kernel)
private def batches : List (PaidBatch (.two6 11) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 114 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 11) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 11) 3 := packedBatch [20748767756,23743505948,21674015272,23553920764,28080421628,26490785636] (by decide +kernel)
private def b1 : PaidBatch (.two6 11) 3 := packedBatch [27581307236] (by decide +kernel)
private def batches : List (PaidBatch (.two6 11) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 114 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 11) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 11) 4 := packedBatch [19146545168,23210830364,21942451240,24090791676,27543551228,26759221092] (by decide +kernel)
private def b1 : PaidBatch (.two6 11) 4 := packedBatch [28118178148] (by decide +kernel)
private def batches : List (PaidBatch (.two6 11) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 114 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 11) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 11) 5 := packedBatch [19964435988,22950785056,21137145900,24090792188,27279311100,26222350692] (by decide +kernel)
private def b1 : PaidBatch (.two6 11) 5 := packedBatch [28386613604] (by decide +kernel)
private def batches : List (PaidBatch (.two6 11) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 114 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 11) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 11) 6 := packedBatch [19704390680,22686544932,21137146412,27820376828,30802531068] (by decide +kernel)
private def batches : List (PaidBatch (.two6 11) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 114 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 11) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 11) 7 := packedBatch [19444345372,23500240936,20600309296,27556136704,30265660672] (by decide +kernel)
private def batches : List (PaidBatch (.two6 11) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 114 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 11) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 11) 8 := packedBatch [29141577760,20063438896,26750830848,30265660672] (by decide +kernel)
private def batches : List (PaidBatch (.two6 11) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 114 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 11) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 11) 9 := packedBatch [28881532452,19258133556,26486590720,29460354816] (by decide +kernel)
private def batches : List (PaidBatch (.two6 11) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 114 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 11) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 11) 10 := packedBatch [27275115560,18721263156,27027656448,28655048960] (by decide +kernel)
private def batches : List (PaidBatch (.two6 11) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 114 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 11) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 11) 11 := packedBatch [21942452780,27551941372,30802531068] (by decide +kernel)
private def batches : List (PaidBatch (.two6 11) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 114 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 11) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 11)).plus a) (fullCap top)) : Covered top (.two6 11) a := by
  change 13+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 114 := by omega
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
end Band17

namespace Band18
namespace Top1
private def b0 : PaidBatch (.two6 12) 1 := packedBatch [12385289732,13484200460,26146807316,22747722788,25164499704,30219482360] (by decide +kernel)
private def b1 : PaidBatch (.two6 12) 1 := packedBatch [28097170272,29728757600] (by decide +kernel)
private def batches : List (PaidBatch (.two6 12) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 113 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 12) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 12) 2 := packedBatch [12397874184,13224155152,25345696280,23821465124,25701371128,31297419000] (by decide +kernel)
private def b1 : PaidBatch (.two6 12) 2 := packedBatch [28097170784,30534063968] (by decide +kernel)
private def batches : List (PaidBatch (.two6 12) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 113 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 12) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 12) 3 := packedBatch [22896218636,26159392284,23553030696,25969807096,31033178872,29175107424] (by decide +kernel)
private def b1 : PaidBatch (.two6 12) 3 := packedBatch [30534064480] (by decide +kernel)
private def batches : List (PaidBatch (.two6 12) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 113 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 12) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 12) 4 := packedBatch [21025560592,25358281244,23821466664,26506678008,30227873016,29443542880] (by decide +kernel)
private def b1 : PaidBatch (.two6 12) 4 := packedBatch [30802499936] (by decide +kernel)
private def batches : List (PaidBatch (.two6 12) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 113 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 12) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 12) 5 := packedBatch [22111886868,25366671392,23553065004,26775146748,29963632892,28906672484] (by decide +kernel)
private def b1 : PaidBatch (.two6 12) 5 := packedBatch [31339370852] (by decide +kernel)
private def batches : List (PaidBatch (.two6 12) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 113 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 12) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 12) 6 := packedBatch [21583406104,24833995812,23284630060,26238276348,30773134076,29716173668] (by decide +kernel)
private def b1 : PaidBatch (.two6 12) 6 := packedBatch [30802500452] (by decide +kernel)
private def batches : List (PaidBatch (.two6 12) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 113 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 12) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 12) 7 := packedBatch [21591796252,25916127272,22479324720,25969841404,30240458492,33218418020] (by decide +kernel)
private def batches : List (PaidBatch (.two6 12) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 113 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 12) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 12) 8 := packedBatch [17597083680,21942454320,32094335220,25969841404,29435152636,33218418020] (by decide +kernel)
private def batches : List (PaidBatch (.two6 12) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 113 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 12) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 12) 9 := packedBatch [31834289700,21137181748,29170912512,32413112064] (by decide +kernel)
private def batches : List (PaidBatch (.two6 12) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 113 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 12) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 12) 10 := packedBatch [29959437352,20868746804,29711978240,31607806208] (by decide +kernel)
private def batches : List (PaidBatch (.two6 12) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 113 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 12) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 12) 11 := packedBatch [24358371884,26775147260,29967827708,29447738212,30802500452] (by decide +kernel)
private def batches : List (PaidBatch (.two6 12) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 113 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 12) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 12)).plus a) (fullCap top)) : Covered top (.two6 12) a := by
  change 14+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 113 := by omega
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
end Band18

namespace Band19
namespace Top1
private def b0 : PaidBatch (.two6 13) 1 := packedBatch [13995869700,15363215884,29636435476,25432044580,28385692404,34245981428] (by decide +kernel)
private def b1 : PaidBatch (.two6 13) 1 := packedBatch [31586798428,33486821212] (by decide +kernel)
private def batches : List (PaidBatch (.two6 13) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 112 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 13) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 13) 2 := packedBatch [30940859400,28298453528,26505786916,28654128372,35323918068,31586798940] (by decide +kernel)
private def b1 : PaidBatch (.two6 13) 2 := packedBatch [34292127580] (by decide +kernel)
private def batches : List (PaidBatch (.two6 13) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 112 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 13) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 13) 3 := packedBatch [25580540428,29380584988,26774256168,29191032568,35059677944,32664735584] (by decide +kernel)
private def b1 : PaidBatch (.two6 13) 3 := packedBatch [34023692640] (by decide +kernel)
private def batches : List (PaidBatch (.two6 13) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 112 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 13) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 13) 4 := packedBatch [23441446928,28579473948,27042692136,29996338936,33985936632,32933171040] (by decide +kernel)
private def b1 : PaidBatch (.two6 13) 4 := packedBatch [34560563552] (by decide +kernel)
private def batches : List (PaidBatch (.two6 13) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 112 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 13) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 13) 5 := packedBatch [24796208660,28319428640,25968951340,29727903992,33453261048,32396300640] (by decide +kernel)
private def b1 : PaidBatch (.two6 13) 5 := packedBatch [34828999008] (by decide +kernel)
private def batches : List (PaidBatch (.two6 13) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 112 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 13) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 13) 6 := packedBatch [23999292440,27786753060,25700516396,29191033592,34262762232,32937366368] (by decide +kernel)
private def b1 : PaidBatch (.two6 13) 6 := packedBatch [34292128608] (by decide +kernel)
private def batches : List (PaidBatch (.two6 13) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 112 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 13) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 13) 7 := packedBatch [24007682588,28868884520,25163679280,28654163196,33730086652,36708046176] (by decide +kernel)
private def batches : List (PaidBatch (.two6 13) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 112 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 13) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 13) 8 := packedBatch [35583963168,24626808880,28922598652,32656345340,36708046176] (by decide +kernel)
private def batches : List (PaidBatch (.two6 13) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 112 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 13) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 13) 9 := packedBatch [35323917860,23284632628,32392105212,35902740220] (by decide +kernel)
private def batches : List (PaidBatch (.two6 13) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 112 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 13) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 13) 10 := packedBatch [33180630056,22747762228,31070080764,32933171040,34828999008] (by decide +kernel)
private def batches : List (PaidBatch (.two6 13) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 112 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 13) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 13) 11 := packedBatch [26774258220,29459469048,33189020408,32668930912,34023693152] (by decide +kernel)
private def batches : List (PaidBatch (.two6 13) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 112 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 13) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 13)).plus a) (fullCap top)) : Covered top (.two6 13) a := by
  change 15+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 112 := by omega
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
end Band19

namespace Band20
namespace Top1
private def b0 : PaidBatch (.two6 14) 1 := packedBatch [16143320580,17510666764,34199805460,29727011876,32949095156,39346222324] (by decide +kernel)
private def b1 : PaidBatch (.two6 14) 1 := packedBatch [36418603868,38587062108] (by decide +kernel)
private def batches : List (PaidBatch (.two6 14) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 111 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 14) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 14) 2 := packedBatch [35772664840,32593388056,30800754212,33217531124,40424158964,36150168924] (by decide +kernel)
private def b1 : PaidBatch (.two6 14) 2 := packedBatch [39392368476] (by decide +kernel)
private def batches : List (PaidBatch (.two6 14) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 111 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 14) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 14) 3 := packedBatch [29338604044,33675519516,30263884328,39891483380,44224204532] (by decide +kernel)
private def batches : List (PaidBatch (.two6 14) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 111 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 14) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 14) 4 := packedBatch [26662639632,32605973020,30532320296,34022838004,38817742068,37496541020] (by decide +kernel)
private def b1 : PaidBatch (.two6 14) 4 := packedBatch [39392368988] (by decide +kernel)
private def batches : List (PaidBatch (.two6 14) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 111 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 14) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 14) 5 := packedBatch [28017401364,32077492256,29727047724,38016631032,43687334136] (by decide +kernel)
private def batches : List (PaidBatch (.two6 14) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 111 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 14) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 14) 6 := packedBatch [27220485144,31276381220,29458612780,38826132216,42882028280] (by decide +kernel)
private def batches : List (PaidBatch (.two6 14) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 111 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 14) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 14) 7 := packedBatch [26960439836,32626948136,28116436528,38293456632,41808286968] (by decide +kernel)
private def batches : List (PaidBatch (.two6 14) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 111 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 14) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 14) 8 := packedBatch [40415768608,27579566128,36951279864,41539851512] (by decide +kernel)
private def batches : List (PaidBatch (.two6 14) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 111 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 14) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 14) 9 := packedBatch [39618852388,26505858100,36418604284,40466110204] (by decide +kernel)
private def batches : List (PaidBatch (.two6 14) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 111 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 14) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 14) 10 := packedBatch [37207129128,25968987700,36959670012,39392368892] (by decide +kernel)
private def batches : List (PaidBatch (.two6 14) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 111 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 14) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 14) 11 := packedBatch [30263919148,37483954936,42076721912] (by decide +kernel)
private def batches : List (PaidBatch (.two6 14) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 111 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 14) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 14)).plus a) (fullCap top)) : Covered top (.two6 14) a := by
  change 16+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 111 := by omega
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
end Band20


end Low52At2390PriceTableTwo6C
