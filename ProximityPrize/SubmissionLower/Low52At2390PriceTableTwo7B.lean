import ProximityPrize.SubmissionLower.Low52At2390PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low52At2390PriceTableTwo7B
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low52At2390Price (fullCap)
open Low52At2390PriceCaps (Band start)
open Low52At2390PriceTableBase (Covered)
open Low52At2390PriceTableCover (PaidBatch packedBatch tilesOf checks checks_join Certificate)

namespace Band25
namespace Top1
private def b0 : PaidBatch (.two7 4) 1 := packedBatch [9969600004,9453703692,21042568212,18717094436,24309936900,28114176260] (by decide +kernel)
private def batches : List (PaidBatch (.two7 4) 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 120 3 44 = true := by decide +kernel
def receipt : Certificate (.two7 4) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two7 4) 2 := packedBatch [22351186952,20782522904,18717095460,24314132228,28114176772] (by decide +kernel)
private def batches : List (PaidBatch (.two7 4) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 120 6 41 = true := by decide +kernel
def receipt : Certificate (.two7 4) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two7 4) 3 := packedBatch [18869916172,19981411868,19522435112,25123633416,28114177288] (by decide +kernel)
private def batches : List (PaidBatch (.two7 4) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 120 9 38 = true := by decide +kernel
def receipt : Certificate (.two7 4) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two7 4) 4 := packedBatch [17267693584,21063543324,18985565224,25127828744,27845742344] (by decide +kernel)
private def batches : List (PaidBatch (.two7 4) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 120 12 35 = true := by decide +kernel
def receipt : Certificate (.two7 4) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two7 4) 5 := packedBatch [16739212820,20530867744,18985565740,24322522888,28114177800] (by decide +kernel)
private def batches : List (PaidBatch (.two7 4) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 120 15 32 = true := by decide +kernel
def receipt : Certificate (.two7 4) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two7 4) 6 := packedBatch [29934494744,18448695852,24058282760,27577307400] (by decide +kernel)
private def batches : List (PaidBatch (.two7 4) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 120 18 29 = true := by decide +kernel
def receipt : Certificate (.two7 4) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two7 4) 7 := packedBatch [27254336028,18448729136,24599348492,27040437004] (by decide +kernel)
private def batches : List (PaidBatch (.two7 4) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 120 21 26 = true := by decide +kernel
def receipt : Certificate (.two7 4) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two7 4) 8 := packedBatch [26725855264,30798530608] (by decide +kernel)
private def batches : List (PaidBatch (.two7 4) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 120 24 23 = true := by decide +kernel
def receipt : Certificate (.two7 4) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two7 4) 9 := packedBatch [24851002916,29993224756] (by decide +kernel)
private def batches : List (PaidBatch (.two7 4) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 120 27 20 = true := by decide +kernel
def receipt : Certificate (.two7 4) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two7 4) 10 := packedBatch [21133048872,24859393288,28382613256] (by decide +kernel)
private def batches : List (PaidBatch (.two7 4) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 120 30 17 = true := by decide +kernel
def receipt : Certificate (.two7 4) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two7 4) 11 := packedBatch [19254002220,23789847304,27577307400] (by decide +kernel)
private def batches : List (PaidBatch (.two7 4) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 120 33 14 = true := by decide +kernel
def receipt : Certificate (.two7 4) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two7 4)).plus a) (fullCap top)) : Covered top (.two7 4) a := by
  change 7+a.b ≤ 127 ∧ 7+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 120 := by omega
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
end Band25

namespace Band26
namespace Top1
private def b0 : PaidBatch (.two7 5) 1 := packedBatch [11580179972,10795848204,24263760916,21669884452,28068000516,32409110788] (by decide +kernel)
private def batches : List (PaidBatch (.two7 5) 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 119 3 44 = true := by decide +kernel
def receipt : Certificate (.two7 5) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two7 5) 2 := packedBatch [25572379656,23735280152,21669885476,27803760388,32140675844] (by decide +kernel)
private def batches : List (PaidBatch (.two7 5) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 119 6 41 = true := by decide +kernel
def receipt : Certificate (.two7 5) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two7 5) 3 := packedBatch [21285802508,22934169116,22206756904,28881697028,31872240900] (by decide +kernel)
private def batches : List (PaidBatch (.two7 5) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 119 9 38 = true := by decide +kernel
def receipt : Certificate (.two7 5) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two7 5) 4 := packedBatch [19683579920,24016300572,21669887016,28349021444,31603805956] (by decide +kernel)
private def batches : List (PaidBatch (.two7 5) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 119 12 35 = true := by decide +kernel
def receipt : Certificate (.two7 5) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two7 5) 5 := packedBatch [18886663700,23215189536,21938355756,27543715592,31872241416] (by decide +kernel)
private def batches : List (PaidBatch (.two7 5) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 119 15 32 = true := by decide +kernel
def receipt : Certificate (.two7 5) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two7 5) 6 := packedBatch [20241425432,23223579684,20864614956,27279475464,31335371016] (by decide +kernel)
private def batches : List (PaidBatch (.two7 5) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 119 18 29 = true := by decide +kernel
def receipt : Certificate (.two7 5) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two7 5) 7 := packedBatch [30743964188,20596180016,27820541192,30530065160] (by decide +kernel)
private def batches : List (PaidBatch (.two7 5) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 119 21 26 = true := by decide +kernel
def receipt : Certificate (.two7 5) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two7 5) 8 := packedBatch [30215483424,19790874672,27556301064,29724759304] (by decide +kernel)
private def batches : List (PaidBatch (.two7 5) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 119 24 23 = true := by decide +kernel
def receipt : Certificate (.two7 5) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two7 5) 9 := packedBatch [28072195620,34019723828] (by decide +kernel)
private def batches : List (PaidBatch (.two7 5) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 119 27 20 = true := by decide +kernel
def receipt : Certificate (.two7 5) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two7 5) 10 := packedBatch [23548935208,28080585988,32140676868] (by decide +kernel)
private def batches : List (PaidBatch (.two7 5) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 119 30 17 = true := by decide +kernel
def receipt : Certificate (.two7 5) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two7 5) 11 := packedBatch [21669921324,26742604552,31335371016] (by decide +kernel)
private def batches : List (PaidBatch (.two7 5) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 119 33 14 = true := by decide +kernel
def receipt : Certificate (.two7 5) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two7 5)).plus a) (fullCap top)) : Covered top (.two7 5) a := by
  change 8+a.b ≤ 127 ∧ 7+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 119 := by omega
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
end Band26

namespace Band27
namespace Top1
private def b0 : PaidBatch (.two7 6) 1 := packedBatch [13459195396,12674863628,28558695444,25159512612,27844790528,32899805952] (by decide +kernel)
private def b1 : PaidBatch (.two7 6) 1 := packedBatch [30509058416,32409081200] (by decide +kernel)
private def batches : List (PaidBatch (.two7 6) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 118 3 44 = true := by decide +kernel
def receipt : Certificate (.two7 6) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two7 6) 2 := packedBatch [30135749640,27761779224,25159513636,28113226496,32635565824,37777787760] (by decide +kernel)
private def batches : List (PaidBatch (.two7 6) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 118 6 41 = true := by decide +kernel
def receipt : Certificate (.two7 6) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two7 6) 3 := packedBatch [25043866124,26692232732,25964853288,33713502468,37240917252] (by decide +kernel)
private def batches : List (PaidBatch (.two7 6) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 118 9 38 = true := by decide +kernel
def receipt : Certificate (.two7 6) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two7 6) 4 := packedBatch [22904772624,27774364188,25159547944,33180826884,36704046852] (by decide +kernel)
private def batches : List (PaidBatch (.two7 6) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 118 12 35 = true := by decide +kernel
def receipt : Certificate (.two7 6) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two7 6) 5 := packedBatch [21839420948,26973253152,25159548460,32107085572,36972482308] (by decide +kernel)
private def batches : List (PaidBatch (.two7 6) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 118 15 32 = true := by decide +kernel
def receipt : Certificate (.two7 6) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two7 6) 6 := packedBatch [23462618136,26981643300,24085807660,31842845444,36167176452] (by decide +kernel)
private def batches : List (PaidBatch (.two7 6) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 118 18 29 = true := by decide +kernel
def receipt : Certificate (.two7 6) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two7 6) 7 := packedBatch [35844205084,24085840944,32383911176,35361870600] (by decide +kernel)
private def batches : List (PaidBatch (.two7 6) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 118 21 26 = true := by decide +kernel
def receipt : Certificate (.two7 6) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two7 6) 8 := packedBatch [34778853408,23012100144,31851235592,34556564744] (by decide +kernel)
private def batches : List (PaidBatch (.two7 6) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 118 24 23 = true := by decide +kernel
def receipt : Certificate (.two7 6) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two7 6) 9 := packedBatch [32635565604,22475229748,30777494280,34288129288] (by decide +kernel)
private def batches : List (PaidBatch (.two7 6) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 118 27 20 = true := by decide +kernel
def receipt : Certificate (.two7 6) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two7 6) 10 := packedBatch [27307031592,32375520516,36972482308] (by decide +kernel)
private def batches : List (PaidBatch (.two7 6) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 118 30 17 = true := by decide +kernel
def receipt : Certificate (.two7 6) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two7 6) 11 := packedBatch [24891114028,30769103620,35898740996] (by decide +kernel)
private def batches : List (PaidBatch (.two7 6) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 118 33 14 = true := by decide +kernel
def receipt : Certificate (.two7 6) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two7 6)).plus a) (fullCap top)) : Covered top (.two7 6) a := by
  change 9+a.b ≤ 127 ∧ 7+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 118 := by omega
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
end Band27

namespace Band28
namespace Top1
private def b0 : PaidBatch (.two7 7) 1 := packedBatch [16680388100,15627620876,35001113620,31065092644,40147530496,46367688960] (by decide +kernel)
private def batches : List (PaidBatch (.two7 7) 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 117 3 44 = true := by decide +kernel
def receipt : Certificate (.two7 7) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two7 7) 2 := packedBatch [37115038728,33667326488,30796658212,39614854912,45830818560] (by decide +kernel)
private def batches : List (PaidBatch (.two7 7) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 117 6 41 = true := by decide +kernel
def receipt : Certificate (.two7 7) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two7 7) 3 := packedBatch [30412542476,32329344540,31333529640,40692791552,45025512704] (by decide +kernel)
private def batches : List (PaidBatch (.two7 7) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 117 9 38 = true := by decide +kernel
def receipt : Certificate (.two7 7) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two7 7) 4 := packedBatch [27736578064,33411475996,30259788840,39891680512,44220206848] (by decide +kernel)
private def batches : List (PaidBatch (.two7 7) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 117 12 35 = true := by decide +kernel
def receipt : Certificate (.two7 7) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two7 7) 5 := packedBatch [26402790932,32341929504,30259822124,38549503748,44488642308] (by decide +kernel)
private def batches : List (PaidBatch (.two7 7) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 117 15 32 = true := by decide +kernel
def receipt : Certificate (.two7 7) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two7 7) 6 := packedBatch [28025988120,32350319652,28917645868,38016828164,43414900996] (by decide +kernel)
private def batches : List (PaidBatch (.two7 7) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 117 18 29 = true := by decide +kernel
def receipt : Certificate (.two7 7) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two7 7) 7 := packedBatch [42555058716,28380775472,38557893892,42072724228] (by decide +kernel)
private def batches : List (PaidBatch (.two7 7) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 117 21 26 = true := by decide +kernel
def receipt : Certificate (.two7 7) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two7 7) 8 := packedBatch [41489707040,27038599216,38025218308,40998982916] (by decide +kernel)
private def batches : List (PaidBatch (.two7 7) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 117 24 23 = true := by decide +kernel
def receipt : Certificate (.two7 7) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two7 7) 9 := packedBatch [38541112868,26770197044,36683041544,40730547464] (by decide +kernel)
private def batches : List (PaidBatch (.two7 7) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 117 27 20 = true := by decide +kernel
def receipt : Certificate (.two7 7) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two7 7) 10 := packedBatch [32138837032,38281067776,43951771392] (by decide +kernel)
private def batches : List (PaidBatch (.two7 7) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 117 30 17 = true := by decide +kernel
def receipt : Certificate (.two7 7) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two7 7) 11 := packedBatch [29454516780,36406215428,42341159172] (by decide +kernel)
private def batches : List (PaidBatch (.two7 7) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 117 33 14 = true := by decide +kernel
def receipt : Certificate (.two7 7) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two7 7)).plus a) (fullCap top)) : Covered top (.two7 7) a := by
  change 10+a.b ≤ 127 ∧ 7+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 117 := by omega
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
end Band28


end Low52At2390PriceTableTwo7B
