import ProximityPrize.SubmissionLower.Low52At2390PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low52At2390PriceTableOne3
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low52At2390Price (fullCap)
open Low52At2390PriceCaps (Band start)
open Low52At2390PriceTableBase (Covered)
open Low52At2390PriceTableCover (PaidBatch packedBatch tilesOf checks checks_join Certificate)

namespace Top1
private def b0 : PaidBatch .one3 1 := packedBatch [285148676,287311880,559942152,2990476296,6505304588,6553640468] (by decide +kernel)
private def b1 : PaidBatch .one3 1 := packedBatch [11754649124,557779204,1098844932,7872651016,9508432648,12829380368] (by decide +kernel)
private def b2 : PaidBatch .one3 1 := packedBatch [11144214288,12511560464,13878906760,15246252936] (by decide +kernel)
private def batches : List (PaidBatch .one3 1) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 126 3 48 = true := by decide +kernel
def receipt : Certificate .one3 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch .one3 2 := packedBatch [2990476296,4076802572,7323195408,6830498840,12023118376,13006480652] (by decide +kernel)
private def b1 : PaidBatch .one3 2 := packedBatch [13366251796,11957910292,12784191252,14688407944,15514688904] (by decide +kernel)
private def batches : List (PaidBatch .one3 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 126 6 45 = true := by decide +kernel
def receipt : Certificate .one3 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch .one3 3 := packedBatch [6505304588,7331585556,6834694172,12291554344,12742240524,13366252308] (by decide +kernel)
private def b1 : PaidBatch .one3 3 := packedBatch [12498976020,13325256980,13903617416,14688408456,14700993988,14977819588] (by decide +kernel)
private def batches : List (PaidBatch .one3 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 126 9 42 = true := by decide +kernel
def receipt : Certificate .one3 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch .one3 4 := packedBatch [6513694736,7876846104,7379987488,12291555372,13555936528,13634688276] (by decide +kernel)
private def b1 : PaidBatch .one3 4 := packedBatch [12503171348,13866322708,14172053384,15229474184,14700994500,15246255044] (by decide +kernel)
private def batches : List (PaidBatch .one3 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 126 12 39 = true := by decide +kernel
def receipt : Certificate .one3 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch .one3 5 := packedBatch [10838023700,13291696160,12291555884,13903123732,12775801620,13597887764] (by decide +kernel)
private def b1 : PaidBatch .one3 5 := packedBatch [13886838152,14440488840,14147343812,14424169412,14969429956,15514690500] (by decide +kernel)
private def batches : List (PaidBatch .one3 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 126 15 36 = true := by decide +kernel
def receipt : Certificate .one3 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch .one3 6 := packedBatch [11655914520,13300086308,12291589680,12258985752,13903157016,14708924300] (by decide +kernel)
private def b1 : PaidBatch .one3 6 := packedBatch [12779997068,14138953612,15229474700,14977590212,15237865412,15242060768] (by decide +kernel)
private def b2 : PaidBatch .one3 6 := packedBatch [15514691040] (by decide +kernel)
private def batches : List (PaidBatch .one3 6) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 126 18 33 = true := by decide +kernel
def receipt : Certificate .one3 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch .one3 7 := packedBatch [11664304668,13304281640,12291590192,12800051480,13903157528,14159468940] (by decide +kernel)
private def b1 : PaidBatch .one3 7 := packedBatch [14440489356,13321062796,14411583884,15514460612,14419974596,14965235140] (by decide +kernel)
private def b2 : PaidBatch .one3 7 := packedBatch [15510495712,15514691040] (by decide +kernel)
private def batches : List (PaidBatch .one3 7) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 126 21 30 = true := by decide +kernel
def receipt : Certificate .one3 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch .one3 8 := packedBatch [9821073440,11754720308,11672695056,13849542416,12804246808,13903158040] (by decide +kernel)
private def b1 : PaidBatch .one3 8 := packedBatch [14708924812,13866323340,14415779212,15502105484,15514460612,15246157280] (by decide +kernel)
private def b2 : PaidBatch .one3 8 := packedBatch [15237865952,15510496224,15514658288,1795577] (by decide +kernel)
private def batches : List (PaidBatch .one3 8) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 126 24 27 = true := by decide +kernel
def receipt : Certificate .one3 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch .one3 9 := packedBatch [9288398372,11754720820,11681085200,13853737744,12535811864,13903158040] (by decide +kernel)
private def b1 : PaidBatch .one3 9 := packedBatch [14708924812,13597888396,14684214668,15502105484,15514460612,15514592736] (by decide +kernel)
private def b2 : PaidBatch .one3 9 := packedBatch [15237865952,15510496224,15514625520,1795573,1795577] (by decide +kernel)
private def batches : List (PaidBatch .one3 9) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 126 27 24 = true := by decide +kernel
def receipt : Certificate .one3 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch .one3 10 := packedBatch [9565256744,11217883704,12767411476,13862127892,12271571740,13634723100] (by decide +kernel)
private def b1 : PaidBatch .one3 10 := packedBatch [15514230156,14143148940,14688409996,14969200068,15246025668,15514592736] (by decide +kernel)
private def b2 : PaidBatch .one3 10 := packedBatch [15233670624,15237865952,15510496224,15514625520,1795573,1828345] (by decide +kernel)
private def batches : List (PaidBatch .one3 10) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 126 30 21 = true := by decide +kernel
def receipt : Certificate .one3 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch .one3 11 := packedBatch [13633733164,14976865556,13044237076,13866323220,15245795208,14684214664] (by decide +kernel)
private def b1 : PaidBatch .one3 11 := packedBatch [14961040264,15514461124,15506300868,15514592736,15510496224,1795569] (by decide +kernel)
private def b2 : PaidBatch .one3 11 := packedBatch [1795573,1828345] (by decide +kernel)
private def batches : List (PaidBatch .one3 11) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 126 33 18 = true := by decide +kernel
def receipt : Certificate .one3 11 := ⟨batches, i33⟩
end Top11

namespace Top12
private def b0 : PaidBatch .one3 12 := packedBatch [12828461104,14440028440,13052627224,14680019224,14159468940,14977360268] (by decide +kernel)
private def b1 : PaidBatch .one3 12 := packedBatch [14973395396,14977590724,14419974596,15233670596,15514592736,15237865952] (by decide +kernel)
private def b2 : PaidBatch .one3 12 := packedBatch [15510496224,1795569,1795573,1828345] (by decide +kernel)
private def batches : List (PaidBatch .one3 12) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i36 : checks tiles 126 36 15 = true := by decide +kernel
def receipt : Certificate .one3 12 := ⟨batches, i36⟩
end Top12

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one3).plus a) (fullCap top)) : Covered top .one3 a := by
  change 1+a.b ≤ 127 ∧ 3+a.j ≤ 53 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 126 := by omega
  have hj' : a.j ≤ 50 := by omega
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

end Low52At2390PriceTableOne3
