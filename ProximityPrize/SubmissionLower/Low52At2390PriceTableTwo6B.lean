import ProximityPrize.SubmissionLower.Low52At2390PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low52At2390PriceTableTwo6B
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low52At2390Price (fullCap)
open Low52At2390PriceCaps (Band start)
open Low52At2390PriceTableBase (Covered)
open Low52At2390PriceTableCover (PaidBatch packedBatch tilesOf checks checks_join Certificate)

namespace Band11
namespace Top1
private def b0 : PaidBatch (.two6 5) 1 := packedBatch [7285245444,8115720716,15409618452,13352580132,17871680772,20602178308] (by decide +kernel)
private def batches : List (PaidBatch (.two6 5) 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 120 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 5) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 5) 2 := packedBatch [16177171464,14876942872,14157887012,18681181956,20602178820] (by decide +kernel)
private def batches : List (PaidBatch (.two6 5) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 120 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 5) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 5) 3 := packedBatch [13501207052,15690638876,14157920808,18685377288,20602179336] (by decide +kernel)
private def batches : List (PaidBatch (.two6 5) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 120 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 5) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 5) 4 := packedBatch [12704290832,15426398748,14426356776,18148506888,21139050248] (by decide +kernel)
private def batches : List (PaidBatch (.two6 5) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 120 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 5) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 5) 5 := packedBatch [13253746196,15434788896,14157922348,18152702216,20870615304] (by decide +kernel)
private def batches : List (PaidBatch (.two6 5) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 120 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 5) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 5) 6 := packedBatch [13262136344,15170548772,14157922860,18693767944,20602180360] (by decide +kernel)
private def batches : List (PaidBatch (.two6 5) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 120 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 5) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 5) 7 := packedBatch [21352950300,13889521200,18429527820,20333745420] (by decide +kernel)
private def batches : List (PaidBatch (.two6 5) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 120 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 5) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 5) 8 := packedBatch [19746533408,13621086256,23823403276] (by decide +kernel)
private def batches : List (PaidBatch (.two6 5) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 120 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 5) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 5) 9 := packedBatch [19486488100,22749662260] (by decide +kernel)
private def batches : List (PaidBatch (.two6 5) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 120 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 5) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 5) 10 := packedBatch [18416942120,21944356404] (by decide +kernel)
private def batches : List (PaidBatch (.two6 5) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 120 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 5) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 5) 11 := packedBatch [14963229228,18693767944,20870615816] (by decide +kernel)
private def batches : List (PaidBatch (.two6 5) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 120 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 5) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 5)).plus a) (fullCap top)) : Covered top (.two6 5) a := by
  change 7+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 120 := by omega
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
end Band11

namespace Band12
namespace Top1
private def b0 : PaidBatch (.two6 6) 1 := packedBatch [7553648132,8384123404,16214892052,14426321956,18676954372,21675887364] (by decide +kernel)
private def batches : List (PaidBatch (.two6 6) 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 119 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 6) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 6) 2 := packedBatch [16982445064,15682216472,14963193380,19754891012,21675887876] (by decide +kernel)
private def batches : List (PaidBatch (.two6 6) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 119 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 6) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 6) 3 := packedBatch [14306480652,16495912476,14963194408,19490650884,21675888388] (by decide +kernel)
private def batches : List (PaidBatch (.two6 6) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 119 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 6) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 6) 4 := packedBatch [13241128976,16231672348,15231630376,19222215940,22212759300] (by decide +kernel)
private def batches : List (PaidBatch (.two6 6) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 119 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 6) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 6) 5 := packedBatch [14059019796,16240062496,14963228716,19226411272,21944324360] (by decide +kernel)
private def batches : List (PaidBatch (.two6 6) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 119 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 6) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 6) 6 := packedBatch [13798974488,15975822372,14963229228,19767477000,21675889416] (by decide +kernel)
private def batches : List (PaidBatch (.two6 6) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 119 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 6) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 6) 7 := packedBatch [22426659356,14426359344,19503236872,21407454472] (by decide +kernel)
private def batches : List (PaidBatch (.two6 6) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 119 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 6) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 6) 8 := packedBatch [20820242464,14157924400,18966366472,21407454472] (by decide +kernel)
private def batches : List (PaidBatch (.two6 6) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 119 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 6) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 6) 9 := packedBatch [20560197156,23823371316] (by decide +kernel)
private def batches : List (PaidBatch (.two6 6) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 119 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 6) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 6) 10 := packedBatch [17110678568,19490651396,23286501124] (by decide +kernel)
private def batches : List (PaidBatch (.two6 6) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 119 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 6) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 6) 11 := packedBatch [15768535596,19767477000,21944324872] (by decide +kernel)
private def batches : List (PaidBatch (.two6 6) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 119 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 6) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 6)).plus a) (fullCap top)) : Covered top (.two6 6) a := by
  change 8+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 119 := by omega
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
end Band12

namespace Band13
namespace Top1
private def b0 : PaidBatch (.two6 7) 1 := packedBatch [8090486276,8920961548,17288601108,14963160100,20019098880,23018031872] (by decide +kernel)
private def batches : List (PaidBatch (.two6 7) 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 118 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 7) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 7) 2 := packedBatch [18056154120,16755925528,15768466980,20828600064,23018032384] (by decide +kernel)
private def batches : List (PaidBatch (.two6 7) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 118 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 7) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 7) 3 := packedBatch [15111754252,17569621532,16036936232,20832795396,23018032900] (by decide +kernel)
private def batches : List (PaidBatch (.two6 7) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 118 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 7) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 7) 4 := packedBatch [14046402576,17036945948,16305372200,20295924996,23554903812] (by decide +kernel)
private def batches : List (PaidBatch (.two6 7) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 118 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 7) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 7) 5 := packedBatch [14864293396,17045336096,15768502316,20300120324,23286468868] (by decide +kernel)
private def batches : List (PaidBatch (.two6 7) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 118 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 7) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 7) 6 := packedBatch [14604248088,16781095972,15768502828,20841186052,23018033924] (by decide +kernel)
private def batches : List (PaidBatch (.two6 7) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 118 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 7) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 7) 7 := packedBatch [23768803868,15231665712,20576945928,22481163528] (by decide +kernel)
private def batches : List (PaidBatch (.two6 7) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 118 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 7) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 7) 8 := packedBatch [21893951520,15231666224,20040075528,22749598984] (by decide +kernel)
private def batches : List (PaidBatch (.two6 7) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 118 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 7) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 7) 9 := packedBatch [21902341668,25165515828] (by decide +kernel)
private def batches : List (PaidBatch (.two6 7) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 118 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 7) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 7) 10 := packedBatch [20564360232,24628645428] (by decide +kernel)
private def batches : List (PaidBatch (.two6 7) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 118 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 7) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 7) 11 := packedBatch [16573809196,20841186052,23286469380] (by decide +kernel)
private def batches : List (PaidBatch (.two6 7) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 118 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 7) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 7)).plus a) (fullCap top)) : Covered top (.two6 7) a := by
  change 9+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 118 := by omega
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
end Band13

namespace Band14
namespace Top1
private def b0 : PaidBatch (.two6 8) 1 := packedBatch [8627324420,9457799692,18362310164,16305337380,21361243392,24628611840] (by decide +kernel)
private def batches : List (PaidBatch (.two6 8) 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 117 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 8) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 8) 2 := packedBatch [8639908872,9466189840,17829634584,17110644260,22170744576,24628612352] (by decide +kernel)
private def batches : List (PaidBatch (.two6 8) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 117 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 8) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 8) 3 := packedBatch [16185463308,18643330588,16842209832,22174939904,24628612864] (by decide +kernel)
private def batches : List (PaidBatch (.two6 8) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 117 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 8) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 8) 4 := packedBatch [15120111632,18379090460,17110645800,21638069504,25165483776] (by decide +kernel)
private def batches : List (PaidBatch (.two6 8) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 117 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 8) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 8) 5 := packedBatch [15938002452,18387480608,16842244140,21642264836,24897048836] (by decide +kernel)
private def batches : List (PaidBatch (.two6 8) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 117 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 8) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 8) 6 := packedBatch [15677957144,17854805028,16842244652,22183330564,24360178436] (by decide +kernel)
private def batches : List (PaidBatch (.two6 8) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 117 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 8) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 8) 7 := packedBatch [15686347292,18936936488,16305374768,21919090436,24091743492] (by decide +kernel)
private def batches : List (PaidBatch (.two6 8) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 117 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 8) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 8) 8 := packedBatch [23236096032,16036939824,21382220036,24091743492] (by decide +kernel)
private def batches : List (PaidBatch (.two6 8) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 117 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 8) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 8) 9 := packedBatch [23244486180,15500102708,21386415368,23554873096] (by decide +kernel)
private def batches : List (PaidBatch (.two6 8) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 117 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 8) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 8) 10 := packedBatch [19258129448,21906504960,26239225600] (by decide +kernel)
private def batches : List (PaidBatch (.two6 8) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 117 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 8) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 8) 11 := packedBatch [17647551020,21914895108,24897049348] (by decide +kernel)
private def batches : List (PaidBatch (.two6 8) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 117 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 8) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 8)).plus a) (fullCap top)) : Covered top (.two6 8) a := by
  change 10+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 117 := by omega
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
end Band14

namespace Band15
namespace Top1
private def b0 : PaidBatch (.two6 9) 1 := packedBatch [9432598020,10263073292,19704454676,17379046436,22971823356,26239191804] (by decide +kernel)
private def batches : List (PaidBatch (.two6 9) 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 116 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 9) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 9) 2 := packedBatch [9445182472,10271463440,19171779096,18184353316,23781324540,26507627772] (by decide +kernel)
private def batches : List (PaidBatch (.two6 9) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 116 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 9) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 9) 3 := packedBatch [17527607820,19985475100,18184387112,23785519872,26507628288] (by decide +kernel)
private def batches : List (PaidBatch (.two6 9) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 116 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 9) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 9) 4 := packedBatch [16193820688,19452799516,18452823080,23248649472,27044499200] (by decide +kernel)
private def batches : List (PaidBatch (.two6 9) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 116 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 9) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 9) 5 := packedBatch [17011711508,19729625120,17915953196,23252844800,26507628800] (by decide +kernel)
private def batches : List (PaidBatch (.two6 9) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 116 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 9) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 9) 6 := packedBatch [16751666200,19196949540,17915953708,23793910528,26239193856] (by decide +kernel)
private def batches : List (PaidBatch (.two6 9) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 116 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 9) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 9) 7 := packedBatch [16760056348,20279081000,17379116592,23529670404,25702323460] (by decide +kernel)
private def batches : List (PaidBatch (.two6 9) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 116 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 9) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 9) 8 := packedBatch [24846676000,17110681648,22992800004,25702323460] (by decide +kernel)
private def batches : List (PaidBatch (.two6 9) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 116 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 9) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 9) 9 := packedBatch [24855066148,16573811764,22728559876,25165453060] (by decide +kernel)
private def batches : List (PaidBatch (.two6 9) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 116 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 9) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 9) 10 := packedBatch [23517084712,16036941364,21943373572,23269625708,24628582764] (by decide +kernel)
private def batches : List (PaidBatch (.two6 9) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 116 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 9) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 9) 11 := packedBatch [18989695532,23525475072,26507629312] (by decide +kernel)
private def batches : List (PaidBatch (.two6 9) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 116 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 9) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 9)).plus a) (fullCap top)) : Covered top (.two6 9) a := by
  change 11+a.b ≤ 127 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 116 := by omega
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
end Band15


end Low52At2390PriceTableTwo6B
