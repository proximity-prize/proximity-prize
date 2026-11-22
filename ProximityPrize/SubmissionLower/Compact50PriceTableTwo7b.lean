import ProximityPrize.SubmissionLower.LambdaC53TiltedPrice
import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo7b
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1
private def batch0 : PaidBatch .two7b 1 := ⟨[
  .rectangle 1 3 113 10 85,
  .rectangle 4 11 123 18 109,
  .rectangle 7 19 123 26 115,
  .rectangle 9 27 123 34 116,
  .rectangle 12 35 109 42 116,
  .rectangle 15 43 113 46 116], by decide +kernel⟩
private def batch1 : PaidBatch .two7b 1 := ⟨[
  .rectangle 110 35 121 40 119,
  .rectangle 110 41 120 44 120,
  .rectangle 114 3 123 9 85,
  .rectangle 114 10 123 17 85,
  .rectangle 114 45 121 46 120,
  .rectangle 121 41 123 43 120], by decide +kernel⟩
private def batch2 : PaidBatch .two7b 1 := ⟨[
  .rectangle 121 44 123 45 120,
  .rectangle 122 35 123 39 119,
  .rectangle 122 40 123 42 120,
  .rectangle 122 46 123 46 120], by decide +kernel⟩

private def batches : List (PaidBatch .two7b 1) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 123 3 25 = true := by decide +kernel
private theorem index28 : checks tiles 123 28 19 = true := by decide +kernel
private theorem covers : checks tiles 123 3 44 = true :=
  checks_join (index3) index28

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 3 .two7b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2
private def batch0 : PaidBatch .two7b 2 := ⟨[
  .rectangle 2 6 123 13 85,
  .rectangle 5 14 123 21 110,
  .rectangle 8 22 123 29 115,
  .rectangle 10 30 115 37 116,
  .rectangle 13 38 103 45 116,
  .rectangle 16 46 118 46 116], by decide +kernel⟩
private def batch1 : PaidBatch .two7b 2 := ⟨[
  .rectangle 104 38 123 41 119,
  .rectangle 104 42 121 44 120,
  .rectangle 104 45 119 46 120,
  .rectangle 116 30 123 35 116,
  .rectangle 116 36 122 40 119,
  .rectangle 120 45 123 45 120], by decide +kernel⟩
private def batch2 : PaidBatch .two7b 2 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 120 46 122 46 120,
  .rectangle 122 42 123 43 120,
  .rectangle 122 44 123 44 120,
  .rectangle 123 36 123 39 119,
  .point 123 46 120] (by decide +kernel)

private def batches : List (PaidBatch .two7b 2) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 123 6 25 = true := by decide +kernel
private theorem index31 : checks tiles 123 31 16 = true := by decide +kernel
private theorem covers : checks tiles 123 6 41 = true :=
  checks_join (index6) index31

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 4 .two7b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3
private def batch0 : PaidBatch .two7b 3 := ⟨[
  .rectangle 3 9 123 16 85,
  .rectangle 6 17 123 24 110,
  .rectangle 9 25 123 32 116,
  .rectangle 11 33 108 40 116,
  .rectangle 14 41 104 46 116,
  .rectangle 105 41 121 43 120], by decide +kernel⟩
private def batch1 : PaidBatch .two7b 3 := ⟨[
  .rectangle 105 44 115 46 120,
  .rectangle 109 33 122 38 119,
  .rectangle 109 39 120 42 119,
  .rectangle 116 44 120 45 120,
  .rectangle 116 46 120 46 120,
  .rectangle 121 39 123 41 119], by decide +kernel⟩
private def batch2 : PaidBatch .two7b 3 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 121 44 123 44 120,
  .rectangle 121 45 122 45 120,
  .point 121 46 120,
  .rectangle 122 42 123 43 120,
  .point 122 46 120,
  .rectangle 123 33 123 37 119] (by decide +kernel)
private def batch3 : PaidBatch .two7b 3 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 123 38 123 40 119,
  .point 123 45 120,
  .point 123 46 120] (by decide +kernel)

private def batches : List (PaidBatch .two7b 3) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 123 9 25 = true := by decide +kernel
private theorem index34 : checks tiles 123 34 13 = true := by decide +kernel
private theorem covers : checks tiles 123 9 38 = true :=
  checks_join (index9) index34

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 5 .two7b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4
private def batch0 : PaidBatch .two7b 4 := ⟨[
  .rectangle 4 12 123 19 110,
  .rectangle 7 20 123 27 115,
  .rectangle 10 28 118 35 116,
  .rectangle 12 36 102 43 116,
  .rectangle 15 44 110 46 116,
  .rectangle 103 36 120 40 119], by decide +kernel⟩
private def batch1 : PaidBatch .two7b 4 := ⟨[
  .rectangle 103 41 120 43 120,
  .rectangle 111 44 119 45 120,
  .rectangle 111 46 119 46 120,
  .rectangle 119 28 123 34 116,
  .rectangle 119 35 123 39 119,
  .rectangle 120 44 123 44 120], by decide +kernel⟩
private def batch2 : PaidBatch .two7b 4 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 120 45 121 45 120,
  .point 120 46 120,
  .rectangle 121 40 123 42 120,
  .rectangle 121 43 123 43 120,
  .point 121 46 120,
  .point 122 45 120] (by decide +kernel)
private def batch3 : PaidBatch .two7b 4 := LambdaC53TiltedPrice.fastBatch [
  .point 122 46 120,
  .point 123 45 120,
  .point 123 46 120] (by decide +kernel)

private def batches : List (PaidBatch .two7b 4) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 123 12 25 = true := by decide +kernel
private theorem index37 : checks tiles 123 37 10 = true := by decide +kernel
private theorem covers : checks tiles 123 12 35 = true :=
  checks_join (index12) index37

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 6 .two7b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5
private def batch0 : PaidBatch .two7b 5 := ⟨[
  .rectangle 5 15 123 22 110,
  .rectangle 8 23 123 30 116,
  .rectangle 11 31 111 38 116,
  .rectangle 13 39 97 46 116,
  .rectangle 98 39 118 42 119,
  .rectangle 98 43 115 45 120], by decide +kernel⟩
private def batch1 : PaidBatch .two7b 5 := ⟨[
  .rectangle 98 46 118 46 120,
  .rectangle 112 31 123 36 116,
  .rectangle 112 37 123 40 119,
  .rectangle 116 43 120 44 120,
  .rectangle 116 45 121 45 120,
  .rectangle 119 41 123 42 120], by decide +kernel⟩
private def batch2 : PaidBatch .two7b 5 := LambdaC53TiltedPrice.fastBatch [
  .point 119 46 120,
  .point 120 46 120,
  .rectangle 121 43 123 43 120,
  .rectangle 121 44 123 44 120,
  .point 121 46 120,
  .point 122 45 120] (by decide +kernel)
private def batch3 : PaidBatch .two7b 5 := LambdaC53TiltedPrice.fastBatch [
  .point 122 46 120,
  .point 123 45 120,
  .point 123 46 120] (by decide +kernel)

private def batches : List (PaidBatch .two7b 5) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 123 15 25 = true := by decide +kernel
private theorem index40 : checks tiles 123 40 7 = true := by decide +kernel
private theorem covers : checks tiles 123 15 32 = true :=
  checks_join (index15) index40

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 7 .two7b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6
private def batch0 : PaidBatch .two7b 6 := ⟨[
  .rectangle 6 18 123 25 110,
  .rectangle 9 26 123 33 116,
  .rectangle 12 34 105 41 116,
  .rectangle 14 42 104 46 116,
  .rectangle 105 42 117 44 120,
  .rectangle 105 45 115 46 120], by decide +kernel⟩
private def batch1 : PaidBatch .two7b 6 := ⟨[
  .rectangle 106 34 123 38 119,
  .rectangle 106 39 123 41 119,
  .rectangle 116 45 120 45 120,
  .rectangle 116 46 118 46 120,
  .rectangle 118 42 123 43 120,
  .rectangle 118 44 123 44 120], by decide +kernel⟩
private def batch2 : PaidBatch .two7b 6 := LambdaC53TiltedPrice.fastBatch [
  .point 119 46 120,
  .point 120 46 120,
  .point 121 45 120,
  .point 121 46 120,
  .point 122 45 120,
  .point 122 46 120] (by decide +kernel)
private def batch3 : PaidBatch .two7b 6 := LambdaC53TiltedPrice.fastBatch [
  .point 123 45 120,
  .point 123 46 120] (by decide +kernel)

private def batches : List (PaidBatch .two7b 6) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 123 18 25 = true := by decide +kernel
private theorem index43 : checks tiles 123 43 4 = true := by decide +kernel
private theorem covers : checks tiles 123 18 29 = true :=
  checks_join (index18) index43

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 8 .two7b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7
private def batch0 : PaidBatch .two7b 7 := ⟨[
  .rectangle 7 21 123 28 115,
  .rectangle 10 29 117 36 116,
  .rectangle 13 37 99 44 116,
  .rectangle 15 45 111 46 116,
  .rectangle 100 37 123 40 119,
  .rectangle 100 41 120 43 120], by decide +kernel⟩
private def batch1 : PaidBatch .two7b 7 := ⟨[
  .rectangle 100 44 112 46 120,
  .rectangle 113 44 118 45 120,
  .rectangle 113 46 118 46 120,
  .rectangle 118 29 123 35 116,
  .rectangle 118 36 123 39 119,
  .rectangle 119 44 123 44 120], by decide +kernel⟩
private def batch2 : PaidBatch .two7b 7 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 119 45 120 45 120,
  .point 119 46 120,
  .point 120 46 120,
  .rectangle 121 41 123 42 120,
  .rectangle 121 43 123 43 120,
  .point 121 45 120] (by decide +kernel)
private def batch3 : PaidBatch .two7b 7 := LambdaC53TiltedPrice.fastBatch [
  .point 121 46 120,
  .point 122 45 120,
  .point 122 46 120,
  .point 123 45 120,
  .point 123 46 120] (by decide +kernel)

private def batches : List (PaidBatch .two7b 7) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 123 21 25 = true := by decide +kernel
private theorem index46 : checks tiles 123 46 1 = true := by decide +kernel
private theorem covers : checks tiles 123 21 26 = true :=
  checks_join (index21) index46

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 9 .two7b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8
private def batch0 : PaidBatch .two7b 8 := ⟨[
  .rectangle 8 24 123 31 116,
  .rectangle 11 32 110 39 116,
  .rectangle 14 40 98 46 116,
  .rectangle 99 40 117 43 120,
  .rectangle 99 44 113 46 120,
  .rectangle 111 32 123 37 119], by decide +kernel⟩
private def batch1 : PaidBatch .two7b 8 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 111 38 122 41 119,
  .rectangle 114 44 123 44 120,
  .rectangle 114 45 121 45 120,
  .rectangle 114 46 118 46 120,
  .rectangle 118 42 123 43 120,
  .point 119 46 120] (by decide +kernel)
private def batch2 : PaidBatch .two7b 8 := LambdaC53TiltedPrice.fastBatch [
  .point 120 46 120,
  .point 121 46 120,
  .point 122 45 120,
  .point 122 46 120,
  .rectangle 123 38 123 40 119,
  .rectangle 123 41 123 42 120] (by decide +kernel)
private def batch3 : PaidBatch .two7b 8 := LambdaC53TiltedPrice.fastBatch [
  .point 123 45 120,
  .point 123 46 120] (by decide +kernel)

private def batches : List (PaidBatch .two7b 8) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 123 24 23 = true := by decide +kernel
private theorem covers : checks tiles 123 24 23 = true :=
  index24

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 10 .two7b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9
private def batch0 : PaidBatch .two7b 9 := ⟨[
  .rectangle 9 27 123 34 116,
  .rectangle 12 35 104 42 116,
  .rectangle 15 43 106 46 116,
  .rectangle 105 35 123 39 119,
  .rectangle 105 40 123 42 120,
  .rectangle 107 43 121 44 120], by decide +kernel⟩
private def batch1 : PaidBatch .two7b 9 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 107 45 116 46 120,
  .rectangle 117 45 121 45 120,
  .rectangle 117 46 118 46 120,
  .point 119 46 120,
  .point 120 46 120,
  .point 121 46 120] (by decide +kernel)
private def batch2 : PaidBatch .two7b 9 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 122 43 123 43 120,
  .rectangle 122 44 123 44 120,
  .point 122 45 120,
  .point 122 46 120,
  .point 123 45 120,
  .point 123 46 120] (by decide +kernel)

private def batches : List (PaidBatch .two7b 9) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 123 27 20 = true := by decide +kernel
private theorem covers : checks tiles 123 27 20 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 11 .two7b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10
private def batch0 : PaidBatch .two7b 10 := ⟨[
  .rectangle 10 30 117 37 116,
  .rectangle 13 38 98 45 116,
  .rectangle 16 46 115 46 116,
  .rectangle 99 38 123 41 119,
  .rectangle 99 42 119 44 120,
  .rectangle 99 45 116 46 120], by decide +kernel⟩
private def batch1 : PaidBatch .two7b 10 := ⟨[
  .rectangle 117 45 122 45 120,
  .rectangle 117 46 119 46 120,
  .rectangle 118 30 123 36 116,
  .rectangle 118 37 123 40 119,
  .rectangle 120 42 123 43 120,
  .rectangle 120 44 123 44 120], by decide +kernel⟩
private def batch2 : PaidBatch .two7b 10 := LambdaC53TiltedPrice.fastBatch [
  .point 120 46 120,
  .point 121 46 120,
  .point 122 46 120,
  .point 123 45 120,
  .point 123 46 120] (by decide +kernel)

private def batches : List (PaidBatch .two7b 10) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 123 30 17 = true := by decide +kernel
private theorem covers : checks tiles 123 30 17 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 12 .two7b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11
private def batch0 : PaidBatch .two7b 11 := ⟨[
  .rectangle 11 33 110 40 116,
  .rectangle 14 41 102 46 116,
  .rectangle 103 41 122 43 120,
  .rectangle 103 44 114 46 120,
  .rectangle 111 33 123 38 119,
  .rectangle 111 39 121 42 119], by decide +kernel⟩
private def batch1 : PaidBatch .two7b 11 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 115 44 119 45 120,
  .rectangle 115 46 119 46 120,
  .rectangle 120 44 123 44 120,
  .rectangle 120 45 122 45 120,
  .point 120 46 120,
  .point 121 46 120] (by decide +kernel)
private def batch2 : PaidBatch .two7b 11 := LambdaC53TiltedPrice.fastBatch [
  .rectangle 122 39 123 41 119,
  .point 122 46 120,
  .rectangle 123 42 123 43 120,
  .point 123 45 120,
  .point 123 46 120] (by decide +kernel)

private def batches : List (PaidBatch .two7b 11) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 123 33 14 = true := by decide +kernel
private theorem covers : checks tiles 123 33 14 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 13 .two7b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .two7b).plus a) (fullCap top)) : Covered top .two7b a := by
  change 6+a.b ≤ 129 ∧ 7+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 123 := by omega
  have hj' : a.j ≤ 46 := by omega
  have casesTop : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 := by omega
  rcases casesTop with ht1 | ht2 | ht3 | ht4 | ht5 | ht6 | ht7 | ht8 | ht9 | ht10 | ht11
  · exact covered_mono (Top1.exact a ha ht1 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top2.exact a ha ht2 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top3.exact a ha ht3 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top4.exact a ha ht4 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top5.exact a ha ht5 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top6.exact a ha ht6 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top7.exact a ha ht7 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top8.exact a ha ht8 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top9.exact a ha ht9 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top10.exact a ha ht10 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top11.exact a ha ht11 hb' hj') (by omega) (htop.trans (by decide))
end Compact50PriceTableTwo7b
