import ProximityPrize.SubmissionLower.Low48PriceTableOne

set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 4000000
namespace Low48PriceTableTwo
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low48Price (fullCap physicalPrice)
open Low48PriceCaps (order allowance start allowance_mono)
open Low48PriceTableBase (point oldRectangle)

private theorem r1_0 {a : Shape} (h₁ : 1 ≤ a.b) (h₂ : 3 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 5)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 3 .two a.j :=
  oldRectangle (l := 10) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 8)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 3 .two a.j :=
  oldRectangle (l := 18) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_2 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 13)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 3 .two a.j :=
  oldRectangle (l := 35) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_3 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 14 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 23)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 3 .two a.j :=
  oldRectangle (l := 71) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_4 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 24 ≤ a.j)
    (h₃ : a.b ≤ 63) (h₄ : a.j ≤ 43)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 3 .two a.j :=
  oldRectangle (l := 63) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_5 {a : Shape} (h₁ : 64 ≤ a.b) (h₂ : 24 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 33)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 3 .two a.j :=
  oldRectangle (l := 83) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_6 {a : Shape} (h₁ : 64 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 91) (h₄ : a.j ≤ 43)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 3 .two a.j :=
  oldRectangle (l := 70) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_7 {a : Shape} (h₁ : 92 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 38)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 3 .two a.j :=
  oldRectangle (l := 76) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_8 {a : Shape} (h₁ : 92 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 43)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 3 .two a.j :=
  oldRectangle (l := 83) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact1 (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 3 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 5
  · apply r1_0 <;> omega
  by_cases hJ1 : a.j ≤ 8
  · apply r1_1 <;> omega
  by_cases hJ2 : a.j ≤ 13
  · apply r1_2 <;> omega
  by_cases hJ3 : a.j ≤ 23
  · apply r1_3 <;> omega
  by_cases hJ4 : a.j ≤ 33
  · by_cases hB0 : a.b ≤ 63
    · apply r1_4 <;> omega
    apply r1_5 <;> omega
  by_cases hJ5 : a.j ≤ 38
  · by_cases hB0 : a.b ≤ 63
    · apply r1_4 <;> omega
    by_cases hB1 : a.b ≤ 91
    · apply r1_6 <;> omega
    apply r1_7 <;> omega
  by_cases hB0 : a.b ≤ 63
  · apply r1_4 <;> omega
  by_cases hB1 : a.b ≤ 91
  · apply r1_6 <;> omega
  apply r1_8 <;> omega

private theorem r2_0 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 10)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 4 .two a.j :=
  oldRectangle (l := 30) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_1 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 11 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 15)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 4 .two a.j :=
  oldRectangle (l := 39) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_2 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 16 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 24)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 4 .two a.j :=
  oldRectangle (l := 69) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_3 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 64) (h₄ : a.j ≤ 43)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 4 .two a.j :=
  oldRectangle (l := 67) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_4 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 29)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 4 .two a.j :=
  oldRectangle (l := 64) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_5 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 30 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 34)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 4 .two a.j :=
  oldRectangle (l := 72) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_6 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 35 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 43)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 4 .two a.j :=
  oldRectangle (l := 73) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_7 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 35 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 39)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 4 .two a.j :=
  oldRectangle (l := 80) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_8 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 43)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 4 .two a.j :=
  oldRectangle (l := 84) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact2 (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 4 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 10
  · apply r2_0 <;> omega
  by_cases hJ1 : a.j ≤ 15
  · apply r2_1 <;> omega
  by_cases hJ2 : a.j ≤ 24
  · apply r2_2 <;> omega
  by_cases hJ3 : a.j ≤ 29
  · by_cases hB0 : a.b ≤ 64
    · apply r2_3 <;> omega
    apply r2_4 <;> omega
  by_cases hJ4 : a.j ≤ 34
  · by_cases hB0 : a.b ≤ 64
    · apply r2_3 <;> omega
    apply r2_5 <;> omega
  by_cases hJ5 : a.j ≤ 39
  · by_cases hB0 : a.b ≤ 64
    · apply r2_3 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r2_6 <;> omega
    apply r2_7 <;> omega
  by_cases hB0 : a.b ≤ 64
  · apply r2_3 <;> omega
  by_cases hB1 : a.b ≤ 92
  · apply r2_6 <;> omega
  apply r2_8 <;> omega

private theorem r3_0 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 17)
    (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 5 .two a.j :=
  oldRectangle (l := 62) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_1 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 18 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 26)
    (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 5 .two a.j :=
  oldRectangle (l := 73) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_2 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 27 ≤ a.j)
    (h₃ : a.b ≤ 64) (h₄ : a.j ≤ 43)
    (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 5 .two a.j :=
  oldRectangle (l := 66) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_3 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 27 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 31)
    (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 5 .two a.j :=
  oldRectangle (l := 69) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_4 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 32 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 35)
    (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 5 .two a.j :=
  oldRectangle (l := 73) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_5 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 43)
    (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 5 .two a.j :=
  oldRectangle (l := 74) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_6 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 39)
    (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 5 .two a.j :=
  oldRectangle (l := 80) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_7 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 43)
    (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 5 .two a.j :=
  oldRectangle (l := 87) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact3 (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 5 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 17
  · apply r3_0 <;> omega
  by_cases hJ1 : a.j ≤ 26
  · apply r3_1 <;> omega
  by_cases hJ2 : a.j ≤ 31
  · by_cases hB0 : a.b ≤ 64
    · apply r3_2 <;> omega
    apply r3_3 <;> omega
  by_cases hJ3 : a.j ≤ 35
  · by_cases hB0 : a.b ≤ 64
    · apply r3_2 <;> omega
    apply r3_4 <;> omega
  by_cases hJ4 : a.j ≤ 39
  · by_cases hB0 : a.b ≤ 64
    · apply r3_2 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r3_5 <;> omega
    apply r3_6 <;> omega
  by_cases hB0 : a.b ≤ 64
  · apply r3_2 <;> omega
  by_cases hB1 : a.b ≤ 92
  · apply r3_5 <;> omega
  apply r3_7 <;> omega

private theorem r4_0 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 12 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 19)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 6 .two a.j :=
  oldRectangle (l := 58) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_1 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 20 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 27)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 6 .two a.j :=
  oldRectangle (l := 72) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_2 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 64) (h₄ : a.j ≤ 43)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 6 .two a.j :=
  oldRectangle (l := 67) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_3 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 31)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 6 .two a.j :=
  oldRectangle (l := 67) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_4 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 32 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 35)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 6 .two a.j :=
  oldRectangle (l := 75) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_5 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 43)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 6 .two a.j :=
  oldRectangle (l := 76) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_6 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 39)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 6 .two a.j :=
  oldRectangle (l := 82) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_7 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 106) (h₄ : a.j ≤ 43)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 6 .two a.j :=
  oldRectangle (l := 79) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_8 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 41)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 6 .two a.j :=
  oldRectangle (l := 81) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_9 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 43)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 6 .two a.j :=
  oldRectangle (l := 85) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact4 (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 6 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 19
  · apply r4_0 <;> omega
  by_cases hJ1 : a.j ≤ 27
  · apply r4_1 <;> omega
  by_cases hJ2 : a.j ≤ 31
  · by_cases hB0 : a.b ≤ 64
    · apply r4_2 <;> omega
    apply r4_3 <;> omega
  by_cases hJ3 : a.j ≤ 35
  · by_cases hB0 : a.b ≤ 64
    · apply r4_2 <;> omega
    apply r4_4 <;> omega
  by_cases hJ4 : a.j ≤ 39
  · by_cases hB0 : a.b ≤ 64
    · apply r4_2 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r4_5 <;> omega
    apply r4_6 <;> omega
  by_cases hJ5 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 64
    · apply r4_2 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r4_5 <;> omega
    by_cases hB2 : a.b ≤ 106
    · apply r4_7 <;> omega
    apply r4_8 <;> omega
  by_cases hB0 : a.b ≤ 64
  · apply r4_2 <;> omega
  by_cases hB1 : a.b ≤ 92
  · apply r4_5 <;> omega
  by_cases hB2 : a.b ≤ 106
  · apply r4_7 <;> omega
  apply r4_9 <;> omega

private theorem r5_0 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 15 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 22)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 7 .two a.j :=
  oldRectangle (l := 63) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_1 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 23 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 29)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 7 .two a.j :=
  oldRectangle (l := 72) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_2 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 30 ≤ a.j)
    (h₃ : a.b ≤ 64) (h₄ : a.j ≤ 43)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 7 .two a.j :=
  oldRectangle (l := 65) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_3 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 30 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 36)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 7 .two a.j :=
  oldRectangle (l := 85) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_4 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 43)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 7 .two a.j :=
  oldRectangle (l := 76) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_5 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 40)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 7 .two a.j :=
  oldRectangle (l := 85) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_6 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 106) (h₄ : a.j ≤ 43)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 7 .two a.j :=
  oldRectangle (l := 79) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_7 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 42)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 7 .two a.j :=
  oldRectangle (l := 84) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_8 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 43)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 7 .two a.j :=
  oldRectangle (l := 84) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact5 (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 7 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 22
  · apply r5_0 <;> omega
  by_cases hJ1 : a.j ≤ 29
  · apply r5_1 <;> omega
  by_cases hJ2 : a.j ≤ 36
  · by_cases hB0 : a.b ≤ 64
    · apply r5_2 <;> omega
    apply r5_3 <;> omega
  by_cases hJ3 : a.j ≤ 40
  · by_cases hB0 : a.b ≤ 64
    · apply r5_2 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r5_4 <;> omega
    apply r5_5 <;> omega
  by_cases hJ4 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 64
    · apply r5_2 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r5_4 <;> omega
    by_cases hB2 : a.b ≤ 106
    · apply r5_6 <;> omega
    apply r5_7 <;> omega
  by_cases hB0 : a.b ≤ 64
  · apply r5_2 <;> omega
  by_cases hB1 : a.b ≤ 92
  · apply r5_4 <;> omega
  by_cases hB2 : a.b ≤ 106
  · apply r5_6 <;> omega
  apply r5_8 <;> omega

private theorem r6_0 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 18 ≤ a.j)
    (h₃ : a.b ≤ 62) (h₄ : a.j ≤ 30)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 8 .two a.j :=
  oldRectangle (l := 53) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_1 {a : Shape} (h₁ : 63 ≤ a.b) (h₂ : 18 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 24)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 8 .two a.j :=
  oldRectangle (l := 63) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_2 {a : Shape} (h₁ : 63 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 30)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 8 .two a.j :=
  oldRectangle (l := 71) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_3 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 65) (h₄ : a.j ≤ 43)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 8 .two a.j :=
  oldRectangle (l := 66) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_4 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 37)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 8 .two a.j :=
  oldRectangle (l := 68) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_5 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 34)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 8 .two a.j :=
  oldRectangle (l := 74) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_6 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 35 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 37)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 8 .two a.j :=
  oldRectangle (l := 78) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_7 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 38 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 43)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 8 .two a.j :=
  oldRectangle (l := 75) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_8 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 38 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 40)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 8 .two a.j :=
  oldRectangle (l := 84) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_9 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 106) (h₄ : a.j ≤ 43)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 8 .two a.j :=
  oldRectangle (l := 80) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_10 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 42)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 8 .two a.j :=
  oldRectangle (l := 85) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_11 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 43)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 8 .two a.j :=
  oldRectangle (l := 85) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact6 (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 8 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 24
  · by_cases hB0 : a.b ≤ 62
    · apply r6_0 <;> omega
    apply r6_1 <;> omega
  by_cases hJ1 : a.j ≤ 30
  · by_cases hB0 : a.b ≤ 62
    · apply r6_0 <;> omega
    apply r6_2 <;> omega
  by_cases hJ2 : a.j ≤ 34
  · by_cases hB0 : a.b ≤ 65
    · apply r6_3 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r6_4 <;> omega
    apply r6_5 <;> omega
  by_cases hJ3 : a.j ≤ 37
  · by_cases hB0 : a.b ≤ 65
    · apply r6_3 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r6_4 <;> omega
    apply r6_6 <;> omega
  by_cases hJ4 : a.j ≤ 40
  · by_cases hB0 : a.b ≤ 65
    · apply r6_3 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r6_7 <;> omega
    apply r6_8 <;> omega
  by_cases hJ5 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 65
    · apply r6_3 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r6_7 <;> omega
    by_cases hB2 : a.b ≤ 106
    · apply r6_9 <;> omega
    apply r6_10 <;> omega
  by_cases hB0 : a.b ≤ 65
  · apply r6_3 <;> omega
  by_cases hB1 : a.b ≤ 92
  · apply r6_7 <;> omega
  by_cases hB2 : a.b ≤ 106
  · apply r6_9 <;> omega
  apply r6_11 <;> omega

private theorem r7_0 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 21 ≤ a.j)
    (h₃ : a.b ≤ 63) (h₄ : a.j ≤ 32)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 9 .two a.j :=
  oldRectangle (l := 53) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_1 {a : Shape} (h₁ : 64 ≤ a.b) (h₂ : 21 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 26)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 9 .two a.j :=
  oldRectangle (l := 63) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_2 {a : Shape} (h₁ : 64 ≤ a.b) (h₂ : 27 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 32)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 9 .two a.j :=
  oldRectangle (l := 75) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_3 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 65) (h₄ : a.j ≤ 43)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 9 .two a.j :=
  oldRectangle (l := 63) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_4 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 38)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 9 .two a.j :=
  oldRectangle (l := 68) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_5 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 35)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 9 .two a.j :=
  oldRectangle (l := 74) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_6 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 38)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 9 .two a.j :=
  oldRectangle (l := 80) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_7 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 43)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 9 .two a.j :=
  oldRectangle (l := 74) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_8 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 41)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 9 .two a.j :=
  oldRectangle (l := 86) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_9 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 106) (h₄ : a.j ≤ 43)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 9 .two a.j :=
  oldRectangle (l := 78) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_10 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 43)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 9 .two a.j :=
  oldRectangle (l := 83) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_11 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 42)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 9 .two a.j :=
  oldRectangle (l := 84) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_12 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 43)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 9 .two a.j :=
  oldRectangle (l := 86) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact7 (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 9 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 26
  · by_cases hB0 : a.b ≤ 63
    · apply r7_0 <;> omega
    apply r7_1 <;> omega
  by_cases hJ1 : a.j ≤ 32
  · by_cases hB0 : a.b ≤ 63
    · apply r7_0 <;> omega
    apply r7_2 <;> omega
  by_cases hJ2 : a.j ≤ 35
  · by_cases hB0 : a.b ≤ 65
    · apply r7_3 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r7_4 <;> omega
    apply r7_5 <;> omega
  by_cases hJ3 : a.j ≤ 38
  · by_cases hB0 : a.b ≤ 65
    · apply r7_3 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r7_4 <;> omega
    apply r7_6 <;> omega
  by_cases hJ4 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 65
    · apply r7_3 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r7_7 <;> omega
    apply r7_8 <;> omega
  by_cases hJ5 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 65
    · apply r7_3 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r7_7 <;> omega
    by_cases hB2 : a.b ≤ 106
    · apply r7_9 <;> omega
    by_cases hB3 : a.b ≤ 113
    · apply r7_10 <;> omega
    apply r7_11 <;> omega
  by_cases hB0 : a.b ≤ 65
  · apply r7_3 <;> omega
  by_cases hB1 : a.b ≤ 92
  · apply r7_7 <;> omega
  by_cases hB2 : a.b ≤ 106
  · apply r7_9 <;> omega
  by_cases hB3 : a.b ≤ 113
  · apply r7_10 <;> omega
  apply r7_12 <;> omega

private theorem r8_0 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 24 ≤ a.j)
    (h₃ : a.b ≤ 63) (h₄ : a.j ≤ 33)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 10 .two a.j :=
  oldRectangle (l := 49) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_1 {a : Shape} (h₁ : 64 ≤ a.b) (h₂ : 24 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 28)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 10 .two a.j :=
  oldRectangle (l := 64) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_2 {a : Shape} (h₁ : 64 ≤ a.b) (h₂ : 29 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 33)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 10 .two a.j :=
  oldRectangle (l := 74) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_3 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 65) (h₄ : a.j ≤ 43)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 10 .two a.j :=
  oldRectangle (l := 62) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_4 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 38)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 10 .two a.j :=
  oldRectangle (l := 85) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_5 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 43)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 10 .two a.j :=
  oldRectangle (l := 74) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_6 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 41)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 10 .two a.j :=
  oldRectangle (l := 86) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_7 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 106) (h₄ : a.j ≤ 43)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 10 .two a.j :=
  oldRectangle (l := 79) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_8 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 43)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 10 .two a.j :=
  oldRectangle (l := 84) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_9 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 42)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 10 .two a.j :=
  oldRectangle (l := 84) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_10 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 43)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 10 .two a.j :=
  oldRectangle (l := 86) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact8 (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 10 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 28
  · by_cases hB0 : a.b ≤ 63
    · apply r8_0 <;> omega
    apply r8_1 <;> omega
  by_cases hJ1 : a.j ≤ 33
  · by_cases hB0 : a.b ≤ 63
    · apply r8_0 <;> omega
    apply r8_2 <;> omega
  by_cases hJ2 : a.j ≤ 38
  · by_cases hB0 : a.b ≤ 65
    · apply r8_3 <;> omega
    apply r8_4 <;> omega
  by_cases hJ3 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 65
    · apply r8_3 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r8_5 <;> omega
    apply r8_6 <;> omega
  by_cases hJ4 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 65
    · apply r8_3 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r8_5 <;> omega
    by_cases hB2 : a.b ≤ 106
    · apply r8_7 <;> omega
    by_cases hB3 : a.b ≤ 113
    · apply r8_8 <;> omega
    apply r8_9 <;> omega
  by_cases hB0 : a.b ≤ 65
  · apply r8_3 <;> omega
  by_cases hB1 : a.b ≤ 92
  · apply r8_5 <;> omega
  by_cases hB2 : a.b ≤ 106
  · apply r8_7 <;> omega
  by_cases hB3 : a.b ≤ 113
  · apply r8_8 <;> omega
  apply r8_10 <;> omega

private theorem r9_0 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 27 ≤ a.j)
    (h₃ : a.b ≤ 64) (h₄ : a.j ≤ 43)
    (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 11 .two a.j :=
  oldRectangle (l := 77) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_1 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 27 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 31)
    (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 11 .two a.j :=
  oldRectangle (l := 70) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_2 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 32 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 35)
    (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 11 .two a.j :=
  oldRectangle (l := 76) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_3 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 43)
    (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 11 .two a.j :=
  oldRectangle (l := 81) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_4 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 39)
    (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 11 .two a.j :=
  oldRectangle (l := 84) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_5 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 41)
    (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 11 .two a.j :=
  oldRectangle (l := 84) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_6 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 106) (h₄ : a.j ≤ 43)
    (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 11 .two a.j :=
  oldRectangle (l := 79) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_7 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 43)
    (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 11 .two a.j :=
  oldRectangle (l := 84) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_8 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 42)
    (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 11 .two a.j :=
  oldRectangle (l := 84) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_9 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 43)
    (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 11 .two a.j :=
  oldRectangle (l := 86) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact9 (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 11 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 31
  · by_cases hB0 : a.b ≤ 64
    · apply r9_0 <;> omega
    apply r9_1 <;> omega
  by_cases hJ1 : a.j ≤ 35
  · by_cases hB0 : a.b ≤ 64
    · apply r9_0 <;> omega
    apply r9_2 <;> omega
  by_cases hJ2 : a.j ≤ 39
  · by_cases hB0 : a.b ≤ 64
    · apply r9_0 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r9_3 <;> omega
    apply r9_4 <;> omega
  by_cases hJ3 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 64
    · apply r9_0 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r9_3 <;> omega
    apply r9_5 <;> omega
  by_cases hJ4 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 64
    · apply r9_0 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r9_3 <;> omega
    by_cases hB2 : a.b ≤ 106
    · apply r9_6 <;> omega
    by_cases hB3 : a.b ≤ 113
    · apply r9_7 <;> omega
    apply r9_8 <;> omega
  by_cases hB0 : a.b ≤ 64
  · apply r9_0 <;> omega
  by_cases hB1 : a.b ≤ 92
  · apply r9_3 <;> omega
  by_cases hB2 : a.b ≤ 106
  · apply r9_6 <;> omega
  by_cases hB3 : a.b ≤ 113
  · apply r9_7 <;> omega
  apply r9_9 <;> omega

private theorem r10_0 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 30 ≤ a.j)
    (h₃ : a.b ≤ 64) (h₄ : a.j ≤ 43)
    (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 12 .two a.j :=
  oldRectangle (l := 70) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_1 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 30 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 36)
    (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 12 .two a.j :=
  oldRectangle (l := 67) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_2 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 30 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 33)
    (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 12 .two a.j :=
  oldRectangle (l := 71) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_3 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 36)
    (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 12 .two a.j :=
  oldRectangle (l := 75) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_4 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 43)
    (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 12 .two a.j :=
  oldRectangle (l := 79) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_5 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 40)
    (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 12 .two a.j :=
  oldRectangle (l := 86) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_6 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 106) (h₄ : a.j ≤ 43)
    (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 12 .two a.j :=
  oldRectangle (l := 81) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_7 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 42)
    (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 12 .two a.j :=
  oldRectangle (l := 86) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_8 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 43)
    (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 12 .two a.j :=
  oldRectangle (l := 86) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact10 (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 12 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 33
  · by_cases hB0 : a.b ≤ 64
    · apply r10_0 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r10_1 <;> omega
    apply r10_2 <;> omega
  by_cases hJ1 : a.j ≤ 36
  · by_cases hB0 : a.b ≤ 64
    · apply r10_0 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r10_1 <;> omega
    apply r10_3 <;> omega
  by_cases hJ2 : a.j ≤ 40
  · by_cases hB0 : a.b ≤ 64
    · apply r10_0 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r10_4 <;> omega
    apply r10_5 <;> omega
  by_cases hJ3 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 64
    · apply r10_0 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r10_4 <;> omega
    by_cases hB2 : a.b ≤ 106
    · apply r10_6 <;> omega
    apply r10_7 <;> omega
  by_cases hB0 : a.b ≤ 64
  · apply r10_0 <;> omega
  by_cases hB1 : a.b ≤ 92
  · apply r10_4 <;> omega
  by_cases hB2 : a.b ≤ 106
  · apply r10_6 <;> omega
  apply r10_8 <;> omega

private theorem r11_0 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 65) (h₄ : a.j ≤ 43)
    (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 13 .two a.j :=
  oldRectangle (l := 64) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_1 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 38)
    (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 13 .two a.j :=
  oldRectangle (l := 68) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_2 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 35)
    (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 13 .two a.j :=
  oldRectangle (l := 73) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_3 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 38)
    (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 13 .two a.j :=
  oldRectangle (l := 79) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_4 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 43)
    (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 13 .two a.j :=
  oldRectangle (l := 74) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_5 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 41)
    (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 13 .two a.j :=
  oldRectangle (l := 86) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_6 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 106) (h₄ : a.j ≤ 43)
    (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 13 .two a.j :=
  oldRectangle (l := 79) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_7 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 42)
    (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 13 .two a.j :=
  oldRectangle (l := 84) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_8 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 43)
    (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .two a) ≤ allowance 13 .two a.j :=
  oldRectangle (l := 86) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact11 (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 119) (hj : a.j ≤ 43) :
    physicalPrice a (order .two a) ≤ allowance 13 .two a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 35
  · by_cases hB0 : a.b ≤ 65
    · apply r11_0 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r11_1 <;> omega
    apply r11_2 <;> omega
  by_cases hJ1 : a.j ≤ 38
  · by_cases hB0 : a.b ≤ 65
    · apply r11_0 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r11_1 <;> omega
    apply r11_3 <;> omega
  by_cases hJ2 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 65
    · apply r11_0 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r11_4 <;> omega
    apply r11_5 <;> omega
  by_cases hJ3 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 65
    · apply r11_0 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r11_4 <;> omega
    by_cases hB2 : a.b ≤ 106
    · apply r11_6 <;> omega
    apply r11_7 <;> omega
  by_cases hB0 : a.b ≤ 65
  · apply r11_0 <;> omega
  by_cases hB1 : a.b ≤ 92
  · apply r11_4 <;> omega
  by_cases hB2 : a.b ≤ 106
  · apply r11_6 <;> omega
  apply r11_8 <;> omega

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .two).plus a) (fullCap top)) :
    physicalPrice a (order .two a) ≤ allowance top .two a.j := by
  change 2+a.b ≤ 121 ∧ 6+a.j ≤ 49 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb, hj, ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 119 := by omega
  have hj' : a.j ≤ 43 := by omega
  have hpt : a.t ≤ 11 := by omega
  have casesTop : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 := by omega
  rcases casesTop with ht1 | ht2 | ht3 | ht4 | ht5 | ht6 | ht7 | ht8 | ht9 | ht10 | ht11
  · exact (exact1 a ha ht1 hb' hj').trans (allowance_mono .two (by omega) htop)
  · exact (exact2 a ha ht2 hb' hj').trans (allowance_mono .two (by omega) htop)
  · exact (exact3 a ha ht3 hb' hj').trans (allowance_mono .two (by omega) htop)
  · exact (exact4 a ha ht4 hb' hj').trans (allowance_mono .two (by omega) htop)
  · exact (exact5 a ha ht5 hb' hj').trans (allowance_mono .two (by omega) htop)
  · exact (exact6 a ha ht6 hb' hj').trans (allowance_mono .two (by omega) htop)
  · exact (exact7 a ha ht7 hb' hj').trans (allowance_mono .two (by omega) htop)
  · exact (exact8 a ha ht8 hb' hj').trans (allowance_mono .two (by omega) htop)
  · exact (exact9 a ha ht9 hb' hj').trans (allowance_mono .two (by omega) htop)
  · exact (exact10 a ha ht10 hb' hj').trans (allowance_mono .two (by omega) htop)
  · exact (exact11 a ha ht11 hb' hj').trans (allowance_mono .two (by omega) htop)
end Low48PriceTableTwo
