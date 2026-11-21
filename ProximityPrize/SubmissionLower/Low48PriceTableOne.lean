import ProximityPrize.SubmissionLower.Low48PriceTableEmpty

set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 4000000
namespace Low48PriceTableOne
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low48Price (fullCap physicalPrice)
open Low48PriceCaps (order allowance start allowance_mono)
open Low48PriceTableBase (point oldRectangle)

private theorem r1_0 {a : Shape} (h₁ : 1 ≤ a.b) (h₂ : 3 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 3)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 1) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 4 ≤ a.j)
    (h₃ : a.b ≤ 61) (h₄ : a.j ≤ 4)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 1) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_2 {a : Shape} (h₁ : 62 ≤ a.b) (h₂ : 4 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 4)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 2) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_3 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 5 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 5)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 4) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_4 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 8)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 11) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_5 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 13)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 20) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_6 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 14 ≤ a.j)
    (h₃ : a.b ≤ 62) (h₄ : a.j ≤ 24)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 22) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_7 {a : Shape} (h₁ : 63 ≤ a.b) (h₂ : 14 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 24)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 44) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_8 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 64) (h₄ : a.j ≤ 46)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 39) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_9 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 35)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 51) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_10 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46)
    (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 59) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact1 (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 3
  · apply r1_0 <;> omega
  by_cases hJ1 : a.j ≤ 4
  · by_cases hB0 : a.b ≤ 61
    · apply r1_1 <;> omega
    apply r1_2 <;> omega
  by_cases hJ2 : a.j ≤ 5
  · apply r1_3 <;> omega
  by_cases hJ3 : a.j ≤ 8
  · apply r1_4 <;> omega
  by_cases hJ4 : a.j ≤ 13
  · apply r1_5 <;> omega
  by_cases hJ5 : a.j ≤ 24
  · by_cases hB0 : a.b ≤ 62
    · apply r1_6 <;> omega
    apply r1_7 <;> omega
  by_cases hJ6 : a.j ≤ 35
  · by_cases hB0 : a.b ≤ 64
    · apply r1_8 <;> omega
    apply r1_9 <;> omega
  by_cases hB0 : a.b ≤ 64
  · apply r1_8 <;> omega
  apply r1_10 <;> omega

private theorem r2_0 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 8)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 11) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_1 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 11)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 14) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_2 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 12 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 16)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 24) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_3 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 17 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 26)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 44) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_4 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 27 ≤ a.j)
    (h₃ : a.b ≤ 64) (h₄ : a.j ≤ 46)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 40) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_5 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 27 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 36)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 52) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_6 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 92) (h₄ : a.j ≤ 46)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 44) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_7 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 41)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_8 {a : Shape} (h₁ : 93 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46)
    (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 53) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact2 (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 8
  · apply r2_0 <;> omega
  by_cases hJ1 : a.j ≤ 11
  · apply r2_1 <;> omega
  by_cases hJ2 : a.j ≤ 16
  · apply r2_2 <;> omega
  by_cases hJ3 : a.j ≤ 26
  · apply r2_3 <;> omega
  by_cases hJ4 : a.j ≤ 36
  · by_cases hB0 : a.b ≤ 64
    · apply r2_4 <;> omega
    apply r2_5 <;> omega
  by_cases hJ5 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 64
    · apply r2_4 <;> omega
    by_cases hB1 : a.b ≤ 92
    · apply r2_6 <;> omega
    apply r2_7 <;> omega
  by_cases hB0 : a.b ≤ 64
  · apply r2_4 <;> omega
  by_cases hB1 : a.b ≤ 92
  · apply r2_6 <;> omega
  apply r2_8 <;> omega

private theorem r3_0 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 13)
    (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 20) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_1 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 14 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 18)
    (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 26) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_2 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 19 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 27)
    (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 43) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_3 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 65) (h₄ : a.j ≤ 46)
    (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_4 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 37)
    (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 54) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_5 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 38 ≤ a.j)
    (h₃ : a.b ≤ 93) (h₄ : a.j ≤ 46)
    (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_6 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 38 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46)
    (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact3 (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 13
  · apply r3_0 <;> omega
  by_cases hJ1 : a.j ≤ 18
  · apply r3_1 <;> omega
  by_cases hJ2 : a.j ≤ 27
  · apply r3_2 <;> omega
  by_cases hJ3 : a.j ≤ 37
  · by_cases hB0 : a.b ≤ 65
    · apply r3_3 <;> omega
    apply r3_4 <;> omega
  by_cases hB0 : a.b ≤ 65
  · apply r3_3 <;> omega
  by_cases hB1 : a.b ≤ 93
  · apply r3_5 <;> omega
  apply r3_6 <;> omega

private theorem r4_0 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 12 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 20)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 38) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_1 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 21 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 29)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_2 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 30 ≤ a.j)
    (h₃ : a.b ≤ 65) (h₄ : a.j ≤ 46)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_3 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 30 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 38)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 55) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_4 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 93) (h₄ : a.j ≤ 46)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_5 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46)
    (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact4 (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 20
  · apply r4_0 <;> omega
  by_cases hJ1 : a.j ≤ 29
  · apply r4_1 <;> omega
  by_cases hJ2 : a.j ≤ 38
  · by_cases hB0 : a.b ≤ 65
    · apply r4_2 <;> omega
    apply r4_3 <;> omega
  by_cases hB0 : a.b ≤ 65
  · apply r4_2 <;> omega
  by_cases hB1 : a.b ≤ 93
  · apply r4_4 <;> omega
  apply r4_5 <;> omega

private theorem r5_0 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 15 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 22)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 37) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_1 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 23 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 30)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 45) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_2 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 65) (h₄ : a.j ≤ 46)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 42) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_3 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 38)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 54) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_4 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 93) (h₄ : a.j ≤ 46)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_5 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 42)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 52) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_6 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46)
    (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 56) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact5 (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 22
  · apply r5_0 <;> omega
  by_cases hJ1 : a.j ≤ 30
  · apply r5_1 <;> omega
  by_cases hJ2 : a.j ≤ 38
  · by_cases hB0 : a.b ≤ 65
    · apply r5_2 <;> omega
    apply r5_3 <;> omega
  by_cases hJ3 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 65
    · apply r5_2 <;> omega
    by_cases hB1 : a.b ≤ 93
    · apply r5_4 <;> omega
    apply r5_5 <;> omega
  by_cases hB0 : a.b ≤ 65
  · apply r5_2 <;> omega
  by_cases hB1 : a.b ≤ 93
  · apply r5_4 <;> omega
  apply r5_6 <;> omega

private theorem r6_0 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 18 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 25)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 40) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_1 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 26 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 32)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_2 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 65) (h₄ : a.j ≤ 46)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_3 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 39)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 54) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_4 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 93) (h₄ : a.j ≤ 46)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_5 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 43)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 54) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_6 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46)
    (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 56) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact6 (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 25
  · apply r6_0 <;> omega
  by_cases hJ1 : a.j ≤ 32
  · apply r6_1 <;> omega
  by_cases hJ2 : a.j ≤ 39
  · by_cases hB0 : a.b ≤ 65
    · apply r6_2 <;> omega
    apply r6_3 <;> omega
  by_cases hJ3 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 65
    · apply r6_2 <;> omega
    by_cases hB1 : a.b ≤ 93
    · apply r6_4 <;> omega
    apply r6_5 <;> omega
  by_cases hB0 : a.b ≤ 65
  · apply r6_2 <;> omega
  by_cases hB1 : a.b ≤ 93
  · apply r6_4 <;> omega
  apply r6_6 <;> omega

private theorem r7_0 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 21 ≤ a.j)
    (h₃ : a.b ≤ 63) (h₄ : a.j ≤ 33)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 33) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_1 {a : Shape} (h₁ : 64 ≤ a.b) (h₂ : 21 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 27)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 40) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_2 {a : Shape} (h₁ : 64 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 33)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 45) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_3 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 66) (h₄ : a.j ≤ 46)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_4 {a : Shape} (h₁ : 67 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 55) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_5 {a : Shape} (h₁ : 67 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46)
    (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact7 (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 27
  · by_cases hB0 : a.b ≤ 63
    · apply r7_0 <;> omega
    apply r7_1 <;> omega
  by_cases hJ1 : a.j ≤ 33
  · by_cases hB0 : a.b ≤ 63
    · apply r7_0 <;> omega
    apply r7_2 <;> omega
  by_cases hJ2 : a.j ≤ 40
  · by_cases hB0 : a.b ≤ 66
    · apply r7_3 <;> omega
    apply r7_4 <;> omega
  by_cases hB0 : a.b ≤ 66
  · apply r7_3 <;> omega
  apply r7_5 <;> omega

private theorem r8_0 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 24 ≤ a.j)
    (h₃ : a.b ≤ 64) (h₄ : a.j ≤ 35)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 33) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_1 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 24 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 29)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 41) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_2 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 30 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 35)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_3 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 66) (h₄ : a.j ≤ 46)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 40) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_4 {a : Shape} (h₁ : 67 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 41)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 55) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_5 {a : Shape} (h₁ : 67 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46)
    (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 59) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact8 (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 29
  · by_cases hB0 : a.b ≤ 64
    · apply r8_0 <;> omega
    apply r8_1 <;> omega
  by_cases hJ1 : a.j ≤ 35
  · by_cases hB0 : a.b ≤ 64
    · apply r8_0 <;> omega
    apply r8_2 <;> omega
  by_cases hJ2 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 66
    · apply r8_3 <;> omega
    apply r8_4 <;> omega
  by_cases hB0 : a.b ≤ 66
  · apply r8_3 <;> omega
  apply r8_5 <;> omega

private theorem r9_0 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 27 ≤ a.j)
    (h₃ : a.b ≤ 64) (h₄ : a.j ≤ 36)
    (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 31) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_1 {a : Shape} (h₁ : 65 ≤ a.b) (h₂ : 27 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 36)
    (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 56) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_2 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 66) (h₄ : a.j ≤ 46)
    (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 39) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_3 {a : Shape} (h₁ : 67 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 41)
    (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 54) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_4 {a : Shape} (h₁ : 67 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46)
    (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact9 (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 36
  · by_cases hB0 : a.b ≤ 64
    · apply r9_0 <;> omega
    apply r9_1 <;> omega
  by_cases hJ1 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 66
    · apply r9_2 <;> omega
    apply r9_3 <;> omega
  by_cases hB0 : a.b ≤ 66
  · apply r9_2 <;> omega
  apply r9_4 <;> omega

private theorem r10_0 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 30 ≤ a.j)
    (h₃ : a.b ≤ 65) (h₄ : a.j ≤ 46)
    (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_1 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 30 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 38)
    (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 57) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_2 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 93) (h₄ : a.j ≤ 46)
    (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 51) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_3 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 42)
    (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 54) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_4 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46)
    (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 59) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact10 (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 38
  · by_cases hB0 : a.b ≤ 65
    · apply r10_0 <;> omega
    apply r10_1 <;> omega
  by_cases hJ1 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 65
    · apply r10_0 <;> omega
    by_cases hB1 : a.b ≤ 93
    · apply r10_2 <;> omega
    apply r10_3 <;> omega
  by_cases hB0 : a.b ≤ 65
  · apply r10_0 <;> omega
  by_cases hB1 : a.b ≤ 93
  · apply r10_2 <;> omega
  apply r10_4 <;> omega

private theorem r11_0 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 65) (h₄ : a.j ≤ 46)
    (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 44) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_1 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 39)
    (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 54) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_2 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 93) (h₄ : a.j ≤ 46)
    (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 50) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_3 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 43)
    (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 55) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_4 {a : Shape} (h₁ : 94 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46)
    (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 57) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact11 (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 39
  · by_cases hB0 : a.b ≤ 65
    · apply r11_0 <;> omega
    apply r11_1 <;> omega
  by_cases hJ1 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 65
    · apply r11_0 <;> omega
    by_cases hB1 : a.b ≤ 93
    · apply r11_2 <;> omega
    apply r11_3 <;> omega
  by_cases hB0 : a.b ≤ 65
  · apply r11_0 <;> omega
  by_cases hB1 : a.b ≤ 93
  · apply r11_2 <;> omega
  apply r11_4 <;> omega

private theorem r12_0 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 66) (h₄ : a.j ≤ 46)
    (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 40) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_1 {a : Shape} (h₁ : 67 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 41)
    (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 55) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_2 {a : Shape} (h₁ : 67 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46)
    (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact12 (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 66
    · apply r12_0 <;> omega
    apply r12_1 <;> omega
  by_cases hB0 : a.b ≤ 66
  · apply r12_0 <;> omega
  apply r12_2 <;> omega

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one).plus a) (fullCap top)) :
    physicalPrice a (order .one a) ≤ allowance top .one a.j := by
  change 1+a.b ≤ 121 ∧ 3+a.j ≤ 49 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb, hj, ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 120 := by omega
  have hj' : a.j ≤ 46 := by omega
  have hpt : a.t ≤ 12 := by omega
  have casesTop : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 ∨ a.t = 12 := by omega
  rcases casesTop with ht1 | ht2 | ht3 | ht4 | ht5 | ht6 | ht7 | ht8 | ht9 | ht10 | ht11 | ht12
  · exact (exact1 a ha ht1 hb' hj').trans (allowance_mono .one (by omega) htop)
  · exact (exact2 a ha ht2 hb' hj').trans (allowance_mono .one (by omega) htop)
  · exact (exact3 a ha ht3 hb' hj').trans (allowance_mono .one (by omega) htop)
  · exact (exact4 a ha ht4 hb' hj').trans (allowance_mono .one (by omega) htop)
  · exact (exact5 a ha ht5 hb' hj').trans (allowance_mono .one (by omega) htop)
  · exact (exact6 a ha ht6 hb' hj').trans (allowance_mono .one (by omega) htop)
  · exact (exact7 a ha ht7 hb' hj').trans (allowance_mono .one (by omega) htop)
  · exact (exact8 a ha ht8 hb' hj').trans (allowance_mono .one (by omega) htop)
  · exact (exact9 a ha ht9 hb' hj').trans (allowance_mono .one (by omega) htop)
  · exact (exact10 a ha ht10 hb' hj').trans (allowance_mono .one (by omega) htop)
  · exact (exact11 a ha ht11 hb' hj').trans (allowance_mono .one (by omega) htop)
  · exact (exact12 a ha ht12 hb' hj').trans (allowance_mono .one (by omega) htop)
end Low48PriceTableOne
