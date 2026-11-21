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
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 3) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 1) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_1 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 4 ≤ a.j)
    (h₃ : a.b ≤ 65) (h₄ : a.j ≤ 4) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 1) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_2 {a : Shape} (h₁ : 66 ≤ a.b) (h₂ : 4 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 4) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 2) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_3 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 5 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 5) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 4) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_4 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 6) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 11) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_5 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 7 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 8) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 11) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_6 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 9) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 20) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_7 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 10 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 12) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 20) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_8 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 13 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 15) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 38) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_9 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 16 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 18) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 38) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_10 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 19 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 21) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 44) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_11 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 22 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 24) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_12 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 27) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_13 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 30) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_14 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 33) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_15 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 36) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_16 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 39) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_17 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 42) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_18 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r1_19 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 1) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact1 (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 2 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 3
  · apply r1_0 <;> omega
  by_cases hJ1 : a.j ≤ 4
  · by_cases hB0 : a.b ≤ 65
    · apply r1_1 <;> omega
    apply r1_2 <;> omega
  by_cases hJ2 : a.j ≤ 5
  · apply r1_3 <;> omega
  by_cases hJ3 : a.j ≤ 6
  · apply r1_4 <;> omega
  by_cases hJ4 : a.j ≤ 8
  · apply r1_5 <;> omega
  by_cases hJ5 : a.j ≤ 9
  · apply r1_6 <;> omega
  by_cases hJ6 : a.j ≤ 12
  · apply r1_7 <;> omega
  by_cases hJ7 : a.j ≤ 15
  · apply r1_8 <;> omega
  by_cases hJ8 : a.j ≤ 18
  · apply r1_9 <;> omega
  by_cases hJ9 : a.j ≤ 21
  · apply r1_10 <;> omega
  by_cases hJ10 : a.j ≤ 24
  · apply r1_11 <;> omega
  by_cases hJ11 : a.j ≤ 27
  · apply r1_12 <;> omega
  by_cases hJ12 : a.j ≤ 30
  · apply r1_13 <;> omega
  by_cases hJ13 : a.j ≤ 33
  · apply r1_14 <;> omega
  by_cases hJ14 : a.j ≤ 36
  · apply r1_15 <;> omega
  by_cases hJ15 : a.j ≤ 39
  · apply r1_16 <;> omega
  by_cases hJ16 : a.j ≤ 42
  · apply r1_17 <;> omega
  by_cases hJ17 : a.j ≤ 45
  · apply r1_18 <;> omega
  apply r1_19 <;> omega

private theorem r2_0 {a : Shape} (h₁ : 2 ≤ a.b) (h₂ : 6 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 6) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 11) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_1 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 7 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 8) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 11) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_2 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 9) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 20) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_3 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 10 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 12) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 20) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_4 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 13 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 15) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 38) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_5 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 16 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 18) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 38) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_6 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 19 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 21) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 44) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_7 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 22 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 24) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_8 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 27) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_9 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 30) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_10 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 33) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_11 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 36) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_12 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 39) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_13 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 42) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_14 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 44) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_15 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r2_16 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 2) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact2 (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 3 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 6
  · apply r2_0 <;> omega
  by_cases hJ1 : a.j ≤ 8
  · apply r2_1 <;> omega
  by_cases hJ2 : a.j ≤ 9
  · apply r2_2 <;> omega
  by_cases hJ3 : a.j ≤ 12
  · apply r2_3 <;> omega
  by_cases hJ4 : a.j ≤ 15
  · apply r2_4 <;> omega
  by_cases hJ5 : a.j ≤ 18
  · apply r2_5 <;> omega
  by_cases hJ6 : a.j ≤ 21
  · apply r2_6 <;> omega
  by_cases hJ7 : a.j ≤ 24
  · apply r2_7 <;> omega
  by_cases hJ8 : a.j ≤ 27
  · apply r2_8 <;> omega
  by_cases hJ9 : a.j ≤ 30
  · apply r2_9 <;> omega
  by_cases hJ10 : a.j ≤ 33
  · apply r2_10 <;> omega
  by_cases hJ11 : a.j ≤ 36
  · apply r2_11 <;> omega
  by_cases hJ12 : a.j ≤ 39
  · apply r2_12 <;> omega
  by_cases hJ13 : a.j ≤ 42
  · apply r2_13 <;> omega
  by_cases hJ14 : a.j ≤ 44
  · apply r2_14 <;> omega
  by_cases hJ15 : a.j ≤ 45
  · apply r2_15 <;> omega
  apply r2_16 <;> omega

private theorem r3_0 {a : Shape} (h₁ : 3 ≤ a.b) (h₂ : 9 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 9) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 20) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_1 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 10 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 12) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 20) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_2 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 13 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 15) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 38) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_3 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 16 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 18) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 38) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_4 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 19 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 21) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 44) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_5 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 22 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 24) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_6 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 27) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_7 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 30) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_8 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 33) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_9 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 36) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_10 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 39) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_11 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 42) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_12 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 43) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_13 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 44) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_14 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 45) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_15 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_16 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 46) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r3_17 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 3) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact3 (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 4 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 9
  · apply r3_0 <;> omega
  by_cases hJ1 : a.j ≤ 12
  · apply r3_1 <;> omega
  by_cases hJ2 : a.j ≤ 15
  · apply r3_2 <;> omega
  by_cases hJ3 : a.j ≤ 18
  · apply r3_3 <;> omega
  by_cases hJ4 : a.j ≤ 21
  · apply r3_4 <;> omega
  by_cases hJ5 : a.j ≤ 24
  · apply r3_5 <;> omega
  by_cases hJ6 : a.j ≤ 27
  · apply r3_6 <;> omega
  by_cases hJ7 : a.j ≤ 30
  · apply r3_7 <;> omega
  by_cases hJ8 : a.j ≤ 33
  · apply r3_8 <;> omega
  by_cases hJ9 : a.j ≤ 36
  · apply r3_9 <;> omega
  by_cases hJ10 : a.j ≤ 39
  · apply r3_10 <;> omega
  by_cases hJ11 : a.j ≤ 42
  · apply r3_11 <;> omega
  by_cases hJ12 : a.j ≤ 43
  · apply r3_12 <;> omega
  by_cases hJ13 : a.j ≤ 44
  · apply r3_13 <;> omega
  by_cases hJ14 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 118
    · apply r3_14 <;> omega
    apply r3_15 <;> omega
  by_cases hB0 : a.b ≤ 116
  · apply r3_16 <;> omega
  apply r3_17 <;> omega

private theorem r4_0 {a : Shape} (h₁ : 4 ≤ a.b) (h₂ : 12 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 12) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 38) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_1 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 13 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 15) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 38) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_2 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 16 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 18) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 38) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_3 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 19 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 21) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 44) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_4 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 22 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 24) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_5 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 27) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_6 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 30) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_7 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 33) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_8 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 36) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_9 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 39) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_10 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 41) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_11 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 42) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_12 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 43) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_13 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 44) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_14 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 44) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_15 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 45) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_16 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_17 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 46) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r4_18 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 4) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact4 (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 5 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 12
  · apply r4_0 <;> omega
  by_cases hJ1 : a.j ≤ 15
  · apply r4_1 <;> omega
  by_cases hJ2 : a.j ≤ 18
  · apply r4_2 <;> omega
  by_cases hJ3 : a.j ≤ 21
  · apply r4_3 <;> omega
  by_cases hJ4 : a.j ≤ 24
  · apply r4_4 <;> omega
  by_cases hJ5 : a.j ≤ 27
  · apply r4_5 <;> omega
  by_cases hJ6 : a.j ≤ 30
  · apply r4_6 <;> omega
  by_cases hJ7 : a.j ≤ 33
  · apply r4_7 <;> omega
  by_cases hJ8 : a.j ≤ 36
  · apply r4_8 <;> omega
  by_cases hJ9 : a.j ≤ 39
  · apply r4_9 <;> omega
  by_cases hJ10 : a.j ≤ 41
  · apply r4_10 <;> omega
  by_cases hJ11 : a.j ≤ 42
  · apply r4_11 <;> omega
  by_cases hJ12 : a.j ≤ 43
  · apply r4_12 <;> omega
  by_cases hJ13 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 117
    · apply r4_13 <;> omega
    apply r4_14 <;> omega
  by_cases hJ14 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 115
    · apply r4_15 <;> omega
    apply r4_16 <;> omega
  by_cases hB0 : a.b ≤ 113
  · apply r4_17 <;> omega
  apply r4_18 <;> omega

private theorem r5_0 {a : Shape} (h₁ : 5 ≤ a.b) (h₂ : 15 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 15) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 38) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_1 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 16 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 18) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 38) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_2 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 19 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 21) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 44) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_3 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 22 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 24) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_4 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 27) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_5 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 30) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_6 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 33) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_7 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 36) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_8 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 39) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_9 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 41) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_10 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 42) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_11 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 43) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_12 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 43) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_13 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 115) (h₄ : a.j ≤ 44) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_14 {a : Shape} (h₁ : 116 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 44) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_15 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 45) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_16 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_17 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 110) (h₄ : a.j ≤ 46) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r5_18 {a : Shape} (h₁ : 111 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 5) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact5 (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 6 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 15
  · apply r5_0 <;> omega
  by_cases hJ1 : a.j ≤ 18
  · apply r5_1 <;> omega
  by_cases hJ2 : a.j ≤ 21
  · apply r5_2 <;> omega
  by_cases hJ3 : a.j ≤ 24
  · apply r5_3 <;> omega
  by_cases hJ4 : a.j ≤ 27
  · apply r5_4 <;> omega
  by_cases hJ5 : a.j ≤ 30
  · apply r5_5 <;> omega
  by_cases hJ6 : a.j ≤ 33
  · apply r5_6 <;> omega
  by_cases hJ7 : a.j ≤ 36
  · apply r5_7 <;> omega
  by_cases hJ8 : a.j ≤ 39
  · apply r5_8 <;> omega
  by_cases hJ9 : a.j ≤ 41
  · apply r5_9 <;> omega
  by_cases hJ10 : a.j ≤ 42
  · apply r5_10 <;> omega
  by_cases hJ11 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 118
    · apply r5_11 <;> omega
    apply r5_12 <;> omega
  by_cases hJ12 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 115
    · apply r5_13 <;> omega
    apply r5_14 <;> omega
  by_cases hJ13 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 113
    · apply r5_15 <;> omega
    apply r5_16 <;> omega
  by_cases hB0 : a.b ≤ 110
  · apply r5_17 <;> omega
  apply r5_18 <;> omega

private theorem r6_0 {a : Shape} (h₁ : 6 ≤ a.b) (h₂ : 18 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 18) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 44) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_1 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 19 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 21) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 44) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_2 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 22 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 24) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_3 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 27) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_4 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 30) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_5 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 33) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_6 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 36) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_7 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 39) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_8 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_9 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 41) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_10 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 118) (h₄ : a.j ≤ 42) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_11 {a : Shape} (h₁ : 119 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 42) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_12 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 43) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_13 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 43) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_14 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 44) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_15 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 44) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_16 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 111) (h₄ : a.j ≤ 45) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_17 {a : Shape} (h₁ : 112 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_18 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 108) (h₄ : a.j ≤ 46) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r6_19 {a : Shape} (h₁ : 109 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 6) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact6 (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 7 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 18
  · apply r6_0 <;> omega
  by_cases hJ1 : a.j ≤ 21
  · apply r6_1 <;> omega
  by_cases hJ2 : a.j ≤ 24
  · apply r6_2 <;> omega
  by_cases hJ3 : a.j ≤ 27
  · apply r6_3 <;> omega
  by_cases hJ4 : a.j ≤ 30
  · apply r6_4 <;> omega
  by_cases hJ5 : a.j ≤ 33
  · apply r6_5 <;> omega
  by_cases hJ6 : a.j ≤ 36
  · apply r6_6 <;> omega
  by_cases hJ7 : a.j ≤ 39
  · apply r6_7 <;> omega
  by_cases hJ8 : a.j ≤ 40
  · apply r6_8 <;> omega
  by_cases hJ9 : a.j ≤ 41
  · apply r6_9 <;> omega
  by_cases hJ10 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 118
    · apply r6_10 <;> omega
    apply r6_11 <;> omega
  by_cases hJ11 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 116
    · apply r6_12 <;> omega
    apply r6_13 <;> omega
  by_cases hJ12 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 113
    · apply r6_14 <;> omega
    apply r6_15 <;> omega
  by_cases hJ13 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 111
    · apply r6_16 <;> omega
    apply r6_17 <;> omega
  by_cases hB0 : a.b ≤ 108
  · apply r6_18 <;> omega
  apply r6_19 <;> omega

private theorem r7_0 {a : Shape} (h₁ : 7 ≤ a.b) (h₂ : 21 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 21) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_1 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 22 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 24) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_2 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 27) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_3 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 30) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_4 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 33) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_5 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 36) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_6 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 39) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_7 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_8 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 41) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_9 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 117) (h₄ : a.j ≤ 42) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_10 {a : Shape} (h₁ : 118 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 42) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_11 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 43) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_12 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 43) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_13 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 112) (h₄ : a.j ≤ 44) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_14 {a : Shape} (h₁ : 113 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 44) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_15 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 109) (h₄ : a.j ≤ 45) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_16 {a : Shape} (h₁ : 110 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_17 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 107) (h₄ : a.j ≤ 46) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r7_18 {a : Shape} (h₁ : 108 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 7) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact7 (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 8 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 21
  · apply r7_0 <;> omega
  by_cases hJ1 : a.j ≤ 24
  · apply r7_1 <;> omega
  by_cases hJ2 : a.j ≤ 27
  · apply r7_2 <;> omega
  by_cases hJ3 : a.j ≤ 30
  · apply r7_3 <;> omega
  by_cases hJ4 : a.j ≤ 33
  · apply r7_4 <;> omega
  by_cases hJ5 : a.j ≤ 36
  · apply r7_5 <;> omega
  by_cases hJ6 : a.j ≤ 39
  · apply r7_6 <;> omega
  by_cases hJ7 : a.j ≤ 40
  · apply r7_7 <;> omega
  by_cases hJ8 : a.j ≤ 41
  · apply r7_8 <;> omega
  by_cases hJ9 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 117
    · apply r7_9 <;> omega
    apply r7_10 <;> omega
  by_cases hJ10 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 114
    · apply r7_11 <;> omega
    apply r7_12 <;> omega
  by_cases hJ11 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 112
    · apply r7_13 <;> omega
    apply r7_14 <;> omega
  by_cases hJ12 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 109
    · apply r7_15 <;> omega
    apply r7_16 <;> omega
  by_cases hB0 : a.b ≤ 107
  · apply r7_17 <;> omega
  apply r7_18 <;> omega

private theorem r8_0 {a : Shape} (h₁ : 8 ≤ a.b) (h₂ : 24 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 24) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_1 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 25 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 27) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_2 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 30) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_3 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 33) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_4 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 36) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_5 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 38) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_6 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 39) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_7 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_8 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 41) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_9 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 42) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_10 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 42) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_11 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 114) (h₄ : a.j ≤ 43) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_12 {a : Shape} (h₁ : 115 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 43) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_13 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 111) (h₄ : a.j ≤ 44) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_14 {a : Shape} (h₁ : 112 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 44) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_15 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 108) (h₄ : a.j ≤ 45) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_16 {a : Shape} (h₁ : 109 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_17 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 106) (h₄ : a.j ≤ 46) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r8_18 {a : Shape} (h₁ : 107 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 8) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact8 (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 9 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 24
  · apply r8_0 <;> omega
  by_cases hJ1 : a.j ≤ 27
  · apply r8_1 <;> omega
  by_cases hJ2 : a.j ≤ 30
  · apply r8_2 <;> omega
  by_cases hJ3 : a.j ≤ 33
  · apply r8_3 <;> omega
  by_cases hJ4 : a.j ≤ 36
  · apply r8_4 <;> omega
  by_cases hJ5 : a.j ≤ 38
  · apply r8_5 <;> omega
  by_cases hJ6 : a.j ≤ 39
  · apply r8_6 <;> omega
  by_cases hJ7 : a.j ≤ 40
  · apply r8_7 <;> omega
  by_cases hJ8 : a.j ≤ 41
  · apply r8_8 <;> omega
  by_cases hJ9 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 116
    · apply r8_9 <;> omega
    apply r8_10 <;> omega
  by_cases hJ10 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 114
    · apply r8_11 <;> omega
    apply r8_12 <;> omega
  by_cases hJ11 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 111
    · apply r8_13 <;> omega
    apply r8_14 <;> omega
  by_cases hJ12 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 108
    · apply r8_15 <;> omega
    apply r8_16 <;> omega
  by_cases hB0 : a.b ≤ 106
  · apply r8_17 <;> omega
  apply r8_18 <;> omega

private theorem r9_0 {a : Shape} (h₁ : 9 ≤ a.b) (h₂ : 27 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 27) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_1 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 28 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 30) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 46) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_2 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 33) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_3 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 36) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_4 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 38) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_5 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 39) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_6 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_7 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 41) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_8 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 41) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_9 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 42) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_10 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 42) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_11 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 43) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_12 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 43) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_13 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 110) (h₄ : a.j ≤ 44) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_14 {a : Shape} (h₁ : 111 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 44) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_15 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 108) (h₄ : a.j ≤ 45) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_16 {a : Shape} (h₁ : 109 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_17 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 105) (h₄ : a.j ≤ 46) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r9_18 {a : Shape} (h₁ : 106 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 9) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact9 (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 10 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 27
  · apply r9_0 <;> omega
  by_cases hJ1 : a.j ≤ 30
  · apply r9_1 <;> omega
  by_cases hJ2 : a.j ≤ 33
  · apply r9_2 <;> omega
  by_cases hJ3 : a.j ≤ 36
  · apply r9_3 <;> omega
  by_cases hJ4 : a.j ≤ 38
  · apply r9_4 <;> omega
  by_cases hJ5 : a.j ≤ 39
  · apply r9_5 <;> omega
  by_cases hJ6 : a.j ≤ 40
  · apply r9_6 <;> omega
  by_cases hJ7 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 119
    · apply r9_7 <;> omega
    apply r9_8 <;> omega
  by_cases hJ8 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 116
    · apply r9_9 <;> omega
    apply r9_10 <;> omega
  by_cases hJ9 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 113
    · apply r9_11 <;> omega
    apply r9_12 <;> omega
  by_cases hJ10 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 110
    · apply r9_13 <;> omega
    apply r9_14 <;> omega
  by_cases hJ11 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 108
    · apply r9_15 <;> omega
    apply r9_16 <;> omega
  by_cases hB0 : a.b ≤ 105
  · apply r9_17 <;> omega
  apply r9_18 <;> omega

private theorem r10_0 {a : Shape} (h₁ : 10 ≤ a.b) (h₂ : 30 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 30) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_1 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 31 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 33) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_2 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 36) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_3 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 38) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_4 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 39) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_5 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_6 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 41) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_7 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 41) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_8 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 42) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_9 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 42) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_10 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 43) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_11 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 43) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_12 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 110) (h₄ : a.j ≤ 44) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_13 {a : Shape} (h₁ : 111 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 44) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_14 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 107) (h₄ : a.j ≤ 45) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_15 {a : Shape} (h₁ : 108 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_16 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 105) (h₄ : a.j ≤ 46) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r10_17 {a : Shape} (h₁ : 106 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 10) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact10 (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 11 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 30
  · apply r10_0 <;> omega
  by_cases hJ1 : a.j ≤ 33
  · apply r10_1 <;> omega
  by_cases hJ2 : a.j ≤ 36
  · apply r10_2 <;> omega
  by_cases hJ3 : a.j ≤ 38
  · apply r10_3 <;> omega
  by_cases hJ4 : a.j ≤ 39
  · apply r10_4 <;> omega
  by_cases hJ5 : a.j ≤ 40
  · apply r10_5 <;> omega
  by_cases hJ6 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 119
    · apply r10_6 <;> omega
    apply r10_7 <;> omega
  by_cases hJ7 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 116
    · apply r10_8 <;> omega
    apply r10_9 <;> omega
  by_cases hJ8 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 113
    · apply r10_10 <;> omega
    apply r10_11 <;> omega
  by_cases hJ9 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 110
    · apply r10_12 <;> omega
    apply r10_13 <;> omega
  by_cases hJ10 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 107
    · apply r10_14 <;> omega
    apply r10_15 <;> omega
  by_cases hB0 : a.b ≤ 105
  · apply r10_16 <;> omega
  apply r10_17 <;> omega

private theorem r11_0 {a : Shape} (h₁ : 11 ≤ a.b) (h₂ : 33 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 33) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_1 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 34 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 36) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_2 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 38) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_3 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 39 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 39) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_4 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_5 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 119) (h₄ : a.j ≤ 41) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_6 {a : Shape} (h₁ : 120 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 41) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_7 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 42) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_8 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 42) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_9 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 43) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_10 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 43) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_11 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 110) (h₄ : a.j ≤ 44) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_12 {a : Shape} (h₁ : 111 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 44) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_13 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 107) (h₄ : a.j ≤ 45) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_14 {a : Shape} (h₁ : 108 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_15 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 105) (h₄ : a.j ≤ 46) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r11_16 {a : Shape} (h₁ : 106 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 11) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact11 (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 12 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 33
  · apply r11_0 <;> omega
  by_cases hJ1 : a.j ≤ 36
  · apply r11_1 <;> omega
  by_cases hJ2 : a.j ≤ 38
  · apply r11_2 <;> omega
  by_cases hJ3 : a.j ≤ 39
  · apply r11_3 <;> omega
  by_cases hJ4 : a.j ≤ 40
  · apply r11_4 <;> omega
  by_cases hJ5 : a.j ≤ 41
  · by_cases hB0 : a.b ≤ 119
    · apply r11_5 <;> omega
    apply r11_6 <;> omega
  by_cases hJ6 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 116
    · apply r11_7 <;> omega
    apply r11_8 <;> omega
  by_cases hJ7 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 113
    · apply r11_9 <;> omega
    apply r11_10 <;> omega
  by_cases hJ8 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 110
    · apply r11_11 <;> omega
    apply r11_12 <;> omega
  by_cases hJ9 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 107
    · apply r11_13 <;> omega
    apply r11_14 <;> omega
  by_cases hB0 : a.b ≤ 105
  · apply r11_15 <;> omega
  apply r11_16 <;> omega

private theorem r12_0 {a : Shape} (h₁ : 12 ≤ a.b) (h₂ : 36 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 36) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_1 {a : Shape} (h₁ : 13 ≤ a.b) (h₂ : 37 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 39) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_2 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 40 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 40) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_3 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 41 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 41) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_4 {a : Shape} (h₁ : 14 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 116) (h₄ : a.j ≤ 42) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_5 {a : Shape} (h₁ : 117 ≤ a.b) (h₂ : 42 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 42) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_6 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 113) (h₄ : a.j ≤ 43) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_7 {a : Shape} (h₁ : 114 ≤ a.b) (h₂ : 43 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 43) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_8 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 110) (h₄ : a.j ≤ 44) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_9 {a : Shape} (h₁ : 111 ≤ a.b) (h₂ : 44 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 44) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_10 {a : Shape} (h₁ : 15 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 107) (h₄ : a.j ≤ 45) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_11 {a : Shape} (h₁ : 108 ≤ a.b) (h₂ : 45 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 45) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_12 {a : Shape} (h₁ : 16 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 105) (h₄ : a.j ≤ 46) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 48) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem r12_13 {a : Shape} (h₁ : 106 ≤ a.b) (h₂ : 46 ≤ a.j)
    (h₃ : a.b ≤ 120) (h₄ : a.j ≤ 46) (ht : a.t = 12) (ha : 3*a.t ≤ a.j) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j :=
  oldRectangle (l := 60) h₁ h₂ h₃ h₄ ht ha (by decide) (by decide +kernel) (by decide +kernel)

private theorem exact12 (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 120) (hj : a.j ≤ 46) :
    physicalPrice a (order .one a) ≤ allowance 13 .one a.j := by
  obtain ⟨hpos,hindex,hdegree⟩ := ha
  by_cases hJ0 : a.j ≤ 36
  · apply r12_0 <;> omega
  by_cases hJ1 : a.j ≤ 39
  · apply r12_1 <;> omega
  by_cases hJ2 : a.j ≤ 40
  · apply r12_2 <;> omega
  by_cases hJ3 : a.j ≤ 41
  · apply r12_3 <;> omega
  by_cases hJ4 : a.j ≤ 42
  · by_cases hB0 : a.b ≤ 116
    · apply r12_4 <;> omega
    apply r12_5 <;> omega
  by_cases hJ5 : a.j ≤ 43
  · by_cases hB0 : a.b ≤ 113
    · apply r12_6 <;> omega
    apply r12_7 <;> omega
  by_cases hJ6 : a.j ≤ 44
  · by_cases hB0 : a.b ≤ 110
    · apply r12_8 <;> omega
    apply r12_9 <;> omega
  by_cases hJ7 : a.j ≤ 45
  · by_cases hB0 : a.b ≤ 107
    · apply r12_10 <;> omega
    apply r12_11 <;> omega
  by_cases hB0 : a.b ≤ 105
  · apply r12_12 <;> omega
  apply r12_13 <;> omega

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
